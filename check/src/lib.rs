//! A witness check for Lean 4 proofs, using [nanoda](../vendor/nanoda/VENDORED.md) as the
//! kernel, over content-addressed declarations (see `tools/lean/node_format.md`).
//!
//! Every blob is a *node*: one declaration, naming the nodes it uses by hash. A theorem's node is
//! its statement; its proof is a separate blob. Nodes are loaded after the nodes they import, and
//! only pinned nodes may declare the names the kernel treats specially (see
//! `nanoda_lib::nodes`).
//!
//! The pins are built in: the hashes of the nodes allowed to declare `Nat`, `Nat.add`, the
//! permitted axioms and the like, for the Lean toolchain the check is for (`pins.txt`, made by
//! `tools/lean/lean_pins.py`; nodes are canonical, so they hash the same in any export on that
//! toolchain). So the check's hash fixes them: every attestation by one check was checked under
//! the same pins, and no node checked against a fake `Nat.add` can be trusted. A new toolchain
//! needs new pins, and so a new check.
//!
//! - **Attest mode:** the subjects are a batch of nodes, the trusted blobs are attested nodes
//!   holding everything the batch imports (recursively), and the witness is the batch's proofs.
//!   A batch whose proofs would make the op too big may carry them among its subjects instead.
//!   Params are empty. Every subject is type-checked, each theorem with its proof. A library is
//!   attested this way in batches, each once.
//! - **Reveal mode:** params are the hash of the bounty's theorem statement node (say `theorem
//!   goal : Goal`, which the poster can hash without a proof). The witness is the solver's nodes
//!   and proofs. Every untrusted node is type-checked, each theorem with its proof, and the
//!   statement node must be among them, proven (or trusted: attested, so proven before).
//!
//! witness lets a reveal trust attested subjects only if its bounty cites one (or the hunter
//! would pick the attestations' params), so a bounty cites an attested node, its `Goal` say.
//!
//! **Judgments** (`nanoda_lib::judgment`) let a declaration too heavy for one check be checked in
//! pieces. A judgment is a blob of kernel cache entries made while checking one declaration's
//! node, importing the nodes that declare what it mentions:
//!
//! - **Attesting judgments:** the subjects are judgments, all for one declaration; the witness
//!   is that declaration's node and a calls blob. The check runs the calls in a checker for the
//!   declaration, seeded with the judgments it cites, and accepts if every subject's entries are
//!   then in the checker's caches. The node is loaded only to set the checker up, not checked.
//! - **Using them:** an attest or reveal op may cite judgments. Each untrusted node is checked
//!   with the cited judgments for it seeded into its checker; a cited judgment for anything else,
//!   or mentioning a constant not declared by one of its imports, fails the op.
//!
//! By induction, every cited entry is a judgment the kernel made, about terms that mean the same
//! here: witness only passes attested subjects as trusted, and only ones attested by this check.
//!
//! **Splitting an inductive block.** A node holding an inductive block (its types, constructors
//! and recursors) can be too big to check in one op even when each declaration isn't. An op whose
//! subjects are *declarations blobs* (see [`DECLARATIONS_MAGIC`]) for one such node, given as the
//! witness, checks just those declarations, the node loaded as an untrusted one is (its imports
//! loaded, declaring what it mentions). An op attesting the node, or a reveal, may then cite them:
//! the node's declarations they cover aren't checked again. An inductive type's own check splits
//! further, into its constructors and its recursors; it's covered when both are. A theorem's node
//! can't be split. Splitting is never needed, only allowed: a node checked whole costs least.
//!
//! Only `propext`, `Classical.choice` and `Quot.sound` may be declared as axioms. Type errors
//! panic, which counts as false.

#![cfg_attr(not(test), no_std)]

extern crate alloc;

use alloc::{collections::BTreeMap, vec::Vec};
use nanoda_lib::env::Phase;
use nanoda_lib::judgment::{self, CALLS_MAGIC, JUDGMENT_MAGIC};
use nanoda_lib::nodes::{Hash, NODE_MAGIC, NodeLoader, PROOF_MAGIC};
use witness_check::{Input, Mode};

// nanoda recurses deeply while type checking. A 1 MiB stack sufficed for every proof the spike
// measured; natively it asks for 16 MiB for deep ones.
#[cfg(any(target_arch = "riscv32", target_arch = "riscv64"))]
polkavm_derive::min_stack_size!(8 * 1024 * 1024);

fn blake2b256(data: &[u8]) -> Hash {
	let h = blake2b_simd::Params::new().hash_length(32).hash(data);
	let mut out = [0; 32];
	out.copy_from_slice(h.as_bytes());
	out
}

fn uvar(bytes: &mut &[u8]) -> Option<usize> {
	let mut value = 0usize;
	for shift in (0..64).step_by(7) {
		let (&b, rest) = bytes.split_first()?;
		*bytes = rest;
		value |= usize::from(b & 0x7f).checked_shl(shift)?;
		if b & 0x80 == 0 {
			return Some(value);
		}
	}
	None
}

/// A witness: a count, then each item's length and bytes, all as unsigned LEB128.
pub fn parse_witness(mut bytes: &[u8]) -> Option<Vec<&[u8]>> {
	let n = uvar(&mut bytes)?;
	let mut items = Vec::new();
	for _ in 0..n {
		let len = uvar(&mut bytes)?;
		let (item, rest) = bytes.split_at_checked(len)?;
		items.push(item);
		bytes = rest;
	}
	bytes.is_empty().then_some(items)
}

/// The pins the check is built with: 32-byte hashes, back to back (see the module docs).
const PINS: &[u8] = include_bytes!("../pins.bin");

/// Pins: 32-byte hashes, back to back.
fn pins(bytes: &[u8]) -> Option<Vec<Hash>> {
	let (pins, rest) = bytes.as_chunks::<32>();
	rest.is_empty().then(|| pins.to_vec())
}

/// A node to load.
struct Entry<'a> {
	node: &'a [u8],
	trusted: bool,
	proof: Option<&'a [u8]>,
}

/// The hashes a node imports.
fn imports(node: &[u8]) -> Option<Vec<Hash>> {
	import_list(node.strip_prefix(NODE_MAGIC)?)
}

/// The hashes a proof imports.
fn proof_imports(proof: &[u8]) -> Option<Vec<Hash>> {
	import_list(proof.strip_prefix(PROOF_MAGIC)?.get(32..)?)
}

fn import_list(mut bytes: &[u8]) -> Option<Vec<Hash>> {
	let n = uvar(&mut bytes)?;
	(0..n)
		.map(|_| {
			let (h, rest) = bytes.split_first_chunk::<32>()?;
			bytes = rest;
			Some(*h)
		})
		.collect()
}

/// Load `entries`, then type-check every untrusted one. Returns the loaded nodes, or `None` if
/// they don't load or an untrusted theorem has no proof. Type errors panic.
///
/// Trusted nodes load first, so every untrusted one is checked against all of them (nanoda checks
/// a declaration against those loaded before it). Each node loads after the ones it (and its
/// proof) imports; a trusted node's imports needn't be there (see `nanoda_lib::nodes`), an
/// untrusted one's must.
///
/// Each untrusted node is checked seeded with the judgments in `cited` made for it (attested:
/// witness passes only attested subjects as trusted); a cited judgment for anything else is
/// refused. An untrusted inductive block's declarations that the declarations blobs `parts`
/// (attested) cover were checked already, and aren't again; a cited blob for any other node is
/// refused.
fn load_and_check<'a>(
	pins: &[Hash],
	entries: &BTreeMap<Hash, Entry<'a>>,
	cited: &[&[u8]],
	parts: &[&[u8]],
) -> Option<nanoda_lib::nodes::Nodes<'a>> {
	let parts: Vec<(Hash, Vec<(usize, Phase)>)> = parts.iter().map(|b| declarations_of(b)).collect::<Option<_>>()?;
	let nodes = load(pins, entries)?;
	let (mut seeded, mut used) = (0, 0);
	for (i, node) in nodes.nodes.iter().enumerate() {
		let entry = &entries[&node.hash];
		if !entry.trusted {
			if node.assumed {
				return None;
			}
			let mine = judgments_for(cited, &node.hash)?;
			seeded += mine.len();
			let theirs: Vec<&(Hash, Vec<(usize, Phase)>)> = parts.iter().filter(|(h, _)| *h == node.hash).collect();
			used += theirs.len();
			let done: Vec<(usize, Phase)> = theirs.iter().flat_map(|(_, p)| p.iter().copied()).collect();
			if done.is_empty() {
				nodes.check_with(i, &mine).ok()?;
				continue;
			}
			// An inductive block, in parts: judgments are for single declarations with values.
			if !mine.is_empty() || !valid_parts(&nodes, i, &done) {
				return None;
			}
			// What's left of each declaration: all of it, the phase not cited, or nothing.
			nodes.check_parts(i, |k| {
				let has = |p: Phase| done.contains(&(k, p));
				if has(Phase::Whole) || (has(Phase::Constructors) && has(Phase::Recursors)) {
					alloc::vec![]
				} else if has(Phase::Constructors) {
					alloc::vec![Phase::Recursors]
				} else if has(Phase::Recursors) {
					alloc::vec![Phase::Constructors]
				} else {
					alloc::vec![Phase::Whole]
				}
			});
		}
	}
	(seeded == cited.len() && used == parts.len()).then_some(nodes)
}

/// Whether `parts` name parts of node `i`, an inductive block: positions within it, and phases
/// only of its inductive types.
fn valid_parts(nodes: &nanoda_lib::nodes::Nodes, i: usize, parts: &[(usize, Phase)]) -> bool {
	nodes.is_inductive_block(i)
		&& parts.iter().all(|&(k, p)| k < nodes.declaration_count(i) && (p == Phase::Whole || nodes.is_inductive_type(i, k)))
}

/// A declarations blob: [`DECLARATIONS_MAGIC`], an inductive block's node hash, then a count
/// (unsigned LEB128) and that many parts its op checked: a declaration's position within the node
/// (unsigned LEB128) and a phase byte: 0 the whole declaration, 1 an inductive type's
/// constructors, 2 its recursors (see `nanoda_lib::env::Phase`).
pub const DECLARATIONS_MAGIC: &[u8] = b"LEANDCL\x01";

fn declarations_of(blob: &[u8]) -> Option<(Hash, Vec<(usize, Phase)>)> {
	let mut rest = blob.strip_prefix(DECLARATIONS_MAGIC)?;
	let (node, r) = rest.split_first_chunk::<32>()?;
	rest = r;
	let n = uvar(&mut rest)?;
	let parts = (0..n)
		.map(|_| {
			let k = uvar(&mut rest)?;
			let (&p, r) = rest.split_first()?;
			rest = r;
			let phase = match p {
				0 => Phase::Whole,
				1 => Phase::Constructors,
				2 => Phase::Recursors,
				_ => return None,
			};
			Some((k, phase))
		})
		.collect::<Option<Vec<_>>>()?;
	rest.is_empty().then_some((*node, parts))
}

/// The judgments of `cited` made for node `node`.
fn judgments_for<'a>(cited: &[&'a [u8]], node: &Hash) -> Option<Vec<&'a [u8]>> {
	let mut out = Vec::new();
	for &j in cited {
		if judgment::header(j).ok()?.declaration == *node {
			out.push(j);
		}
	}
	Some(out)
}

/// Load `entries`, trusted ones first, each after its imports.
fn load<'a>(pins: &[Hash], entries: &BTreeMap<Hash, Entry<'a>>) -> Option<nanoda_lib::nodes::Nodes<'a>> {
	let mut loader = NodeLoader::new(pins);
	for trusted_phase in [true, false] {
		for (root, _) in entries.iter().filter(|(_, e)| e.trusted == trusted_phase) {
			// Depth-first, imports before the node, iteratively: the import DAG can be deep.
			let mut stack = alloc::vec![(*root, false)];
			while let Some((hash, imports_done)) = stack.pop() {
				if loader.is_loaded(&hash) {
					continue;
				}
				let entry = entries.get(&hash)?;
				if imports_done {
					loader.add(hash, entry.node, entry.proof, entry.trusted).ok()?;
					continue;
				}
				stack.push((hash, true));
				let mut deps = imports(entry.node)?;
				if let Some(proof) = entry.proof {
					deps.extend(proof_imports(proof)?);
				}
				for import in deps {
					if loader.is_loaded(&import) || (entry.trusted && !entries.contains_key(&import)) {
						continue;
					}
					// An import cycle can't happen (a node's hash covers its imports'), but a node
					// revisited here would mean one: refuse rather than loop.
					if stack.iter().any(|(h, done)| *h == import && *done) {
						return None;
					}
					stack.push((import, false));
				}
			}
		}
	}
	loader.finish().ok()
}

/// Add `node` to `entries`. The same trusted node may come twice (an op may cite a subject
/// twice, say a bounty's and again among the solver's); anything else twice is refused.
fn insert<'a>(entries: &mut BTreeMap<Hash, Entry<'a>>, hash: Hash, node: &'a [u8], trusted: bool) -> Option<()> {
	match entries.insert(hash, Entry { node, trusted, proof: None }) {
		None => Some(()),
		Some(old) => (old.trusted && trusted).then_some(()),
	}
}

/// Attach each of `proofs` to the untrusted node it proves.
fn attach<'a>(entries: &mut BTreeMap<Hash, Entry<'a>>, proofs: &[&'a [u8]]) -> Option<()> {
	for proof in proofs {
		let of: Hash = *proof.strip_prefix(PROOF_MAGIC)?.first_chunk::<32>()?;
		let entry = entries.get_mut(&of).filter(|e| !e.trusted)?;
		if entry.proof.replace(proof).is_some() {
			return None;
		}
	}
	Some(())
}

fn attest(input: &Input, pins: &[Hash]) -> Option<()> {
	if !input.params.is_empty() {
		return None;
	}
	let mut entries = BTreeMap::new();
	let (mut cited, mut judgments) = (Vec::new(), Vec::new());
	let (mut parts, mut declarations) = (Vec::new(), Vec::new());
	let mut subjects = 0;
	let mut witness = parse_witness(input.witness)?;
	for blob in input.blobs() {
		if blob.data.starts_with(JUDGMENT_MAGIC) {
			if blob.trusted { cited.push(blob.data) } else { judgments.push(blob.data) }
			continue;
		}
		if blob.data.starts_with(DECLARATIONS_MAGIC) {
			if blob.trusted { parts.push(blob.data) } else { declarations.push(blob.data) }
			continue;
		}
		// A batch too big for an op carries its proofs among its subjects instead.
		if !blob.trusted && blob.data.starts_with(PROOF_MAGIC) {
			witness.push(blob.data);
			continue;
		}
		insert(&mut entries, *blob.hash, blob.data, blob.trusted)?;
		subjects += usize::from(!blob.trusted);
	}
	if !judgments.is_empty() {
		// A judgment op attests judgments only.
		if subjects != 0 || !declarations.is_empty() || !parts.is_empty() {
			return None;
		}
		return attest_judgments(pins, entries, &cited, &judgments, &witness);
	}
	if !declarations.is_empty() {
		// An op checking some declarations of one inductive block, and nothing else.
		if subjects != 0 || !cited.is_empty() || !parts.is_empty() {
			return None;
		}
		return attest_declarations(pins, entries, &declarations, &witness);
	}
	if subjects == 0 {
		return None;
	}
	attach(&mut entries, &witness)?;
	load_and_check(pins, &entries, &cited, &parts).map(|_| ())
}

/// Attest `declarations` (blobs), each naming parts of one inductive block, whose node is the
/// witness: load it as an untrusted node (so its imports are loaded, and declare what it
/// mentions), and check just those parts, as checking the whole node would.
fn attest_declarations<'a>(pins: &[Hash], mut entries: BTreeMap<Hash, Entry<'a>>, declarations: &[&[u8]], witness: &[&'a [u8]]) -> Option<()> {
	let &[node] = witness else { return None };
	if !node.starts_with(NODE_MAGIC) {
		return None;
	}
	let hash = blake2b256(node);
	let mut parts = Vec::new();
	for blob in declarations {
		let (of, p) = declarations_of(blob)?;
		if of != hash {
			return None;
		}
		parts.extend(p);
	}
	insert(&mut entries, hash, node, false)?;
	let nodes = load(pins, &entries)?;
	let i = nodes.find(&hash)?;
	if !valid_parts(&nodes, i, &parts) {
		return None;
	}
	nodes.check_parts(i, |k| {
		let mut phases: Vec<Phase> = parts.iter().filter(|(j, _)| *j == k).map(|&(_, p)| p).collect();
		phases.dedup();
		phases
	});
	Some(())
}

/// Attest `judgments`, all for one declaration, whose node is in the witness with the calls that
/// make them: run the calls in a checker for it, seeded with the judgments `cited`, then every
/// entry of every judgment must be in its caches.
fn attest_judgments<'a>(
	pins: &[Hash],
	mut entries: BTreeMap<Hash, Entry<'a>>,
	cited: &[&[u8]],
	judgments: &[&[u8]],
	witness: &[&'a [u8]],
) -> Option<()> {
	let &[a, b] = witness else { return None };
	let (node, calls) = if a.starts_with(NODE_MAGIC) { (a, b) } else { (b, a) };
	if !node.starts_with(NODE_MAGIC) || !calls.starts_with(CALLS_MAGIC) {
		return None;
	}
	let declaration = blake2b256(node);
	// Loaded as an untrusted node, and not checked: it fixes the checker's environment and
	// universe parameters, and nothing here relies on it being true; its judgments are only ever
	// seeded into a check of this same node. Untrusted, it loads after every trusted node, as it
	// does where it's checked, so the checker sees what's declared before it there; and its
	// imports must be loaded, as there.
	insert(&mut entries, declaration, node, false)?;
	let nodes = load(pins, &entries)?;
	nodes.attest_judgments(nodes.find(&declaration)?, cited, calls, judgments).ok()
}

fn reveal(input: &Input, pins: &[Hash]) -> Option<()> {
	let goal: &Hash = input.params.try_into().ok()?;
	let mut entries = BTreeMap::new();
	let (mut cited, mut parts) = (Vec::new(), Vec::new());
	for blob in input.blobs() {
		if blob.trusted && blob.data.starts_with(JUDGMENT_MAGIC) {
			cited.push(blob.data);
			continue;
		}
		if blob.trusted && blob.data.starts_with(DECLARATIONS_MAGIC) {
			parts.push(blob.data);
			continue;
		}
		insert(&mut entries, *blob.hash, blob.data, blob.trusted)?;
	}
	let (nodes, proofs): (Vec<&[u8]>, Vec<&[u8]>) =
		parse_witness(input.witness)?.into_iter().partition(|item| item.starts_with(NODE_MAGIC));
	for node in nodes {
		insert(&mut entries, blake2b256(node), node, false)?;
	}
	attach(&mut entries, &proofs)?;
	let loaded = load_and_check(pins, &entries, &cited, &parts)?;
	// Untrusted theorems were proven above, and trusted ones were when they were attested.
	loaded.nodes[loaded.find(goal)?].theorem.then_some(())
}

/// An attest op's nodes (trusted and subjects, with their proofs) loaded, not checked: for
/// planning judgments (see `tools/lean-host`).
pub fn load_attest<'a>(input: &Input<'a>) -> Option<nanoda_lib::nodes::Nodes<'a>> {
	let pins = pins(PINS)?;
	let mut entries = BTreeMap::new();
	let mut witness = parse_witness(input.witness)?;
	for blob in input.blobs() {
		if !blob.trusted && blob.data.starts_with(PROOF_MAGIC) {
			witness.push(blob.data);
			continue;
		}
		if blob.data.starts_with(JUDGMENT_MAGIC) || blob.data.starts_with(DECLARATIONS_MAGIC) {
			continue;
		}
		insert(&mut entries, *blob.hash, blob.data, blob.trusted)?;
	}
	attach(&mut entries, &witness)?;
	load(&pins, &entries)
}

/// The check, for running natively too (see `tools/lean-host`).
pub fn check(input: &Input) -> bool {
	pins(PINS).is_some_and(|pins| check_with(input, &pins))
}

/// The check with `pins` in place of its own, for testing with other fixtures.
fn check_with(input: &Input, pins: &[Hash]) -> bool {
	match input.mode {
		Mode::Attest => attest(input, pins),
		Mode::Reveal => reveal(input, pins),
	}
	.is_some()
}

witness_check::declare_full_check!(check);

#[cfg(test)]
mod tests;
