//! A witness check for Lean 4 proofs, using [nanoda](../vendor/nanoda/VENDORED.md) as the
//! kernel, over content-addressed declarations (see `tools/lean/node_format.md`).
//!
//! Every blob is a *node*: one declaration, naming the nodes it uses by hash. A theorem's node is
//! its statement; its proof is a separate blob. Nodes are loaded after the nodes they import, and
//! only pinned nodes may declare the names the kernel treats specially (see
//! `nanoda_lib::nodes`).
//!
//! - **Attest mode:** the subjects are a batch of nodes, the trusted blobs are attested nodes
//!   holding everything the batch imports (recursively), and the witness is the batch's proofs.
//!   Params are the pins: the hashes of the nodes allowed to declare `Nat`, `Nat.add`, the
//!   permitted axioms and the like, 32 bytes each. Every subject is type-checked, each theorem
//!   with its proof. A library is attested this way in batches, each once.
//! - **Reveal mode:** params are the hash of the bounty's theorem statement node (say `theorem
//!   goal : Goal`, which the poster can hash without a proof), then the pins. The witness is the
//!   solver's nodes and proofs. Every untrusted node is type-checked, each theorem with its proof,
//!   and the statement node must be among them, proven (or trusted: attested, so proven before).
//!
//! The bounty must cite at least one node attested with params equal to its pins (its `Goal`,
//! say). witness then makes every attestation a reveal relies on share those params, so every
//! trusted node was checked under the same pins. Otherwise a node checked against a fake `Nat.add`
//! could be trusted where the real one is pinned.
//!
//! Only `propext`, `Classical.choice` and `Quot.sound` may be declared as axioms. Type errors
//! panic, which counts as false.

#![cfg_attr(not(test), no_std)]

extern crate alloc;

use alloc::{collections::BTreeMap, vec::Vec};
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

/// Pins: 32-byte hashes, back to back.
fn pins(params: &[u8]) -> Option<Vec<Hash>> {
	let (pins, rest) = params.as_chunks::<32>();
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

/// Load `entries`, each after what it and its proof import, then type-check every untrusted one. Returns the
/// loaded nodes, or `None` if they don't load or an untrusted theorem has no proof. Type errors
/// panic.
fn load_and_check<'a>(pins: &[Hash], entries: &BTreeMap<Hash, Entry<'a>>) -> Option<nanoda_lib::nodes::Nodes<'a>> {
	let mut loader = NodeLoader::new(pins);
	// Depth-first, imports before the node, iteratively: the import DAG can be deep.
	for root in entries.keys() {
		let mut stack = alloc::vec![(*root, false)];
		while let Some((hash, imports_done)) = stack.pop() {
			if loader.is_loaded(&hash) {
				continue;
			}
			let entry = entries.get(&hash)?;
			if imports_done {
				loader.add(hash, entry.node, entry.proof).ok()?;
			} else {
				stack.push((hash, true));
				let mut deps = imports(entry.node)?;
				if let Some(proof) = entry.proof {
					deps.extend(proof_imports(proof)?);
				}
				for import in deps {
					if !loader.is_loaded(&import) {
						// An import cycle can't happen (a node's hash covers its imports'), but
						// a node revisited here would mean one: refuse rather than loop.
						if stack.iter().any(|(h, done)| *h == import && *done) {
							return None;
						}
						stack.push((import, false));
					}
				}
			}
		}
	}
	let nodes = loader.finish();
	for (i, node) in nodes.nodes.iter().enumerate() {
		let entry = &entries[&node.hash];
		if !entry.trusted {
			if node.assumed {
				return None;
			}
			nodes.check(i);
		}
	}
	Some(nodes)
}

/// Add `node` to `entries`, refusing a duplicate.
fn insert<'a>(entries: &mut BTreeMap<Hash, Entry<'a>>, hash: Hash, node: &'a [u8], trusted: bool) -> Option<()> {
	entries.insert(hash, Entry { node, trusted, proof: None }).is_none().then_some(())
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

fn attest(input: &Input) -> Option<()> {
	let pins = pins(input.params)?;
	let mut entries = BTreeMap::new();
	let mut subjects = 0;
	for blob in input.blobs() {
		insert(&mut entries, *blob.hash, blob.data, blob.trusted)?;
		subjects += usize::from(!blob.trusted);
	}
	if subjects == 0 {
		return None;
	}
	attach(&mut entries, &parse_witness(input.witness)?)?;
	load_and_check(&pins, &entries).map(|_| ())
}

fn reveal(input: &Input) -> Option<()> {
	let (goal, pinned) = input.params.split_first_chunk::<32>()?;
	let pins = pins(pinned)?;
	let mut entries = BTreeMap::new();
	for blob in input.blobs() {
		insert(&mut entries, *blob.hash, blob.data, blob.trusted)?;
	}
	let (nodes, proofs): (Vec<&[u8]>, Vec<&[u8]>) =
		parse_witness(input.witness)?.into_iter().partition(|item| item.starts_with(NODE_MAGIC));
	for node in nodes {
		insert(&mut entries, blake2b256(node), node, false)?;
	}
	attach(&mut entries, &proofs)?;
	let loaded = load_and_check(&pins, &entries)?;
	// Untrusted theorems were proven above, and trusted ones were when they were attested.
	loaded.nodes[loaded.find(goal)?].theorem.then_some(())
}

/// The check, for running natively too (see `tools/lean-host`).
pub fn check(input: &Input) -> bool {
	match input.mode {
		Mode::Attest => attest(input),
		Mode::Reveal => reveal(input),
	}
	.is_some()
}

witness_check::declare_full_check!(check);

#[cfg(test)]
mod tests;
