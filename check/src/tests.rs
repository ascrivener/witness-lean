use super::*;
use std::vec;
use witness_types::{CheckBlob, CheckMode, check_args};

/// A fixture: one theorem's closure as nodes, in dependency order (the theorem's statement
/// last), and their proofs.
struct Pack {
	nodes: Vec<&'static [u8]>,
	proofs: Vec<&'static [u8]>,
}

macro_rules! pack {
	($name: literal) => {{
		let items = parse_witness(include_bytes!(concat!("../testdata/", $name, ".pack"))).unwrap();
		let (nodes, proofs) = items.into_iter().partition(|i| i.starts_with(NODE_MAGIC));
		Pack { nodes, proofs }
	}};
}

impl Pack {
	/// The theorem's statement.
	fn goal(&self) -> &'static [u8] {
		self.nodes.last().unwrap()
	}

	/// Everything but the theorem's statement.
	fn env(&self) -> &[&'static [u8]] {
		&self.nodes[..self.nodes.len() - 1]
	}

	fn proof_of(&self, node: &[u8]) -> Option<&'static [u8]> {
		let h = blake2b256(node);
		self.proofs.iter().copied().find(|p| p[PROOF_MAGIC.len()..][..32] == h)
	}

	/// `nodes` with each one's proof, if it has one.
	fn with_proofs(&self, nodes: &[&'static [u8]]) -> Vec<&'static [u8]> {
		let mut items = nodes.to_vec();
		items.extend(nodes.iter().filter_map(|n| self.proof_of(n)));
		items
	}

	/// Pins every node, so whichever declares `Nat` and the like is pinned.
	fn pins(&self) -> Vec<u8> {
		self.nodes.iter().flat_map(|n| blake2b256(n)).collect()
	}
}

fn encode(items: &[&[u8]]) -> Vec<u8> {
	fn uvar(out: &mut Vec<u8>, mut n: usize) {
		loop {
			let b = (n & 0x7f) as u8;
			n >>= 7;
			if n == 0 {
				return out.push(b);
			}
			out.push(b | 0x80);
		}
	}
	let mut out = Vec::new();
	uvar(&mut out, items.len());
	for item in items {
		uvar(&mut out, item.len());
		out.extend_from_slice(item);
	}
	out
}

/// Run the check; blobs get their real hashes, as witness gives them.
fn run(mode: CheckMode, blobs: &[(bool, &[u8])], params: &[u8], witness: &[u8]) -> bool {
	let hashes: Vec<Hash> = blobs.iter().map(|(_, d)| blake2b256(d)).collect();
	let blobs: Vec<_> =
		blobs.iter().zip(&hashes).map(|(&(trusted, data), h)| CheckBlob { trusted, hash: *h, data }).collect();
	let args = check_args(mode, &blobs, params, witness);
	// Type errors panic, which the PVM turns into false.
	std::panic::catch_unwind(|| check(&Input::parse(&args).unwrap())).unwrap_or(false)
}

/// Reveal `solver`'s nodes and proofs for the theorem statement `goal`, trusting `trusted`.
fn reveal(goal: &[u8], pins: &[u8], trusted: &[&[u8]], solver: &[&[u8]]) -> bool {
	let mut params = blake2b256(goal).to_vec();
	params.extend_from_slice(pins);
	let blobs: Vec<(bool, &[u8])> = trusted.iter().map(|n| (true, *n)).collect();
	run(CheckMode::Reveal, &blobs, &params, &encode(solver))
}

/// Attest `subjects` with `proofs`, trusting `trusted`.
fn attest(pins: &[u8], trusted: &[&[u8]], subjects: &[&[u8]], proofs: &[&[u8]]) -> bool {
	let blobs: Vec<(bool, &[u8])> =
		trusted.iter().map(|n| (true, *n)).chain(subjects.iter().map(|n| (false, *n))).collect();
	run(CheckMode::Attest, &blobs, pins, &encode(proofs))
}

#[test]
fn honest_proofs_are_accepted() {
	for p in [pack!("two"), pack!("f")] {
		let solver = p.with_proofs(&[p.goal()]);
		assert!(reveal(p.goal(), &p.pins(), p.env(), &solver), "on a trusted environment");
		let everything = p.with_proofs(&p.nodes);
		assert!(reveal(p.goal(), &p.pins(), &[], &everything), "proving the whole closure");
		// Nodes come in any order: each is loaded after what it imports.
		let mut reversed = everything.clone();
		reversed.reverse();
		assert!(reveal(p.goal(), &p.pins(), &[], &reversed), "in reverse");
		let mut env = p.env().to_vec();
		env.reverse();
		assert!(reveal(p.goal(), &p.pins(), &env, &solver), "a reversed environment");
		env.extend_from_slice(&p.env()[..3]);
		assert!(reveal(p.goal(), &p.pins(), &env, &solver), "trusted nodes cited twice");
	}
}

#[test]
fn an_attested_theorem_needs_no_proof() {
	let p = pack!("two");
	assert!(reveal(p.goal(), &p.pins(), &p.nodes, &[]));
}

#[test]
fn the_goal_must_be_a_theorem() {
	let p = pack!("two");
	// GoalTwo itself, a definition, named as the goal by mistake.
	let def = p.env().iter().find(|n| p.proof_of(n).is_none() && imports(n).unwrap().len() > 1).unwrap();
	assert!(!reveal(def, &p.pins(), &p.nodes, &[]));
	assert!(!reveal(def, &p.pins(), p.env(), &p.with_proofs(&[p.goal()])));
}

#[test]
fn attacks_are_rejected() {
	let two = pack!("two");
	let others = |p: &Pack| p.with_proofs(&p.nodes);
	for (p, what) in [
		(pack!("wrong"), "proves True instead"),
		(pack!("def"), "a def, not a theorem"),
		(pack!("axiom"), "an extra axiom"),
		(pack!("sorry"), "sorry"),
	] {
		assert!(!reveal(two.goal(), &two.pins(), two.env(), &others(&p)), "{what}");
		assert!(!reveal(two.goal(), &[two.pins(), p.pins()].concat(), &[], &others(&p)), "{what}, alone");
	}
	// The solver's own myF: loaded with the poster's, it's a second myF; alone, it proves a
	// statement with another hash.
	let f = pack!("f");
	let redefine = pack!("redefine");
	let pins = [f.pins(), redefine.pins()].concat();
	assert!(!reveal(f.goal(), &pins, f.env(), &others(&redefine)), "redefines myF");
	assert!(!reveal(f.goal(), &pins, &[], &others(&redefine)), "redefines myF, alone");
	assert!(!reveal(two.goal(), &two.pins(), two.env(), &[]), "no proof");
	assert!(!reveal(two.goal(), &two.pins(), two.env(), &[two.goal()]), "the statement without its proof");
}

#[test]
fn proofs_are_type_checked() {
	// GoalTwo edited to say 2 + 2 = 5, with the honest proof (rfl) of 2 + 2 = 4.
	let five = pack!("five");
	assert!(!reveal(five.goal(), &five.pins(), five.env(), &five.with_proofs(&[five.goal()])));
	assert!(!reveal(five.goal(), &five.pins(), &[], &five.with_proofs(&five.nodes)));
	// Its environment is fine, so it attests.
	assert!(attest(&five.pins(), &[], five.env(), &five.with_proofs(five.env())[five.env().len()..]));
}

#[test]
fn the_kernel_builtins_must_be_pinned() {
	let two = pack!("two");
	let solver = two.with_proofs(&[two.goal()]);
	assert!(!reveal(two.goal(), &[], two.env(), &solver), "nothing pinned");
	// Pinning just the goal: `Nat`, `Nat.add` and the rest are declared by unpinned nodes.
	assert!(!reveal(two.goal(), &blake2b256(two.goal()), two.env(), &solver));
}

#[test]
fn checked_nodes_need_their_imports() {
	let two = pack!("two");
	let solver = two.with_proofs(&[two.goal()]);
	let imported: Vec<Hash> = imports(two.goal()).unwrap();
	for skip in two.env().iter().filter(|n| imported.contains(&blake2b256(n))) {
		let env: Vec<&[u8]> = two.env().iter().copied().filter(|n| n != skip).collect();
		assert!(!reveal(two.goal(), &two.pins(), &env, &solver), "without one of the goal's imports");
	}
	// Trusted nodes needn't come with their own imports: only what the kernel touches.
	assert!(reveal(two.goal(), &two.pins(), two.env(), &solver));
}

#[test]
fn trusted_nodes_are_read_only_against_their_imports() {
	let f = pack!("f");
	let redefine = pack!("redefine");
	let hashes = |p: &Pack| p.nodes.iter().map(|n| blake2b256(n)).collect::<Vec<_>>();
	let (f_hashes, redefine_hashes) = (hashes(&f), hashes(&redefine));
	let node = |p: &Pack, h: &Hash| *p.nodes.iter().find(|n| blake2b256(n) == *h).unwrap();
	// GoalF mentions myF; each pack has its own myF, the one its GoalF imports.
	let goal_f = node(&f, &imports(f.goal()).unwrap()[0]);
	let their_goal_f = node(&redefine, &imports(redefine.goal()).unwrap()[0]);
	let my_f = imports(goal_f).unwrap().into_iter().find(|h| !redefine_hashes.contains(h)).unwrap();
	let their_my_f = imports(their_goal_f).unwrap().into_iter().find(|h| !f_hashes.contains(h)).unwrap();
	let load = |nodes: &[&[u8]]| {
		let mut loader = NodeLoader::new(&[]);
		for n in nodes {
			loader.add(blake2b256(n), n, None, true).unwrap();
		}
		loader.finish().is_ok()
	};
	assert!(load(&[goal_f, node(&f, &my_f)]), "GoalF with its own myF");
	assert!(load(&[goal_f]), "GoalF without myF: nothing to misread");
	assert!(!load(&[goal_f, node(&redefine, &their_my_f)]), "GoalF with another myF");
}

#[test]
fn untrusted_theorems_need_their_proofs() {
	let two = pack!("two");
	let f = pack!("f");
	// The closure of GoalF has theorems; leave their proofs out.
	let statements: Vec<&[u8]> = f.nodes.clone();
	let only_goal_proof = [statements.clone(), vec![f.proof_of(f.goal()).unwrap()]].concat();
	assert!(f.proofs.len() > 1);
	assert!(!reveal(f.goal(), &f.pins(), &[], &only_goal_proof));
	// A proof for a trusted node is refused.
	let extra = [two.goal(), two.proof_of(two.goal()).unwrap(), two.proof_of(two.goal()).unwrap()];
	assert!(!reveal(two.goal(), &two.pins(), two.env(), &extra), "a proof twice");
	let trusted_proof = [two.with_proofs(&[two.goal()]), f.proofs[..1].to_vec()].concat();
	assert!(!reveal(two.goal(), &two.pins(), two.env(), &trusted_proof), "a proof of nothing loaded");
}

#[test]
fn attesting_batches() {
	let f = pack!("f");
	let pins = f.pins();
	let proofs_of = |nodes: &[&'static [u8]]| f.with_proofs(nodes)[nodes.len()..].to_vec();
	// The whole closure as one batch.
	assert!(attest(&pins, &[], &f.nodes, &proofs_of(&f.nodes)));
	// In two batches, the second trusting the first.
	let (first, second) = f.nodes.split_at(f.nodes.len() / 2);
	assert!(attest(&pins, &[], first, &proofs_of(first)));
	assert!(attest(&pins, first, second, &proofs_of(second)));
	assert!(!attest(&pins, &[], second, &proofs_of(second)), "without what it imports");
	assert!(!attest(&pins, first, second, &[]), "without its proofs");
	assert!(!attest(&pins, &f.nodes, &[], &[]), "no subjects");
	assert!(!attest(&pins[1..], &[], &f.nodes, &proofs_of(&f.nodes)), "pins not 32 bytes each");
	assert!(!attest(&pins, first, second, &[proofs_of(second), vec![second[0]]].concat()), "a node in the proofs");
	assert!(!attest(&pins, first, &[second, &second[..1]].concat(), &proofs_of(second)), "a node twice");
	// Proofs may come among the subjects instead, or some there and some in the witness.
	let in_bundle = [second, &proofs_of(second)].concat();
	assert!(attest(&pins, first, &in_bundle, &[]), "proofs among the subjects");
	let second_proofs = proofs_of(second);
	let (some, rest) = second_proofs.split_at(1);
	assert!(attest(&pins, first, &[second, some].concat(), rest), "split between the two");
	assert!(!attest(&pins, first, &proofs_of(second), &[]), "proofs but no nodes");
	assert!(!attest(&pins, first, &in_bundle, &proofs_of(second)), "a proof twice");
	assert!(!attest(&pins, first, &[second, &first[..1]].concat(), &proofs_of(second)), "trusted and a subject");
}

#[test]
fn witnesses_parse() {
	assert_eq!(parse_witness(&encode(&[b"ab", b"", b"c"])), Some(vec![&b"ab"[..], b"", b"c"]));
	assert_eq!(parse_witness(&[]), None);
	assert_eq!(parse_witness(&[1, 2, 0]), None, "an item past the end");
	assert_eq!(parse_witness(&[0, 0]), None, "trailing bytes");
}


/// `node` with its `i`th import left out of its header: a node mentioning a constant it doesn't
/// import. (Its hash changes too.)
fn without_import(node: &[u8], i: usize) -> Vec<u8> {
	let mut rest = &node[NODE_MAGIC.len()..];
	let n = uvar(&mut rest).unwrap();
	assert!(n < 128 && i < n);
	let mut out = NODE_MAGIC.to_vec();
	out.push((n - 1) as u8);
	for (j, h) in rest[..32 * n].chunks(32).enumerate() {
		if j != i {
			out.extend_from_slice(h);
		}
	}
	out.extend_from_slice(&rest[32 * n..]);
	out
}

#[test]
fn nodes_must_import_what_they_mention() {
	let two = pack!("two");
	// The non-theorem with the most imports, trusting the nodes before it, which hold its imports.
	let k = (0..two.env().len())
		.filter(|&k| two.proof_of(two.nodes[k]).is_none())
		.max_by_key(|&k| imports(two.nodes[k]).unwrap().len())
		.unwrap();
	let (env, node) = (&two.nodes[..k], two.nodes[k]);
	let n = imports(node).unwrap().len();
	assert!(n > 1);
	assert!(attest(&two.pins(), env, &[node], &[]));
	for i in 0..n {
		// Whatever it no longer imports is still loaded, trusted: it's mentioned, not imported.
		let stripped = without_import(node, i);
		assert!(!attest(&two.pins(), env, &[&stripped], &[]), "import {i} left out");
	}
}
