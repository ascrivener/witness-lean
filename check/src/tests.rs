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

/// Run the check with `pins` (32-byte hashes, back to back; `None` for its own); blobs get their
/// real hashes, as witness gives them.
fn run(mode: CheckMode, blobs: &[(bool, &[u8])], pins: Option<&[u8]>, params: &[u8], witness: &[u8]) -> bool {
	let hashes: Vec<Hash> = blobs.iter().map(|(_, d)| blake2b256(d)).collect();
	let blobs: Vec<_> =
		blobs.iter().zip(&hashes).map(|(&(trusted, data), h)| CheckBlob { trusted, hash: *h, data }).collect();
	let args = check_args(mode, &blobs, params, witness);
	// Type errors panic, which the PVM turns into false.
	std::panic::catch_unwind(|| {
		let input = Input::parse(&args).unwrap();
		match pins {
			Some(pins) => check_with(&input, &super::pins(pins).unwrap()),
			None => check(&input),
		}
	})
	.unwrap_or(false)
}

/// Reveal `solver`'s nodes and proofs for the theorem statement `goal`, trusting `trusted`, with
/// `pins`.
fn reveal(goal: &[u8], pins: &[u8], trusted: &[&[u8]], solver: &[&[u8]]) -> bool {
	let blobs: Vec<(bool, &[u8])> = trusted.iter().map(|n| (true, *n)).collect();
	run(CheckMode::Reveal, &blobs, Some(pins), &blake2b256(goal), &encode(solver))
}

/// Attest `subjects` with `proofs`, trusting `trusted`, with `pins`.
fn attest(pins: &[u8], trusted: &[&[u8]], subjects: &[&[u8]], proofs: &[&[u8]]) -> bool {
	let blobs: Vec<(bool, &[u8])> =
		trusted.iter().map(|n| (true, *n)).chain(subjects.iter().map(|n| (false, *n))).collect();
	run(CheckMode::Attest, &blobs, Some(pins), &[], &encode(proofs))
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
fn the_built_in_pins_are_this_toolchains() {
	// The fixtures are exports on the toolchain the check's pins are for, so its own pins serve.
	let f = pack!("f");
	let proofs = f.with_proofs(&f.nodes)[f.nodes.len()..].to_vec();
	let subjects: Vec<(bool, &[u8])> = f.nodes.iter().map(|n| (false, *n)).collect();
	assert!(run(CheckMode::Attest, &subjects, None, &[], &encode(&proofs)));
	assert!(!run(CheckMode::Attest, &subjects, None, &[0; 32], &encode(&proofs)), "attest params");
	let two = pack!("two");
	let trusted: Vec<(bool, &[u8])> = two.env().iter().map(|n| (true, *n)).collect();
	let solver = encode(&two.with_proofs(&[two.goal()]));
	assert!(run(CheckMode::Reveal, &trusted, None, &blake2b256(two.goal()), &solver));
	let pinned = [blake2b256(two.goal()).as_slice(), PINS].concat();
	assert!(!run(CheckMode::Reveal, &trusted, None, &pinned, &solver), "pins as reveal params");
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

// Splitting an inductive block (see `DECLARATIONS_MAGIC`).

/// A declarations blob naming the declarations at `positions` of node `node`, whole.
fn declarations(node: &[u8], positions: &[usize]) -> Vec<u8> {
	parts(node, &positions.iter().map(|&k| (k, 0)).collect::<Vec<_>>())
}

/// A declarations blob naming `parts` of node `node`: positions and phase bytes.
fn parts(node: &[u8], parts: &[(usize, u8)]) -> Vec<u8> {
	let mut out = DECLARATIONS_MAGIC.to_vec();
	out.extend_from_slice(&blake2b256(node));
	out.push(parts.len() as u8);
	for &(k, p) in parts {
		out.extend_from_slice(&[k as u8, p]);
	}
	out
}

/// The pack's inductive block with the most declarations among those importing something, its
/// position, and how many it holds.
fn biggest_block(p: &Pack) -> (usize, usize) {
	let pins = super::pins(&p.pins()).unwrap();
	let mut loader = NodeLoader::new(&pins);
	for n in &p.nodes {
		loader.add(blake2b256(n), n, None, true).unwrap();
	}
	let nodes = loader.finish().unwrap();
	(0..p.nodes.len())
		.map(|k| (k, nodes.find(&blake2b256(p.nodes[k])).unwrap()))
		.filter(|&(k, i)| nodes.is_inductive_block(i) && !imports(p.nodes[k]).unwrap().is_empty())
		.map(|(k, i)| (k, nodes.declaration_count(i)))
		.max_by_key(|&(_, n)| n)
		.unwrap()
}

/// Attest declarations blobs `subjects` of `node`, trusting `trusted`.
fn attest_declarations(pins: &[u8], trusted: &[&[u8]], subjects: &[&[u8]], node: &[u8]) -> bool {
	let blobs: Vec<(bool, &[u8])> = trusted.iter().map(|n| (true, *n)).chain(subjects.iter().map(|j| (false, *j))).collect();
	run(CheckMode::Attest, &blobs, Some(pins), &[], &encode(&[node]))
}

#[test]
fn inductive_blocks_split_by_declaration() {
	let f = pack!("f");
	let pins = f.pins();
	let (k, n) = biggest_block(&f);
	assert!(n >= 3, "an inductive with constructors and a recursor");
	let (env, node) = (&f.nodes[..k], f.nodes[k]);
	let (first, rest) = (declarations(node, &[0]), declarations(node, &(1..n).collect::<Vec<_>>()));
	assert!(attest_declarations(&pins, env, &[&first], node));
	assert!(attest_declarations(&pins, env, &[&rest], node));
	assert!(attest_declarations(&pins, env, &[&first, &rest], node), "two blobs in one op");
	// The node, citing both, or one (the rest checked here), or none.
	assert!(attest(&pins, &[env, &[&first[..], &rest[..]]].concat(), &[node], &[]));
	assert!(attest(&pins, &[env, &[&first[..]]].concat(), &[node], &[]));
	assert!(attest(&pins, env, &[node], &[]));
	// By a reveal too, with the block among the solver's nodes.
	let trusted: Vec<&[u8]> = f.env().iter().copied().filter(|b| *b != node).chain([&first[..]]).collect();
	let solver = [vec![node], f.with_proofs(&[f.goal()])].concat();
	assert!(reveal(f.goal(), &pins, &trusted, &solver));
	assert!(!reveal(f.goal(), &pins, &[f.env(), &[&first[..]]].concat(), &f.with_proofs(&[f.goal()])), "its node trusted");
}

#[test]
fn only_inductive_blocks_split() {
	let f = pack!("f");
	let pins = f.pins();
	let (k, n) = biggest_block(&f);
	let (env, node) = (&f.nodes[..k], f.nodes[k]);
	// A theorem's node: checking its "declaration" would skip its proof.
	let goal = declarations(f.goal(), &[0]);
	assert!(!attest_declarations(&pins, f.env(), &[&goal], f.goal()));
	let proof = f.proof_of(f.goal()).unwrap();
	assert!(!attest(&pins, &[f.env(), &[&goal[..]]].concat(), &[f.goal()], &[proof]), "cited for a theorem");
	// Positions past the node's end.
	let past = declarations(node, &[n]);
	assert!(!attest_declarations(&pins, env, &[&past], node));
	assert!(!attest(&pins, &[env, &[&past[..]]].concat(), &[node], &[]));
	// For another node than the witness, or cited where that node isn't checked.
	let other = declarations(f.nodes[k - 1], &[0]);
	assert!(!attest_declarations(&pins, env, &[&other], node));
	let first = declarations(node, &[0]);
	assert!(!attest(&pins, &[f.nodes[..=k].to_vec(), vec![&first[..]]].concat(), &[f.nodes[k + 1]], &[]), "its node trusted");
	// Not alongside other subjects, nor without the node.
	assert!(!attest(&pins, env, &[node, &first], &[]));
	let blobs: Vec<(bool, &[u8])> = env.iter().map(|n| (true, *n)).chain([(false, &first[..])]).collect();
	assert!(!run(CheckMode::Attest, &blobs, Some(&pins), &[], &encode(&[])));
}

#[test]
fn a_split_block_is_checked_where_its_hash_pins() {
	// The block's node is loaded as an untrusted one: every import loaded, declaring what it
	// mentions. Without one of them, its declarations aren't checked.
	let f = pack!("f");
	let pins = f.pins();
	let (k, _) = biggest_block(&f);
	let (env, node) = (&f.nodes[..k], f.nodes[k]);
	let first = declarations(node, &[0]);
	let imported = imports(node).unwrap();
	assert!(!imported.is_empty());
	for skip in env.iter().filter(|n| imported.contains(&blake2b256(n))) {
		let fewer: Vec<&[u8]> = env.iter().copied().filter(|n| n != skip).collect();
		assert!(!attest_declarations(&pins, &fewer, &[&first], node), "without one of its imports");
	}
}

#[test]
fn an_inductive_types_check_splits_into_phases() {
	let f = pack!("f");
	let pins = f.pins();
	let (k, n) = biggest_block(&f);
	let (env, node) = (&f.nodes[..k], f.nodes[k]);
	// Position 0 is the block's (first) inductive type; the rest its constructors and recursors.
	let ctors = parts(node, &[(0, 1)]);
	let recs = parts(node, &[(0, 2)]);
	let rest = declarations(node, &(1..n).collect::<Vec<_>>());
	assert!(attest_declarations(&pins, env, &[&ctors], node));
	assert!(attest_declarations(&pins, env, &[&recs], node));
	// Both phases cited: the type is covered; one: the other phase runs where the node's attested.
	assert!(attest(&pins, &[env, &[&ctors[..], &recs[..], &rest[..]]].concat(), &[node], &[]));
	assert!(attest(&pins, &[env, &[&ctors[..], &rest[..]]].concat(), &[node], &[]));
	assert!(attest(&pins, &[env, &[&recs[..]]].concat(), &[node], &[]));
	// Phases only of an inductive type, and only the three.
	let ctor_phase = parts(node, &[(n - 1, 1)]);
	assert!(!attest_declarations(&pins, env, &[&ctor_phase], node), "a phase of a recursor");
	assert!(!attest(&pins, &[env, &[&ctor_phase[..]]].concat(), &[node], &[]));
	let bad = parts(node, &[(0, 3)]);
	assert!(!attest_declarations(&pins, env, &[&bad], node), "no such phase");
}
