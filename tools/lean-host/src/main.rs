//! Runs the Lean check natively, as refine would, and reports how long it takes.
//!
//!     lean-host convert EXPORT OUT [--pack [--no-data]]
//!                                  write OUT as lean_nodes.py would from EXPORT ("-": stdin), in
//!                                  far less memory, for exports the size of all of Mathlib; with
//!                                  --pack, into OUT's pack (see pack.rs) instead of a file a node;
//!                                  with --no-data, recording hashes only (to compare exports)
//!     lean-host pack DIR           move DIR's node and proof files into its pack
//!     lean-host profile DIR OUT    check every node of DIR's pack once, recording each one's time
//!                                  and lookups (see profile.rs)
//!     lean-host nodes DIR          load and check every node of DIR, in order, with its proof
//!     lean-host plan DIR PLAN      attest each batch of PLAN (from lean_plan.py), timing each
//!     lean-host trace DIR PLAN OUT [MS]
//!                                  write OUT: PLAN with each batch trusting only what the kernel
//!                                  looks up while checking it, plus what its nodes import, and
//!                                  split where a batch takes longer than MS (default 100); print
//!                                  `over T: NAME` for each declaration that alone takes longer;
//!                                  each batch in OUT records how long it took (`ms`)
//!
//!     lean-host declarations-args ARGS K[:P],… OUT
//!                                  write OUT: the attest op ARGS, whose one subject is an inductive
//!                                  block's node, checking only its declarations at positions K…,
//!                                  each whole or its phase P (1 constructors, 2 recursors; see the
//!                                  check's DECLARATIONS_MAGIC), for witness-sim
//!
//!     lean-host judgments ARGS OUT [MS [COSTS]]
//!                                  plan judgments for the theorem the attest op ARGS proves (its one
//!                                  untrusted subject), ARGS trusting its whole closure, so that every
//!                                  constant a judgment mentions resolves to the node declaring it:
//!                                  record its check, cut it into ops of at most
//!                                  MS native milliseconds of the kernel's own work (default 25), and
//!                                  write OUT/group-N.judgment, OUT/group-N.calls and OUT/plan.json
//!                                  (each group's round, cites and estimated gas; what the theorem's
//!                                  own attestation cites); with COSTS (judgments-check's
//!                                  costs.json for an earlier plan), grouping by each unit's
//!                                  measured replay time
//!     lean-host judgments-check ARGS OUT
//!                                  run every op of that plan (ARGS as for judgments) through the
//!                                  check natively, in order, then the theorem's own, citing what it
//!                                  plans: each trusting what it looks up (traced in the whole
//!                                  closure) and what it must load; write each op's arguments as
//!                                  OUT/group-N.args and OUT/final.args, for witness-sim, and each
//!                                  unit's replay time as OUT/costs.json; count ops over 45 native
//!                                  ms (about 4.2e9 gas)
//!
//! DIR is a `lean_nodes.py` output directory. What a native millisecond costs in PolkaJam
//! v0.1.29's recompiler depends on the machine (about 29M gas on one, 77M on an M3), so budgets in
//! milliseconds come from gas budgets measured there (`tools/lean/gas_per_ms.py`).

mod convert;
mod pack;
mod profile;

use nanoda_lib::nodes::{Hash, NodeLoader, PINNED_NAMES};
use serde_json::Value;
use std::time::{Duration, Instant};
use witness_types::{CheckBlob, CheckMode, check_args};

fn hex(s: &str) -> Hash {
	std::array::from_fn(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap())
}

fn blake2b256(data: &[u8]) -> Hash {
	let mut out = [0; 32];
	out.copy_from_slice(blake2b_simd::Params::new().hash_length(32).hash(data).as_bytes());
	out
}

struct Dir {
	path: String,
	manifest: Vec<Value>,
	pack: Option<pack::Pack>,
}

impl Dir {
	fn open(path: &str) -> Dir {
		let manifest = serde_json::from_slice(&std::fs::read(format!("{path}/manifest.json")).expect("manifest"));
		let pack = pack::exists(path).then(|| pack::Pack::open(path, false));
		Dir { path: path.to_string(), manifest: manifest.expect("JSON"), pack }
	}
	fn node(&self, h: &str) -> Vec<u8> {
		match &self.pack {
			Some(p) => p.get(pack::NODE, &hex(h)).unwrap_or_else(|| panic!("no node {h}")),
			None => std::fs::read(format!("{}/nodes/{h}", self.path)).unwrap(),
		}
	}
	fn proof(&self, h: &str) -> Option<Vec<u8>> {
		match &self.pack {
			Some(p) => p.get(pack::PROOF, &hex(h)),
			None => std::fs::read(format!("{}/proofs/{h}", self.path)).ok(),
		}
	}
	/// The nodes declaring the names the kernel treats specially, for loading nodes directly (the
	/// check has its own, which these are among on its toolchain).
	fn pins(&self) -> Vec<Hash> {
		let pinned = |e: &&Value| e["names"].as_array().unwrap().iter().any(|n| PINNED_NAMES.contains(&n.as_str().unwrap()));
		self.manifest.iter().filter(pinned).map(|e| hex(e["hash"].as_str().unwrap())).collect()
	}
}

fn nodes(dir: &Dir) {
	let pins = dir.pins();
	let start = Instant::now();
	let mut loader = NodeLoader::new(&pins);
	for e in &dir.manifest {
		let h = e["hash"].as_str().unwrap();
		if let Err(err) = loader.add(hex(h), &dir.node(h), dir.proof(h).as_deref(), false) {
			eprintln!("{}: {err}", e["names"][0]);
			std::process::exit(1);
		}
	}
	let nodes = loader.finish().expect("nodes load");
	let loaded = start.elapsed();
	for i in 0..nodes.nodes.len() {
		nodes.check(i);
	}
	println!("{} nodes ({} pinned) loaded in {loaded:?}, all checked in {:?}", dir.manifest.len(), pins.len(), start.elapsed());
}

/// The check's witness encoding: a count, then each item's length and bytes, LEB128.
fn encode(items: &[Vec<u8>]) -> Vec<u8> {
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

/// Run the check natively; false on a panic, as on the PVM.
fn run(mode: CheckMode, blobs: &[(bool, Vec<u8>)], params: &[u8], witness: &[u8]) -> (bool, Duration) {
	let hashes: Vec<Hash> = blobs.iter().map(|(_, d)| blake2b256(d)).collect();
	let check_blobs: Vec<CheckBlob> =
		blobs.iter().zip(&hashes).map(|((trusted, data), h)| CheckBlob { trusted: *trusted, hash: *h, data }).collect();
	let args = check_args(mode, &check_blobs, params, witness);
	let input = witness_check::Input::parse(&args).expect("well-formed arguments");
	let start = Instant::now();
	let ok = std::panic::catch_unwind(|| lean_check::check(&input)).unwrap_or(false);
	(ok, start.elapsed())
}

fn plan(dir: &Dir, plan: &str) {
	let plan: Vec<Value> = serde_json::from_slice(&std::fs::read(plan).expect("plan")).expect("JSON");
	let mut times = Vec::new();
	for (i, batch) in plan.iter().enumerate() {
		let hashes = |k: &str| batch[k].as_array().unwrap().iter().map(|h| h.as_str().unwrap().to_string()).collect::<Vec<_>>();
		let (trusted, subjects) = (hashes("trusted"), hashes("subjects"));
		let blobs: Vec<(bool, Vec<u8>)> = trusted
			.iter()
			.map(|h| (true, dir.node(h)))
			.chain(subjects.iter().map(|h| (false, dir.node(h))))
			.collect();
		let proofs: Vec<Vec<u8>> = subjects.iter().filter_map(|h| dir.proof(h)).collect();
		let witness = encode(&proofs);
		let (ok, t) = run(CheckMode::Attest, &blobs, &[], &witness);
		let bytes: usize = blobs.iter().map(|(_, d)| d.len()).sum();
		println!("batch {i}: {ok} in {t:?} ({} trusted, {} subjects, {bytes} bytes, {} of proofs)", trusted.len(), subjects.len(), witness.len());
		if !ok {
			std::process::exit(1);
		}
		times.push(t);
	}
	times.sort();
	let total: Duration = times.iter().sum();
	println!("{} batches: total {total:?}, median {:?}, max {:?}", times.len(), times[times.len() / 2], times.last().unwrap());
}

/// Re-plan each batch to trust only the nodes the kernel looks up while checking it (traced),
/// plus the nodes its subjects and their proofs import directly: a trusted node's own imports
/// needn't be loaded (see `nanoda_lib::nodes`). Then time each batch as planned, and split one
/// that takes longer than `budget` in two, until it fits or holds one subject. The goal of a plan
/// made with `lean_plan.py --goal` is traced too.
fn trace(dir: &Dir, plan: &str, out: &str, budget: Duration) {
	let plan: Vec<Value> = serde_json::from_slice(&std::fs::read(plan).expect("plan")).expect("JSON");
	let tracer = Tracer::new(dir);
	let strs = |v: &Value| v.as_array().map(|a| a.iter().map(|h| h.as_str().unwrap().to_string()).collect::<Vec<_>>()).unwrap_or_default();
	let mut out_plan = Vec::new();
	let (mut over, mut slowest) = (0, Duration::ZERO);
	for batch in &plan {
		if let Some(goal) = batch["goal"].as_str() {
			let (keep, t) = tracer.trace(&[goal.to_string()], &strs(&batch["trusted"]));
			slowest = slowest.max(t);
			out_plan.push(serde_json::json!({ "goal": goal, "trusted": keep, "ms": t.as_secs_f64() * 1e3 }));
			continue;
		}
		let mut queue = vec![(strs(&batch["subjects"]), strs(&batch["trusted"]))];
		while let Some((subjects, closure)) = queue.pop() {
			let (keep, t) = tracer.trace(&subjects, &closure);
			if t > budget && subjects.len() > 1 {
				// The second half may trust the first, which is attested before it.
				let (first, second) = subjects.split_at(subjects.len() / 2);
				let second_closure = closure.iter().chain(first).cloned().collect();
				queue.push((second.to_vec(), second_closure));
				queue.push((first.to_vec(), closure));
				continue;
			}
			if t > budget {
				over += 1;
				// For lean_split.py: a theorem whose proof alone takes too long.
				let name = dir.manifest.iter().find(|e| e["hash"] == subjects[0].as_str()).map(|e| &e["names"][0]);
				println!("over {t:?}: {}", name.and_then(Value::as_str).unwrap_or(&subjects[0]));
			}
			slowest = slowest.max(t);
			out_plan.push(serde_json::json!({
				"depth": batch["depth"],
				"subjects": subjects,
				"trusted": keep,
				"ms": t.as_secs_f64() * 1e3,
			}));
		}
	}
	std::fs::write(out, serde_json::to_vec(&out_plan).unwrap()).unwrap();
	println!(
		"{} batches (from {}); slowest {slowest:?}; {over} single-subject batches over {budget:?}",
		out_plan.iter().filter(|b| b.get("subjects").is_some()).count(),
		plan.iter().filter(|b| b.get("subjects").is_some()).count(),
	);
}

struct Tracer<'d> {
	dir: &'d Dir,
	pins: Vec<Hash>,
	position: std::collections::HashMap<String, usize>,
}

impl<'d> Tracer<'d> {
	fn new(dir: &'d Dir) -> Self {
		let position = dir.manifest.iter().enumerate().map(|(i, e)| (e["hash"].as_str().unwrap().to_string(), i)).collect();
		Tracer { dir, pins: dir.pins(), position }
	}

	fn entry(&self, h: &str) -> &Value {
		&self.dir.manifest[self.position[h]]
	}

	/// What checking `subjects` needs trusted, out of `closure`, and how long checking them with
	/// just that takes.
	fn trace(&self, subjects: &[String], closure: &[String]) -> (Vec<String>, Duration) {
		use std::collections::BTreeSet;
		let key = |h: &String| self.position[h.as_str()];
		let mut trusted = closure.to_vec();
		trusted.sort_by_key(key);
		let mut subjects = subjects.to_vec();
		subjects.sort_by_key(key);
		let mut loader = NodeLoader::new(&self.pins);
		for h in &trusted {
			loader.add(hex(h), &self.dir.node(h), None, true).expect("trusted node loads");
		}
		for h in &subjects {
			loader.add(hex(h), &self.dir.node(h), self.dir.proof(h).as_deref(), false).expect("subject loads");
		}
		let nodes = loader.finish().expect("nodes load");
		nanoda_lib::nodes::trace::start();
		for i in trusted.len()..nodes.nodes.len() {
			nodes.check(i);
		}
		let looked_up = nanoda_lib::nodes::trace::stop();
		let subject_set: BTreeSet<&String> = subjects.iter().collect();
		let strs = |v: &Value| v.as_array().map(|a| a.iter().map(|h| h.as_str().unwrap().to_string()).collect::<Vec<_>>()).unwrap_or_default();
		let mut keep: BTreeSet<String> = nodes.nodes[..trusted.len()]
			.iter()
			.filter(|n| looked_up.iter().any(|d| n.declars.contains(d)))
			.map(|n| n.hash.iter().map(|b| format!("{b:02x}")).collect())
			.collect();
		for h in &subjects {
			let e = self.entry(h);
			for i in strs(&e["imports"]).into_iter().chain(strs(&e["proof_imports"])) {
				if !subject_set.contains(&i) {
					keep.insert(i);
				}
			}
		}
		// Time the check as it will run: just what's kept trusted.
		let blobs: Vec<(bool, Vec<u8>)> = keep
			.iter()
			.map(|h| (true, self.dir.node(h)))
			.chain(subjects.iter().map(|h| (false, self.dir.node(h))))
			.collect();
		let proofs: Vec<Vec<u8>> = subjects.iter().filter_map(|h| self.dir.proof(h)).collect();
		let (ok, t) = run(CheckMode::Attest, &blobs, &[], &encode(&proofs));
		assert!(ok, "a traced batch doesn't check: {subjects:?}");
		(keep.into_iter().collect(), t)
	}
}

/// Write the arguments the check gets for batch `n` of `plan`, for running it in PolkaVM with
/// witness's `witness-sim check` to measure its gas.
fn write_args(dir: &Dir, plan: &str, n: usize, out: &str) {
	let plan: Vec<Value> = serde_json::from_slice(&std::fs::read(plan).expect("plan")).expect("JSON");
	let hashes = |k: &str| plan[n][k].as_array().unwrap().iter().map(|h| h.as_str().unwrap().to_string()).collect::<Vec<_>>();
	let (trusted, subjects) = (hashes("trusted"), hashes("subjects"));
	let blobs: Vec<(bool, Vec<u8>)> =
		trusted.iter().map(|h| (true, dir.node(h))).chain(subjects.iter().map(|h| (false, dir.node(h)))).collect();
	let proofs: Vec<Vec<u8>> = subjects.iter().filter_map(|h| dir.proof(h)).collect();
	let hashes: Vec<Hash> = blobs.iter().map(|(_, d)| blake2b256(d)).collect();
	let check_blobs: Vec<CheckBlob> =
		blobs.iter().zip(&hashes).map(|((trusted, data), h)| CheckBlob { trusted: *trusted, hash: *h, data }).collect();
	std::fs::write(out, check_args(CheckMode::Attest, &check_blobs, &[], &encode(&proofs))).unwrap();
}

/// The attest op `args`, its one subject an inductive block's node, as an op checking only the
/// declarations at `positions`.
fn declarations_args(args: &str, positions: &str, out: &str) {
	let args = std::fs::read(args).expect("arguments");
	let input = witness_check::Input::parse(&args).expect("well-formed arguments");
	let node = input.blobs().find(|b| !b.trusted).expect("a subject").data.to_vec();
	let parts: Vec<(u8, u8)> = positions
		.split(',')
		.map(|kp| match kp.split_once(':') {
			Some((k, p)) => (k.parse().expect("a position"), p.parse().expect("a phase")),
			None => (kp.parse().expect("a position"), 0),
		})
		.collect();
	let mut subject = lean_check::DECLARATIONS_MAGIC.to_vec();
	subject.extend_from_slice(&blake2b256(&node));
	subject.push(parts.len() as u8);
	for (k, p) in parts {
		subject.extend_from_slice(&[k, p]);
	}
	let mut blobs: Vec<(bool, Vec<u8>)> = input.blobs().filter(|b| b.trusted).map(|b| (true, b.data.to_vec())).collect();
	blobs.push((false, subject));
	let hashes: Vec<Hash> = blobs.iter().map(|(_, d)| blake2b256(d)).collect();
	let check_blobs: Vec<CheckBlob> =
		blobs.iter().zip(&hashes).map(|((trusted, data), h)| CheckBlob { trusted: *trusted, hash: *h, data }).collect();
	std::fs::write(out, check_args(CheckMode::Attest, &check_blobs, &[], &encode(&[node]))).unwrap();
}

/// Plan judgments for the one untrusted theorem of the attest op `args`.
fn judgments(args: &str, out: &str, budget_ms: f64, costs: Option<&str>) {
	let bytes = std::fs::read(args).expect("arguments");
	let input = witness_check::Input::parse(&bytes).expect("well-formed arguments");
	let start = Instant::now();
	let nodes = lean_check::load_attest(&input).expect("nodes load");
	let i = nodes.nodes.iter().position(|n| n.theorem && !n.assumed).expect("an untrusted theorem");
	let unit_costs = costs.map(|c| {
		let v: Value = serde_json::from_slice(&std::fs::read(c).expect("costs")).expect("JSON");
		v.as_object().unwrap().iter().map(|(k, ns)| (k.parse().unwrap(), ns.as_u64().unwrap())).collect()
	});
	let cfg = nanoda_lib::plan::PlanConfig { budget_ns: (budget_ms * 1e6) as u64, unit_costs, ..Default::default() };
	let plan = nodes.plan_judgments(i, &cfg).expect("planned");
	std::fs::create_dir_all(out).unwrap();
	let mut groups = Vec::new();
	for (g, group) in plan.groups.iter().enumerate() {
		std::fs::write(format!("{out}/group-{g}.judgment"), &group.judgment).unwrap();
		std::fs::write(format!("{out}/group-{g}.calls"), &group.calls).unwrap();
		groups.push(serde_json::json!({
			"round": group.round, "cites": group.cites, "units": group.units, "gas": group.gas,
			"judgment_bytes": group.judgment.len(), "calls_bytes": group.calls.len(),
			"unit_ns": group.unit_ns,
		}));
	}
	let summary = serde_json::json!({
		"declaration": nodes.nodes[i].hash.iter().map(|b| format!("{b:02x}")).collect::<String>(),
		"calls": plan.calls, "units": plan.units, "rounds": plan.rounds,
		"groups": groups, "final_cites": plan.final_cites, "final_gas": plan.final_gas,
	});
	std::fs::write(format!("{out}/plan.json"), serde_json::to_vec_pretty(&summary).unwrap()).unwrap();
	let max_gas = plan.groups.iter().map(|g| g.gas).fold(plan.final_gas, f64::max);
	println!(
		"{} calls, {} units, {} rounds, {} ops (+ the theorem's own, citing {}); estimated gas: max {max_gas:.2e}; {} needs recomputed; planned in {:?}",
		plan.calls, plan.units, plan.rounds, plan.groups.len(), plan.final_cites.len(), plan.skipped, start.elapsed()
	);
}

/// The hashes a node (or, after the statement's hash, a proof) imports.
fn import_hashes(mut bytes: &[u8]) -> Vec<Hash> {
	let mut n = 0usize;
	let mut shift = 0;
	loop {
		let b = bytes[0];
		bytes = &bytes[1..];
		n |= usize::from(b & 0x7f) << shift;
		shift += 7;
		if b & 0x80 == 0 {
			break;
		}
	}
	(0..n).map(|k| bytes[32 * k..32 * k + 32].try_into().unwrap()).collect()
}

/// The nodes `f` looks up, checking in a closure of `trusted` nodes and `node` (untrusted, with
/// `proof` if given), by hash.
fn traced_op(trusted: &[Vec<u8>], node: &[u8], proof: Option<&[u8]>, f: impl Fn(&nanoda_lib::nodes::Nodes, usize)) -> std::collections::BTreeSet<Hash> {
	let mut blobs: Vec<(bool, Vec<u8>)> = trusted.iter().map(|d| (true, d.clone())).collect();
	blobs.push((false, node.to_vec()));
	if let Some(p) = proof {
		blobs.push((false, p.to_vec()));
	}
	let hashes: Vec<Hash> = blobs.iter().map(|(_, d)| blake2b256(d)).collect();
	let check_blobs: Vec<CheckBlob> = blobs.iter().zip(&hashes).map(|((t, d), h)| CheckBlob { trusted: *t, hash: *h, data: d }).collect();
	let args = check_args(CheckMode::Attest, &check_blobs, &[], &encode(&[]));
	let input = witness_check::Input::parse(&args).unwrap();
	let nodes = lean_check::load_attest(&input).expect("nodes load");
	let i = nodes.find(&blake2b256(node)).unwrap();
	nanoda_lib::nodes::trace::start();
	f(&nodes, i);
	let looked_up = nanoda_lib::nodes::trace::stop();
	nodes.nodes.iter().filter(|n| looked_up.iter().any(|d| n.declars.contains(d))).map(|n| n.hash).collect()
}

/// Run a judgment plan's ops through the check, then the theorem's own attestation, each trusting
/// just what it looks up (traced against the theorem's whole closure) and what it must load: the
/// nodes the theorem's statement (and, for its own attestation, its proof) imports, and for a
/// judgment op the nodes its judgment imports.
fn judgments_check(full: &str, out: &str) {
	let bytes = std::fs::read(full).expect("arguments");
	let input = witness_check::Input::parse(&bytes).expect("well-formed arguments");
	let plan: Value = serde_json::from_slice(&std::fs::read(format!("{out}/plan.json")).unwrap()).unwrap();
	let closure: Vec<Vec<u8>> = input.blobs().filter(|b| b.trusted).map(|b| b.data.to_vec()).collect();
	let by_hash: std::collections::HashMap<Hash, Vec<u8>> = closure.iter().map(|d| (blake2b256(d), d.clone())).collect();
	let node = input.blobs().find(|b| !b.trusted && b.data.starts_with(nanoda_lib::nodes::NODE_MAGIC)).expect("a node").data.to_vec();
	let proof: Vec<u8> = input
		.blobs()
		.map(|b| b.data.to_vec())
		.chain(lean_check::parse_witness(input.witness).unwrap().into_iter().map(<[u8]>::to_vec))
		.find(|d| d.starts_with(nanoda_lib::nodes::PROOF_MAGIC))
		.expect("a proof");
	let statement_imports = import_hashes(&node[nanoda_lib::nodes::NODE_MAGIC.len()..]);
	let judgment = |g: u64| std::fs::read(format!("{out}/group-{g}.judgment")).unwrap();
	let run = |blobs: &[(bool, Vec<u8>)], witness: &[u8], name: &str| -> (bool, usize) {
		let hashes: Vec<Hash> = blobs.iter().map(|(_, d)| blake2b256(d)).collect();
		let check_blobs: Vec<CheckBlob> =
			blobs.iter().zip(&hashes).map(|((t, d), h)| CheckBlob { trusted: *t, hash: *h, data: d }).collect();
		let a = check_args(CheckMode::Attest, &check_blobs, &[], witness);
		std::fs::write(format!("{out}/{name}.args"), &a).unwrap();
		let input = witness_check::Input::parse(&a).unwrap();
		(std::panic::catch_unwind(|| lean_check::check(&input)).unwrap_or(false), a.len())
	};
	let env = |keep: std::collections::BTreeSet<Hash>| -> Vec<(bool, Vec<u8>)> {
		keep.into_iter().filter(|h| *h != blake2b256(&node)).map(|h| (true, by_hash[&h].clone())).collect()
	};
	let groups = plan["groups"].as_array().unwrap();
	let (mut worst, mut failed, mut biggest, mut over) = (Duration::ZERO, 0, 0, 0);
	let mut costs = serde_json::Map::new();
	for (g, group) in groups.iter().enumerate() {
		let cited: Vec<Vec<u8>> = group["cites"].as_array().unwrap().iter().map(|c| judgment(c.as_u64().unwrap())).collect();
		let mine = judgment(g as u64);
		let calls = std::fs::read(format!("{out}/group-{g}.calls")).unwrap();
		let cited_refs: Vec<&[u8]> = cited.iter().map(Vec::as_slice).collect();
		let mut keep = traced_op(&closure, &node, None, |nodes, i| {
			nodes.attest_judgments(i, &cited_refs, &calls, &[&mine]).expect("the op checks in the whole closure")
		});
		keep.extend(nanoda_lib::judgment::header(&mine).unwrap().imports);
		keep.extend(statement_imports.iter().copied());
		let mut blobs = env(keep);
		blobs.extend(cited.into_iter().map(|c| (true, c)));
		blobs.push((false, mine));
		let env_bytes: usize = blobs.iter().filter(|(t, d)| *t && d.starts_with(nanoda_lib::nodes::NODE_MAGIC)).map(|(_, d)| d.len()).sum();
		let env_nodes = blobs.iter().filter(|(t, d)| *t && d.starts_with(nanoda_lib::nodes::NODE_MAGIC)).count();
		let cited_bytes: usize = blobs.iter().filter(|(t, d)| *t && d.starts_with(nanoda_lib::judgment::JUDGMENT_MAGIC)).map(|(_, d)| d.len()).sum();
		let own_bytes = blobs.last().unwrap().1.len();
		let calls_bytes = calls.len();
		let t0 = Instant::now();
		let (ok, size) = run(&blobs, &encode(&[node.clone(), calls]), &format!("group-{g}"));
		worst = worst.max(t0.elapsed());
		if t0.elapsed() > Duration::from_millis(45) {
			over += 1;
		}
		let times = nanoda_lib::judgment::CALL_TIMES.lock().unwrap().clone();
		for (unit, ns) in group["unit_ns"].as_array().unwrap().iter().zip(times) {
			costs.insert(unit[0].as_u64().unwrap().to_string(), Value::from(ns));
		}
		println!(
			"op {g} round {} units {} est {:.2e}: {:.1} ms; env {env_nodes} nodes {} KB, cited {} KB, own {} KB, calls {} KB",
			group["round"], group["units"], group["gas"].as_f64().unwrap(), t0.elapsed().as_secs_f64() * 1e3,
			env_bytes / 1000, cited_bytes / 1000, own_bytes / 1000, calls_bytes / 1000
		);
		biggest = biggest.max(size);
		if !ok {
			failed += 1;
			println!("group {g} (round {}, {} units) FAILED", group["round"], group["units"]);
		}
	}
	let cited: Vec<Vec<u8>> = plan["final_cites"].as_array().unwrap().iter().map(|c| judgment(c.as_u64().unwrap())).collect();
	let cited_refs: Vec<&[u8]> = cited.iter().map(Vec::as_slice).collect();
	let mut keep = traced_op(&closure, &node, Some(&proof), |nodes, i| nodes.check_with(i, &cited_refs).expect("checks"));
	keep.extend(statement_imports.iter().copied());
	keep.extend(import_hashes(&proof[nanoda_lib::nodes::PROOF_MAGIC.len() + 32..]));
	let mut blobs = env(keep);
	blobs.extend(cited.into_iter().map(|c| (true, c)));
	blobs.push((false, node.clone()));
	let t0 = Instant::now();
	let (ok, size) = run(&blobs, &encode(std::slice::from_ref(&proof)), "final");
	std::fs::write(format!("{out}/costs.json"), serde_json::to_vec(&costs).unwrap()).unwrap();
	println!(
		"{} ops, {failed} failed, {over} over 45 ms, slowest {worst:?}, biggest arguments {} KB; the theorem's own: {ok} in {:?} ({} KB)",
		groups.len(),
		biggest / 1000,
		t0.elapsed(),
		size / 1000
	);
	if failed > 0 || !ok {
		std::process::exit(1);
	}
}

fn main() {
	// Type errors panic, which counts as false, as on the PVM.
	std::panic::set_hook(Box::new(|info| eprintln!("check panicked: {info}")));
	let args: Vec<String> = std::env::args().skip(1).collect();
	match args.iter().map(String::as_str).collect::<Vec<_>>()[..] {
		["convert", export, out] => convert::convert(export, out, false, false),
		["convert", export, out, "--pack"] => convert::convert(export, out, true, false),
		["convert", export, out, "--pack", "--no-data"] => convert::convert(export, out, true, true),
		["pack", dir] => pack::pack_dir(dir),
		["profile", dir, out] => profile::profile(dir, out),
		["nodes", dir] => nodes(&Dir::open(dir)),
		["plan", dir, p] => plan(&Dir::open(dir), p),
		["run", args] => {
			let args = std::fs::read(args).expect("arguments");
			let input = witness_check::Input::parse(&args).expect("well-formed arguments");
			let start = Instant::now();
			let ok = std::panic::catch_unwind(|| lean_check::check(&input)).unwrap_or(false);
			println!("{ok} in {:?}", start.elapsed());
		},
		["declarations-args", args, positions, out] => declarations_args(args, positions, out),
		["judgments", args, out] => judgments(args, out, 25.0, None),
		["judgments", args, out, ms] => judgments(args, out, ms.parse().expect("milliseconds"), None),
		["judgments", args, out, ms, costs] => judgments(args, out, ms.parse().expect("milliseconds"), Some(costs)),
		["judgments-check", full, out] => judgments_check(full, out),
		["args", dir, p, n, out] => write_args(&Dir::open(dir), p, n.parse().expect("batch number"), out),
		["trace", dir, p, out] => trace(&Dir::open(dir), p, out, Duration::from_millis(100)),
		["trace", dir, p, out, ms] => trace(&Dir::open(dir), p, out, Duration::from_millis(ms.parse().expect("milliseconds"))),
		_ => {
			eprintln!("usage: lean-host convert EXPORT OUT | lean-host nodes DIR | lean-host plan DIR PLAN | lean-host trace DIR PLAN OUT [MS]");
			std::process::exit(2);
		},
	}
}
