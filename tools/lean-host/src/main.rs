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
//!     lean-host reveal DIR GOAL…   run the check as a bounty's reveal, every node of DIR in the
//!                                  witness, once for each GOAL (a statement node's hash): print
//!                                  which it proves; exit 1 if none (for checking a solution
//!                                  before submitting it)
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
//!                                  write OUT/blob-N.judgment (each op attests one or more),
//!                                  OUT/group-N.calls and OUT/plan.json (each group's round,
//!                                  judgments, cites and estimated gas; what the theorem's
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
//!     lean-host split-inductive ARGS OUT [MS]
//!                                  split the inductive block the attest op ARGS attests (its one
//!                                  untrusted node) into ops of at most MS native milliseconds
//!                                  (default 40): each declaration whole, or an inductive type by
//!                                  phase when it's over, packed into ops; write each op's arguments
//!                                  as OUT/part-N.args, then the node's own, citing them, as
//!                                  OUT/final.args, and check them all natively
//!
//!     lean-host pack-args DIR LIST OUT
//!                                  write OUT: the attest op for the node LIST's first line names
//!                                  (hex), from DIR's pack, trusting the nodes its other lines name,
//!                                  with its proof as the witness if it has one
//!     lean-host judgments-ops ARGS OUT
//!                                  as judgments-check, faster, for many declarations: load ARGS's
//!                                  closure once, trace every op of OUT's plan in it, and write
//!                                  OUT/ops.json (each op's subject, witness, trusted nodes and the
//!                                  ops it cites; what the theorem's own attestation trusts and
//!                                  cites), the ops' witnesses, and OUT/costs.json; with VERIFY set,
//!                                  also each op's arguments, checked natively
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

/// An unsigned LEB128 varint.
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

/// A declarations blob for `node`'s `parts` (positions and phases; see the check's
/// DECLARATIONS_MAGIC).
fn declarations_blob(node: &[u8], parts: &[(usize, u8)]) -> Vec<u8> {
	let mut out = lean_check::DECLARATIONS_MAGIC.to_vec();
	out.extend_from_slice(&blake2b256(node));
	uvar(&mut out, parts.len());
	for &(k, p) in parts {
		uvar(&mut out, k);
		out.push(p);
	}
	out
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

/// Run the check in reveal mode as a bounty's reveal would, with every node of DIR (and its
/// proof) in the witness, untrusted, so all of them are checked: for each of GOALS (statement
/// node hashes), print whether the reveal proves it. Exits 1 if none is proven.
fn reveal(dir: &Dir, goals: &[&str]) {
	let mut items = Vec::new();
	for e in &dir.manifest {
		let h = e["hash"].as_str().unwrap();
		items.push(dir.node(h));
		items.extend(dir.proof(h));
	}
	let witness = encode(&items);
	let mut proven = false;
	for goal in goals {
		let (ok, t) = run(CheckMode::Reveal, &[], &hex(goal), &witness);
		println!("{goal}: {} in {t:?}", if ok { "proven" } else { "not proven" });
		proven |= ok;
	}
	if !proven {
		std::process::exit(1);
	}
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
	let parts: Vec<(usize, u8)> = positions
		.split(',')
		.map(|kp| match kp.split_once(':') {
			Some((k, p)) => (k.parse().expect("a position"), p.parse().expect("a phase")),
			None => (kp.parse().expect("a position"), 0),
		})
		.collect();
	let subject = declarations_blob(&node, &parts);
	let mut blobs: Vec<(bool, Vec<u8>)> = input.blobs().filter(|b| b.trusted).map(|b| (true, b.data.to_vec())).collect();
	blobs.push((false, subject));
	let hashes: Vec<Hash> = blobs.iter().map(|(_, d)| blake2b256(d)).collect();
	let check_blobs: Vec<CheckBlob> =
		blobs.iter().zip(&hashes).map(|((trusted, data), h)| CheckBlob { trusted: *trusted, hash: *h, data }).collect();
	std::fs::write(out, check_args(CheckMode::Attest, &check_blobs, &[], &encode(&[node]))).unwrap();
}

/// Plan judgments for the one untrusted declaration of the attest op `args`.
fn judgments(args: &str, out: &str, budget_ms: f64, costs: Option<&str>) {
	let bytes = std::fs::read(args).expect("arguments");
	let input = witness_check::Input::parse(&bytes).expect("well-formed arguments");
	let start = Instant::now();
	let nodes = lean_check::load_attest(&input).expect("nodes load");
	let node = input.blobs().find(|b| !b.trusted && b.data.starts_with(nanoda_lib::nodes::NODE_MAGIC)).expect("an untrusted node");
	let i = nodes.find(&blake2b256(node.data)).expect("the untrusted node loaded");
	let unit_costs = costs.map(|c| {
		let v: Value = serde_json::from_slice(&std::fs::read(c).expect("costs")).expect("JSON");
		// Each unit's cost: its run, its seeding and how many it seeded (`judgments-ops`), or a
		// single figure, all run.
		let cost = |c: &Value| match c.as_u64() {
			Some(run) => nanoda_lib::plan::UnitCost { run, seed: 0, seeds: 0 },
			None => nanoda_lib::plan::UnitCost {
				run: c["run"].as_u64().unwrap(),
				seed: c["seed"].as_u64().unwrap(),
				seeds: u32::try_from(c["seeds"].as_u64().unwrap()).unwrap(),
			},
		};
		v.as_object().unwrap().iter().map(|(k, c)| (k.parse().unwrap(), cost(c))).collect()
	});
	// The op's witness is the theorem's node and the calls: at most 64 KiB (witness's
	// MAX_WITNESS_LEN), with room for its encoding.
	let node_len = input.blobs().find(|b| !b.trusted && b.data.starts_with(nanoda_lib::nodes::NODE_MAGIC)).map_or(0, |b| b.data.len());
	// Overrides, for tuning: PLAN_OP_GAS (an op's estimated gas), PLAN_RELAY_MB (citing more than
	// this goes through relays), PLAN_CALLS_KB (a calls blob, if the witness can be an extrinsic);
	// PLAN_FINE=0 writes each op's judgment whole, citing through relays; otherwise each is split
	// by which ops seed it, tuned by PLAN_BLOB_OVERHEAD (bytes), PLAN_OWN_PER_CITED, PLAN_MAX_BLOBS
	// and PLAN_CITE_FACTOR (see PlanConfig).
	let var = |k: &str| std::env::var(k).ok().map(|v| v.parse::<f64>().expect("a number"));
	let defaults = nanoda_lib::plan::PlanConfig::default();
	// What every op of this declaration loads besides what its units look up: the declaration's
	// node, what its statement imports, and the check's pinned nodes (`judgments-ops`).
	let sizes: std::collections::HashMap<Hash, usize> = input.blobs().filter(|b| b.trusted).map(|b| (*b.hash, b.data.len())).collect();
	let mut fixed: std::collections::BTreeSet<Hash> = import_hashes(&node.data[nanoda_lib::nodes::NODE_MAGIC.len()..]).into_iter().collect();
	fixed.extend(lean_check::PINS.chunks(32).map(|c| <Hash>::try_from(c).unwrap()));
	let env_bytes = node_len + fixed.iter().filter_map(|h| sizes.get(h)).sum::<usize>();
	let cfg = nanoda_lib::plan::PlanConfig {
		budget_ns: (budget_ms * 1e6) as u64,
		unit_costs,
		env_bytes,
		max_calls_bytes: var("PLAN_CALLS_KB").map_or(64 * 1024 - 1024 - node_len, |kb| (kb * 1024.0) as usize),
		op_gas: var("PLAN_OP_GAS").unwrap_or(defaults.op_gas),
		relay_bytes: var("PLAN_RELAY_MB").map_or(defaults.relay_bytes, |mb| (mb * 1e6) as usize),
		fine: var("PLAN_FINE").map_or(defaults.fine, |f| f != 0.0),
		blob_overhead: var("PLAN_BLOB_OVERHEAD").unwrap_or(defaults.blob_overhead),
		own_per_cited: var("PLAN_OWN_PER_CITED").unwrap_or(defaults.own_per_cited),
		max_blobs: var("PLAN_MAX_BLOBS").map_or(defaults.max_blobs, |n| n as usize),
		cite_factor: var("PLAN_CITE_FACTOR").unwrap_or(defaults.cite_factor),
		..defaults
	};
	let plan = nodes.plan_judgments(i, &cfg).expect("planned");
	std::fs::create_dir_all(out).unwrap();
	let mut groups = Vec::new();
	let mut blobs = Vec::new();
	for (g, group) in plan.groups.iter().enumerate() {
		for (&b, j) in group.blobs.iter().zip(&group.judgments) {
			std::fs::write(format!("{out}/blob-{b}.judgment"), j).unwrap();
			blobs.push(serde_json::json!({"group": g, "bytes": j.len()}));
		}
		std::fs::write(format!("{out}/group-{g}.calls"), &group.calls).unwrap();
		groups.push(serde_json::json!({
			"round": group.round, "blobs": group.blobs, "cites": group.cites, "units": group.units, "gas": group.gas,
			"judgment_bytes": group.judgments.iter().map(Vec::len).sum::<usize>(), "calls_bytes": group.calls.len(),
			"unit_ns": group.unit_ns, "env": group.env, "work": group.work,
		}));
	}
	let cited: Vec<usize> = plan.groups.iter().map(|g| g.cites.iter().map(|&b| blobs[b]["bytes"].as_u64().unwrap() as usize).sum()).collect();
	let summary = serde_json::json!({
		"declaration": nodes.nodes[i].hash.iter().map(|b| format!("{b:02x}")).collect::<String>(),
		"calls": plan.calls, "units": plan.units, "rounds": plan.rounds,
		"groups": groups, "blobs": blobs, "final_cites": plan.final_cites, "final_gas": plan.final_gas,
	});
	std::fs::write(format!("{out}/plan.json"), serde_json::to_vec_pretty(&summary).unwrap()).unwrap();
	let max_gas = plan.groups.iter().map(|g| g.gas).fold(plan.final_gas, f64::max);
	// Planned with measured costs, an op estimated over what witness lets a check use won't pass,
	// unless the estimate is high: PLAN_MAX_GAS raises the limit, to measure the ops in PolkaVM.
	let limit = var("PLAN_MAX_GAS").unwrap_or(5e9);
	let over = plan.groups.iter().filter(|g| g.gas > limit).count();
	if cfg.unit_costs.is_some() && over > 0 {
		eprintln!("{over} ops estimated over {limit:.2e} gas (max {max_gas:.2e}): a unit too heavy to cut");
		std::process::exit(1);
	}
	println!(
		"{} calls, {} units, {} rounds, {} ops (+ the theorem's own, citing {}), {} judgments of {} KB, cited {} KB in all (most {} cites); estimated gas: max {max_gas:.2e}; {} needs recomputed; planned in {:?}",
		plan.calls, plan.units, plan.rounds, plan.groups.len(), plan.final_cites.len(), plan.blob_group.len(),
		plan.groups.iter().flat_map(|g| g.judgments.iter().map(Vec::len)).sum::<usize>() / 1000, cited.iter().sum::<usize>() / 1000,
		plan.groups.iter().map(|g| g.cites.len()).max().unwrap_or(0), plan.skipped, start.elapsed()
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
	let judgment = |b: u64| std::fs::read(format!("{out}/blob-{b}.judgment")).unwrap();
	let mine_of = |group: &Value| -> Vec<Vec<u8>> { group["blobs"].as_array().unwrap().iter().map(|b| judgment(b.as_u64().unwrap())).collect() };
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
		let mine = mine_of(group);
		let mine_refs: Vec<&[u8]> = mine.iter().map(Vec::as_slice).collect();
		let calls = std::fs::read(format!("{out}/group-{g}.calls")).unwrap();
		let cited_refs: Vec<&[u8]> = cited.iter().map(Vec::as_slice).collect();
		let mut keep = traced_op(&closure, &node, None, |nodes, i| {
			nodes.attest_judgments(i, &cited_refs, &calls, &mine_refs).expect("the op checks in the whole closure")
		});
		for j in &mine {
			keep.extend(nanoda_lib::judgment::header(j).unwrap().imports);
		}
		keep.extend(statement_imports.iter().copied());
		let mut blobs = env(keep);
		blobs.extend(cited.into_iter().map(|c| (true, c)));
		let own_bytes: usize = mine.iter().map(Vec::len).sum();
		blobs.extend(mine.into_iter().map(|j| (false, j)));
		let env_bytes: usize = blobs.iter().filter(|(t, d)| *t && d.starts_with(nanoda_lib::nodes::NODE_MAGIC)).map(|(_, d)| d.len()).sum();
		let env_nodes = blobs.iter().filter(|(t, d)| *t && d.starts_with(nanoda_lib::nodes::NODE_MAGIC)).count();
		let cited_bytes: usize = blobs.iter().filter(|(t, d)| *t && d.starts_with(nanoda_lib::judgment::JUDGMENT_MAGIC)).map(|(_, d)| d.len()).sum();
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

/// Split the inductive block that `args` attests into ops of at most `budget` native time: each
/// declaration whole, or an inductive type over budget by phase, packed into ops in order, each
/// trusting what it looks up (traced in the closure `args` trusts) and the block's imports. Writes
/// OUT/part-N.dcl and OUT/part-N.witness, and OUT/ops.json as judgments-ops does; with VERIFY set,
/// also each op's arguments and the node's own, checked natively.
fn split_inductive(args: &str, out: &str, budget: Duration) {
	use nanoda_lib::env::Phase;
	let verify = std::env::var_os("VERIFY").is_some();
	let bytes = std::fs::read(args).expect("arguments");
	let input = witness_check::Input::parse(&bytes).expect("well-formed arguments");
	let closure: Vec<Vec<u8>> = input.blobs().filter(|b| b.trusted).map(|b| b.data.to_vec()).collect();
	let by_hash: std::collections::HashMap<Hash, &[u8]> = closure.iter().map(|d| (blake2b256(d), &d[..])).collect();
	let node = input.blobs().find(|b| !b.trusted).expect("a node").data.to_vec();
	let node_hash = blake2b256(&node);
	let imports = import_hashes(&node[nanoda_lib::nodes::NODE_MAGIC.len()..]);
	let nodes = lean_check::load_attest(&input).expect("nodes load");
	let i = nodes.find(&node_hash).expect("the node");
	assert!(nodes.is_inductive_block(i), "not an inductive block");
	// A part's time, and the nodes its check looks up.
	let run = |k: usize, phase: Phase| {
		nanoda_lib::nodes::trace::start();
		let t0 = Instant::now();
		nodes.check_parts(i, |j| if j == k { vec![phase] } else { vec![] });
		let t = t0.elapsed();
		let declars = nanoda_lib::nodes::trace::stop();
		let keep: std::collections::BTreeSet<Hash> =
			nodes.nodes.iter().filter(|n| declars.iter().any(|d| n.declars.contains(d))).map(|n| n.hash).collect();
		(t, keep)
	};
	let mut parts: Vec<((usize, u8), Duration, std::collections::BTreeSet<Hash>)> = Vec::new();
	for k in 0..nodes.declaration_count(i) {
		let (whole, keep) = run(k, Phase::Whole);
		if whole > budget && nodes.is_inductive_type(i, k) {
			let (t, keep) = run(k, Phase::Constructors);
			parts.push(((k, 1), t, keep));
			let (t, keep) = run(k, Phase::Recursors);
			parts.push(((k, 2), t, keep));
		} else {
			parts.push(((k, 0), whole, keep));
		}
	}
	let mut ops: Vec<(Vec<(usize, u8)>, std::collections::BTreeSet<Hash>)> = vec![Default::default()];
	let mut used = Duration::ZERO;
	for (part, t, keep) in parts {
		if used + t > budget && !ops.last().unwrap().0.is_empty() {
			ops.push(Default::default());
			used = Duration::ZERO;
		}
		let op = ops.last_mut().unwrap();
		op.0.push(part);
		op.1.extend(keep);
		used += t;
	}
	std::fs::create_dir_all(out).unwrap();
	let check = |blobs: &[(bool, &[u8])], witness: &[u8], name: &str| -> bool {
		let hashes: Vec<Hash> = blobs.iter().map(|(_, d)| blake2b256(d)).collect();
		let check_blobs: Vec<CheckBlob> = blobs.iter().zip(&hashes).map(|((t, d), h)| CheckBlob { trusted: *t, hash: *h, data: d }).collect();
		let a = check_args(CheckMode::Attest, &check_blobs, &[], witness);
		std::fs::write(format!("{out}/{name}.args"), &a).unwrap();
		let input = witness_check::Input::parse(&a).unwrap();
		std::panic::catch_unwind(|| lean_check::check(&input)).unwrap_or(false)
	};
	let mut manifest = Vec::new();
	let mut failed = 0;
	let witness = encode(std::slice::from_ref(&node));
	for (n, (op, keep)) in ops.iter().enumerate() {
		let subject = declarations_blob(&node, op);
		std::fs::write(format!("{out}/part-{n}.dcl"), &subject).unwrap();
		std::fs::write(format!("{out}/part-{n}.witness"), &witness).unwrap();
		let mut keep = keep.clone();
		keep.extend(imports.iter().copied());
		keep.remove(&node_hash);
		if verify {
			let mut blobs: Vec<(bool, &[u8])> = keep.iter().map(|h| (true, by_hash[h])).collect();
			blobs.push((false, &subject));
			if !check(&blobs, &witness, &format!("part-{n}")) {
				println!("part {n} FAILED");
				failed += 1;
			}
		}
		manifest.push(serde_json::json!({
			"name": format!("part-{n}"),
			"subject": format!("part-{n}.dcl"),
			"witness": format!("part-{n}.witness"),
			"trust_nodes": keep.iter().map(hex_of).collect::<Vec<_>>(),
			"trust_ops": Vec::<String>::new(),
		}));
	}
	// The node's own attestation checks nothing left: it trusts its imports and cites every part.
	let summary = serde_json::json!({
		"node": hex_of(&node_hash),
		"ops": manifest,
		"final": {
			"trust_nodes": imports.iter().filter(|h| **h != node_hash).map(hex_of).collect::<Vec<_>>(),
			"trust_ops": (0..ops.len()).map(|n| format!("part-{n}")).collect::<Vec<_>>(),
		},
	});
	std::fs::write(format!("{out}/ops.json"), serde_json::to_vec(&summary).unwrap()).unwrap();
	if verify {
		let parts: Vec<Vec<u8>> = (0..ops.len()).map(|n| std::fs::read(format!("{out}/part-{n}.dcl")).unwrap()).collect();
		let mut blobs: Vec<(bool, &[u8])> = imports.iter().filter_map(|h| by_hash.get(h).map(|d| (true, *d))).collect();
		blobs.extend(parts.iter().map(|p| (true, &p[..])));
		blobs.push((false, &node));
		if !check(&blobs, &encode(&[]), "final") {
			println!("the node's own FAILED");
			failed += 1;
		}
	}
	println!("{} ops for {} parts; {failed} failed", ops.len(), ops.iter().map(|o| o.0.len()).sum::<usize>());
	if failed > 0 {
		std::process::exit(1);
	}
}

/// The attest op for one node of a pack, trusting the nodes listed.
fn pack_args(dir: &str, list: &str, out: &str) {
	let p = pack::Pack::open(dir, false);
	let hashes: Vec<Hash> = std::fs::read_to_string(list).unwrap().lines().filter(|l| !l.is_empty()).map(hex).collect();
	let (node, closure) = hashes.split_first().expect("a node");
	let mut blobs: Vec<(bool, Vec<u8>)> = closure.iter().map(|h| (true, p.get(pack::NODE, h).expect("a trusted node"))).collect();
	blobs.push((false, p.get(pack::NODE, node).expect("the node")));
	let witness = match p.get(pack::PROOF, node) {
		Some(proof) => encode(&[proof]),
		None => encode(&[]),
	};
	let hashes: Vec<Hash> = blobs.iter().map(|(_, d)| blake2b256(d)).collect();
	let check_blobs: Vec<CheckBlob> = blobs.iter().zip(&hashes).map(|((t, d), h)| CheckBlob { trusted: *t, hash: *h, data: d }).collect();
	std::fs::write(out, check_args(CheckMode::Attest, &check_blobs, &[], &witness)).unwrap();
}

/// The check arguments of batch `n` of a mathlib_work.py layout in `work`: its subjects untrusted,
/// what it trusts (other batches' subjects, by claim entry) trusted, and its witness.
fn batch_args(work: &str, n: usize, out: &str) {
	let read = |f: String| std::fs::read_to_string(format!("{work}/{f}")).unwrap();
	let list = |s: String| s.split(',').filter(|p| !p.is_empty()).map(str::to_owned).collect::<Vec<_>>();
	let mut blobs: Vec<(bool, Vec<u8>)> = Vec::new();
	for r in list(read(format!("batch-{n}.trust"))) {
		let (claim, entry) = r.rsplit_once(':').expect("CLAIM:ENTRY");
		let m = claim.trim_start_matches("batch-").trim_end_matches(".claim");
		let subject = &list(read(format!("batch-{m}.subjects")))[entry.parse::<usize>().unwrap()];
		blobs.push((true, std::fs::read(format!("{work}/{subject}")).unwrap()));
	}
	// ONLY=K: subject K alone untrusted, the batch's other nodes trusted (for finding what fails).
	let only: Option<usize> = std::env::var("ONLY").ok().map(|k| k.parse().unwrap());
	let mut node = None;
	for (k, f) in list(read(format!("batch-{n}.subjects"))).into_iter().enumerate() {
		let d = std::fs::read(format!("{work}/{f}")).unwrap();
		match only {
			Some(o) if o == k => node = Some(blake2b256(&d)),
			Some(_) if !d.starts_with(nanoda_lib::nodes::NODE_MAGIC) => continue,
			_ => {},
		}
		blobs.push((only.is_some_and(|o| o != k), d));
	}
	let mut witness = std::fs::read(format!("{work}/batch-{n}.witness")).unwrap();
	if let Some(node) = node {
		let mine = |d: &&[u8]| d.starts_with(nanoda_lib::nodes::PROOF_MAGIC) && d[nanoda_lib::nodes::PROOF_MAGIC.len()..][..32] == node;
		let proofs: Vec<Vec<u8>> = lean_check::parse_witness(&witness).unwrap().into_iter().filter(mine).map(<[u8]>::to_vec).collect();
		witness = encode(&proofs);
	}
	let hashes: Vec<Hash> = blobs.iter().map(|(_, d)| blake2b256(d)).collect();
	let check_blobs: Vec<CheckBlob> = blobs.iter().zip(&hashes).map(|((t, d), h)| CheckBlob { trusted: *t, hash: *h, data: d }).collect();
	std::fs::write(out, check_args(CheckMode::Attest, &check_blobs, &[], &witness)).unwrap();
}

fn hex_of(h: &Hash) -> String {
	h.iter().map(|b| format!("{b:02x}")).collect()
}

/// The gas a unit of each kernel work counter costs (`nanoda_lib::util::work::NAMES`'s order: terms
/// looked up, terms newly built, names, levels, calls), fit by least squares to ops of nine heavy
/// declarations run in PolkaVM, with the planner's per-byte terms (`PlanConfig`).
const WORK_GAS: [f64; 5] = [4517.1, 0.0, 7212.8, 10170.2, 13182.3];

/// Trace every op of a judgment plan in the theorem's whole closure, loaded once, and write what
/// each op trusts, cites and carries (see the usage).
fn judgments_ops(full: &str, out: &str) {
	let verify = std::env::var_os("VERIFY").is_some();
	// VERIFY_MIN_GAS: verify only the ops planned at this much gas or more.
	let verify_min: f64 = std::env::var("VERIFY_MIN_GAS").map_or(0.0, |v| v.parse().expect("a number"));
	let bytes = std::fs::read(full).expect("arguments");
	let input = witness_check::Input::parse(&bytes).expect("well-formed arguments");
	let plan: Value = serde_json::from_slice(&std::fs::read(format!("{out}/plan.json")).unwrap()).unwrap();
	let closure: Vec<Vec<u8>> = input.blobs().filter(|b| b.trusted).map(|b| b.data.to_vec()).collect();
	// The check's pinned nodes in the closure, which every op trusts besides what it looks up:
	// nanoda takes its shortcuts (computing on literals, expanding a string) only with their names
	// loaded, and checks that they exist rather than looking anything up, so the trace misses
	// them; an op traced with them present reduces another way without them.
	let in_closure: std::collections::BTreeSet<Hash> = closure.iter().map(|d| blake2b256(d)).collect();
	let pinned: Vec<Hash> =
		lean_check::PINS.chunks(32).map(|c| <Hash>::try_from(c).unwrap()).filter(|h| in_closure.contains(h)).collect();
	let node = input.blobs().find(|b| !b.trusted && b.data.starts_with(nanoda_lib::nodes::NODE_MAGIC)).expect("a node").data.to_vec();
	// A theorem's proof; a definition's value is in its node.
	let proof: Option<Vec<u8>> = input
		.blobs()
		.map(|b| b.data.to_vec())
		.chain(lean_check::parse_witness(input.witness).unwrap().into_iter().map(<[u8]>::to_vec))
		.find(|d| d.starts_with(nanoda_lib::nodes::PROOF_MAGIC));
	let node_hash = blake2b256(&node);
	let statement_imports = import_hashes(&node[nanoda_lib::nodes::NODE_MAGIC.len()..]);
	let judgment = |b: u64| std::fs::read(format!("{out}/blob-{b}.judgment")).unwrap();
	let mine_of = |group: &Value| -> Vec<Vec<u8>> { group["blobs"].as_array().unwrap().iter().map(|b| judgment(b.as_u64().unwrap())).collect() };
	// The closure, loaded once each way: the theorem as its judgment ops load it (no proof), and as
	// its own attestation does.
	let load = |with_proof: bool| -> Vec<u8> {
		let mut blobs: Vec<(bool, &[u8])> = closure.iter().map(|d| (true, &d[..])).collect();
		blobs.push((false, &node[..]));
		if let (true, Some(proof)) = (with_proof, &proof) {
			blobs.push((false, &proof[..]));
		}
		let hashes: Vec<Hash> = blobs.iter().map(|(_, d)| blake2b256(d)).collect();
		let check_blobs: Vec<CheckBlob> = blobs.iter().zip(&hashes).map(|((t, d), h)| CheckBlob { trusted: *t, hash: *h, data: d }).collect();
		check_args(CheckMode::Attest, &check_blobs, &[], &encode(&[]))
	};
	let (ops_args, final_args) = (load(false), load(true));
	let ops_input = witness_check::Input::parse(&ops_args).unwrap();
	let final_input = witness_check::Input::parse(&final_args).unwrap();
	let ops_nodes = lean_check::load_attest(&ops_input).expect("nodes load");
	let final_nodes = lean_check::load_attest(&final_input).expect("nodes load");
	let i = ops_nodes.find(&node_hash).unwrap();
	let looked_up = |nodes: &nanoda_lib::nodes::Nodes, f: &dyn Fn()| -> std::collections::BTreeSet<Hash> {
		nanoda_lib::nodes::trace::start();
		f();
		let declars = nanoda_lib::nodes::trace::stop();
		nodes.nodes.iter().filter(|n| declars.iter().any(|d| n.declars.contains(d))).map(|n| n.hash).collect()
	};
	let groups = plan["groups"].as_array().unwrap();
	// A judgment as witness names it: the op attesting it, and its position among the op's subjects.
	let blob_ref = |b: u64| -> Value {
		let g = plan["blobs"][b as usize]["group"].as_u64().unwrap();
		let k = groups[g as usize]["blobs"].as_array().unwrap().iter().position(|x| x.as_u64() == Some(b)).unwrap();
		serde_json::json!([format!("group-{g}"), k])
	};
	let mut ops = Vec::new();
	let mut costs = serde_json::Map::new();
	let (start, mut failed) = (Instant::now(), 0);
	for (g, group) in groups.iter().enumerate() {
		let cites: Vec<u64> = group["cites"].as_array().unwrap().iter().map(|c| c.as_u64().unwrap()).collect();
		let cited: Vec<Vec<u8>> = cites.iter().map(|&c| judgment(c)).collect();
		let cited_refs: Vec<&[u8]> = cited.iter().map(Vec::as_slice).collect();
		let mine = mine_of(group);
		let mine_refs: Vec<&[u8]> = mine.iter().map(Vec::as_slice).collect();
		let calls = std::fs::read(format!("{out}/group-{g}.calls")).unwrap();
		let ok = std::cell::Cell::new(true);
		let mut keep = looked_up(&ops_nodes, &|| {
			if let Err(e) = ops_nodes.attest_judgments(i, &cited_refs, &calls, &mine_refs) {
				println!("group {g}: {e}");
				ok.set(false);
			}
		});
		if !ok.get() {
			failed += 1;
			println!("group {g} FAILED");
		}
		for j in &mine {
			keep.extend(nanoda_lib::judgment::header(j).unwrap().imports);
		}
		keep.extend(statement_imports.iter().copied());
		keep.extend(pinned.iter().copied());
		keep.remove(&node_hash);
		let witness = encode(&[node.clone(), calls]);
		std::fs::write(format!("{out}/group-{g}.witness"), &witness).unwrap();
		// The op as the layout runs it, checked natively and cold (parsed and rebuilt afresh, as in
		// PolkaVM): each unit's cost for the next plan is the kernel work its call did there,
		// seeding included, in gas (WORK_GAS) as the planner's nanoseconds.
		let by_hash: std::collections::HashMap<Hash, &[u8]> = closure.iter().map(|d| (blake2b256(d), &d[..])).collect();
		let mut blobs: Vec<(bool, &[u8])> = keep.iter().map(|h| (true, by_hash[h])).collect();
		blobs.extend(cited_refs.iter().map(|c| (true, *c)));
		blobs.extend(mine.iter().map(|j| (false, &j[..])));
		let hashes: Vec<Hash> = blobs.iter().map(|(_, d)| blake2b256(d)).collect();
		let check_blobs: Vec<CheckBlob> = blobs.iter().zip(&hashes).map(|((t, d), h)| CheckBlob { trusted: *t, hash: *h, data: d }).collect();
		let a = check_args(CheckMode::Attest, &check_blobs, &[], &witness);
		let input = witness_check::Input::parse(&a).unwrap();
		if !std::panic::catch_unwind(|| lean_check::check(&input)).unwrap_or(false) {
			println!("group {g} FAILED trimmed");
			failed += 1;
		}
		let work = nanoda_lib::judgment::CALL_WORK.lock().unwrap().clone();
		let gas_per_ns = nanoda_lib::plan::PlanConfig::default().gas_per_ns;
		let ns = |w: &[u64; 5]| (w.iter().zip(WORK_GAS).map(|(&n, g)| n as f64 * g).sum::<f64>() / gas_per_ns) as u64;
		for (unit, w) in group["unit_ns"].as_array().unwrap().iter().zip(work) {
			let cost = serde_json::json!({ "run": ns(&w.run), "seed": ns(&w.seed), "seeds": w.seeds });
			costs.insert(unit[0].as_u64().unwrap().to_string(), cost);
		}
		if verify && group["gas"].as_f64().unwrap_or(f64::INFINITY) >= verify_min {
			std::fs::write(format!("{out}/group-{g}.args"), &a).unwrap();
		}
		ops.push(serde_json::json!({
			"name": format!("group-{g}"),
			"subjects": group["blobs"].as_array().unwrap().iter().map(|b| format!("blob-{b}.judgment")).collect::<Vec<_>>(),
			"witness": format!("group-{g}.witness"),
			"trust_nodes": keep.iter().map(hex_of).collect::<Vec<_>>(),
			"trust_ops": cites.iter().map(|&c| blob_ref(c)).collect::<Vec<_>>(),
		}));
	}
	let final_cites: Vec<u64> = plan["final_cites"].as_array().unwrap().iter().map(|c| c.as_u64().unwrap()).collect();
	let cited: Vec<Vec<u8>> = final_cites.iter().map(|&c| judgment(c)).collect();
	let cited_refs: Vec<&[u8]> = cited.iter().map(Vec::as_slice).collect();
	let fi = final_nodes.find(&node_hash).unwrap();
	let ok = std::cell::Cell::new(true);
	let mut keep = looked_up(&final_nodes, &|| {
		if final_nodes.check_with(fi, &cited_refs).is_err() {
			ok.set(false);
		}
	});
	keep.extend(statement_imports.iter().copied());
	keep.extend(pinned.iter().copied());
	if let Some(proof) = &proof {
		keep.extend(import_hashes(&proof[nanoda_lib::nodes::PROOF_MAGIC.len() + 32..]));
	}
	keep.remove(&node_hash);
	let summary = serde_json::json!({
		"node": hex_of(&node_hash),
		"ops": ops,
		"final": {
			"trust_nodes": keep.iter().map(hex_of).collect::<Vec<_>>(),
			"trust_ops": final_cites.iter().map(|&c| blob_ref(c)).collect::<Vec<_>>(),
		},
	});
	std::fs::write(format!("{out}/ops.json"), serde_json::to_vec(&summary).unwrap()).unwrap();
	std::fs::write(format!("{out}/costs.json"), serde_json::to_vec(&costs).unwrap()).unwrap();
	println!("{} ops traced in {:?}, {failed} failed; the theorem's own: {}", groups.len(), start.elapsed(), ok.get());
	if failed > 0 || !ok.get() {
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
		["reveal", dir, ref goals @ ..] if !goals.is_empty() => reveal(&Dir::open(dir), goals),
		["run", args] => {
			let args = std::fs::read(args).expect("arguments");
			let input = witness_check::Input::parse(&args).expect("well-formed arguments");
			let start = Instant::now();
			nanoda_lib::util::work::reset();
			let ok = std::panic::catch_unwind(|| lean_check::check(&input)).unwrap_or(false);
			println!("{ok} in {:?}", start.elapsed());
			// WORK_COUNTS: the kernel work the check did, as JSON.
			if std::env::var_os("WORK_COUNTS").is_some() {
				let counts = nanoda_lib::util::work::read();
				let calls = nanoda_lib::judgment::CALL_WORK.lock().unwrap().clone();
				let mut pairs: serde_json::Map<String, Value> =
					nanoda_lib::util::work::NAMES.iter().zip(counts).map(|(k, v)| (k.to_string(), Value::from(v))).collect();
				for (k, name) in nanoda_lib::util::work::NAMES.iter().enumerate() {
					pairs.insert(format!("in_{name}"), Value::from(calls.iter().map(|w| w.seed[k] + w.run[k]).sum::<u64>()));
				}
				println!("{}", Value::Object(pairs));
			}
		},
		["declarations-args", args, positions, out] => declarations_args(args, positions, out),
		["judgments", args, out] => judgments(args, out, 25.0, None),
		["judgments", args, out, ms] => judgments(args, out, ms.parse().expect("milliseconds"), None),
		["judgments", args, out, ms, costs] => judgments(args, out, ms.parse().expect("milliseconds"), Some(costs)),
		["judgments-check", full, out] => judgments_check(full, out),
		["judgments-ops", full, out] => judgments_ops(full, out),
		["pack-args", dir, list, out] => pack_args(dir, list, out),
		["batch-args", work, n, out] => batch_args(work, n.parse().expect("batch number"), out),
		["split-inductive", args, out] => split_inductive(args, out, Duration::from_millis(40)),
		["split-inductive", args, out, ms] => split_inductive(args, out, Duration::from_millis(ms.parse().expect("milliseconds"))),
		["args", dir, p, n, out] => write_args(&Dir::open(dir), p, n.parse().expect("batch number"), out),
		["trace", dir, p, out] => trace(&Dir::open(dir), p, out, Duration::from_millis(100)),
		["trace", dir, p, out, ms] => trace(&Dir::open(dir), p, out, Duration::from_millis(ms.parse().expect("milliseconds"))),
		_ => {
			eprintln!("usage: lean-host convert EXPORT OUT | lean-host nodes DIR | lean-host plan DIR PLAN | lean-host trace DIR PLAN OUT [MS]");
			std::process::exit(2);
		},
	}
}
