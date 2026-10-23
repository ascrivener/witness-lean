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
//!                                  `over T: NAME` for each declaration that alone takes longer
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
	/// The nodes declaring the names the kernel treats specially.
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
	let pins: Vec<u8> = dir.pins().concat();
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
		let (ok, t) = run(CheckMode::Attest, &blobs, &pins, &witness);
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
			out_plan.push(serde_json::json!({ "goal": goal, "trusted": keep }));
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
			out_plan.push(serde_json::json!({ "depth": batch["depth"], "subjects": subjects, "trusted": keep }));
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
		let (ok, t) = run(CheckMode::Attest, &blobs, &self.pins.concat(), &encode(&proofs));
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
	std::fs::write(out, check_args(CheckMode::Attest, &check_blobs, &dir.pins().concat(), &encode(&proofs))).unwrap();
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
		["args", dir, p, n, out] => write_args(&Dir::open(dir), p, n.parse().expect("batch number"), out),
		["trace", dir, p, out] => trace(&Dir::open(dir), p, out, Duration::from_millis(100)),
		["trace", dir, p, out, ms] => trace(&Dir::open(dir), p, out, Duration::from_millis(ms.parse().expect("milliseconds"))),
		_ => {
			eprintln!("usage: lean-host convert EXPORT OUT | lean-host nodes DIR | lean-host plan DIR PLAN | lean-host trace DIR PLAN OUT [MS]");
			std::process::exit(2);
		},
	}
}
