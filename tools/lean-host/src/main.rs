//! Runs the Lean check natively, as refine would, and reports how long it takes.
//!
//!     lean-host nodes DIR          load and check every node of DIR, in order, with its proof
//!     lean-host plan DIR PLAN      attest each batch of PLAN (from lean_plan.py), timing each
//!
//! DIR is a `lean_nodes.py` output directory. A native millisecond costs about 29M gas in
//! PolkaJam v0.1.29's recompiler, so a batch should stay well under 150 ms to fit a refine.

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
}

impl Dir {
	fn open(path: &str) -> Dir {
		let manifest = serde_json::from_slice(&std::fs::read(format!("{path}/manifest.json")).expect("manifest"));
		Dir { path: path.to_string(), manifest: manifest.expect("JSON") }
	}
	fn node(&self, h: &str) -> Vec<u8> {
		std::fs::read(format!("{}/nodes/{h}", self.path)).unwrap()
	}
	fn proof(&self, h: &str) -> Option<Vec<u8>> {
		std::fs::read(format!("{}/proofs/{h}", self.path)).ok()
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
		if let Err(err) = loader.add(hex(h), &dir.node(h), dir.proof(h).as_deref()) {
			eprintln!("{}: {err}", e["names"][0]);
			std::process::exit(1);
		}
	}
	let nodes = loader.finish();
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

fn main() {
	// Type errors panic, which counts as false, as on the PVM.
	std::panic::set_hook(Box::new(|info| eprintln!("check panicked: {info}")));
	let args: Vec<String> = std::env::args().skip(1).collect();
	match args.iter().map(String::as_str).collect::<Vec<_>>()[..] {
		["nodes", dir] => nodes(&Dir::open(dir)),
		["plan", dir, p] => plan(&Dir::open(dir), p),
		_ => {
			eprintln!("usage: lean-host nodes DIR | lean-host plan DIR PLAN");
			std::process::exit(2);
		},
	}
}
