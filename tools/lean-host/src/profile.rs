//! `lean-host profile DIR OUT`: check every node of a pack directory (see pack.rs) once, in one
//! environment, and record for each how long its check took and which nodes the kernel looked up
//! while checking it. Planning all of Mathlib the way `trace` does (one environment per batch, from
//! each batch's full closure) doesn't scale; from this, `plan_profile.py` plans it directly: a
//! batch must trust what its subjects looked up, and what they and their proofs import.
//!
//! DIR's manifest is `manifest.jsonl` (one entry a line, as the chunked Mathlib export writes it).
//! OUT gets, for each node in manifest order: u32 check microseconds (u32::MAX if the check
//! failed, u32::MAX - 1 if it was left out for depending on an unpermitted axiom: see OUT.excluded), u32 count, then that many u32 manifest positions of the nodes looked up. OUT.index:
//! each node's u32 position list for its imports and its proof's, in the same form, so the planner
//! needn't parse the manifest's hex again. OUT.order: the u32 positions in an order where every
//! node comes after what it and its proof import.

use crate::pack::{self, Pack};
use nanoda_lib::nodes::{Hash, NodeLoader, PINNED_NAMES};
use std::collections::HashMap;
use std::io::{BufRead, BufWriter, Write};
use std::time::Instant;

fn unhex(s: &str) -> Hash {
	std::array::from_fn(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap())
}

struct Entry {
	hash: Hash,
	name: String,
	kind: String,
	imports: Vec<u32>,
	proof_imports: Vec<u32>,
	no_proof: bool,
}

fn write_list(w: &mut impl Write, xs: &[u32]) {
	w.write_all(&(xs.len() as u32).to_le_bytes()).unwrap();
	for x in xs {
		w.write_all(&x.to_le_bytes()).unwrap();
	}
}

pub fn profile(dir: &str, out: &str) {
	let start = Instant::now();
	let mut position: HashMap<Hash, u32> = HashMap::new();
	let mut entries: Vec<Entry> = Vec::new();
	let mut pins = Vec::new();
	let f = std::io::BufReader::with_capacity(1 << 20, std::fs::File::open(format!("{dir}/manifest.jsonl")).expect("manifest.jsonl"));
	for line in f.lines() {
		let e: serde_json::Value = serde_json::from_str(&line.unwrap()).unwrap();
		let hash = unhex(e["hash"].as_str().unwrap());
		let list = |k: &str| -> Vec<u32> {
			e.get(k).and_then(|v| v.as_array()).into_iter().flatten().map(|h| position[&unhex(h.as_str().unwrap())]).collect()
		};
		let names = e["names"].as_array().unwrap();
		if names.iter().any(|n| PINNED_NAMES.contains(&n.as_str().unwrap())) {
			pins.push(hash);
		}
		let entry = Entry { hash, name: names[0].as_str().unwrap().to_string(), kind: e["kind"].as_str().unwrap().to_string(), imports: list("imports"), proof_imports: list("proof_imports"), no_proof: false };
		position.insert(hash, entries.len() as u32);
		entries.push(entry);
	}
	eprintln!("{} manifest entries read in {:?}", entries.len(), start.elapsed());

	// A proof's imports, from the proof itself: a theorem Lean generates on demand (an `eq_def`,
	// say) can get a different proof in another environment, so a pack built from several exports
	// can hold a proof that isn't the one its manifest entry describes (3 of all Mathlib's).
	let pack = Pack::open(dir, false);
	for e in entries.iter_mut() {
		if let Some(p) = pack.get(pack::PROOF, &e.hash) {
			let (mut n, mut shift, mut at) = (0usize, 0, 40);
			loop {
				let b = p[at];
				at += 1;
				n |= ((b & 0x7f) as usize) << shift;
				shift += 7;
				if b < 0x80 {
					break;
				}
			}
			let imports: Option<Vec<u32>> =
				(0..n).map(|k| position.get(&<Hash>::try_from(&p[at + 32 * k..at + 32 * k + 32]).unwrap()).copied()).collect();
			match imports {
				Some(i) => e.proof_imports = i,
				// It imports a node the manifest hasn't got (from that other environment): check
				// the statement without it.
				None => {
					eprintln!("proof unusable (imports an unlisted node): {}", e.name);
					e.proof_imports.clear();
					e.no_proof = true;
				},
			}
		}
	}
	// Load in an order where everything a node or its proof imports comes first: the manifest's,
	// except where a proof (as above) needs otherwise.
	let mut order = Vec::with_capacity(entries.len());
	let mut state = vec![0u8; entries.len()]; // 0 new, 1 on the stack, 2 placed
	for root in 0..entries.len() {
		let mut stack = vec![(root as u32, false)];
		while let Some((i, done)) = stack.pop() {
			let iu = i as usize;
			if done {
				state[iu] = 2;
				order.push(i);
				continue;
			}
			if state[iu] != 0 {
				continue;
			}
			state[iu] = 1;
			stack.push((i, true));
			for &d in entries[iu].imports.iter().chain(&entries[iu].proof_imports).rev() {
				assert!(state[d as usize] != 1, "import cycle at {}", entries[iu].name);
				if state[d as usize] == 0 {
					stack.push((d, false));
				}
			}
		}
	}
	// Leave out what depends on an axiom the kernel doesn't permit (Mathlib's export has sorryAx,
	// which a few declarations mention): such a node can't load, nor anything importing it; a
	// theorem whose proof alone imports one keeps its statement, unproven.
	let mut excluded = vec![false; entries.len()];
	let mut lost_proofs = 0;
	for &i in &order {
		let e = &entries[i as usize];
		let axiom = e.kind == "axiom" && !nanoda_lib::nodes::PERMITTED_AXIOMS.contains(&e.name.as_str());
		excluded[i as usize] = axiom || e.imports.iter().any(|&d| excluded[d as usize]);
		if !excluded[i as usize] && e.proof_imports.iter().any(|&d| excluded[d as usize]) {
			lost_proofs += 1;
			let e = &mut entries[i as usize];
			e.proof_imports.clear();
			e.no_proof = true;
		}
	}
	let mut ex = BufWriter::new(std::fs::File::create(format!("{out}.excluded")).unwrap());
	for (i, e) in entries.iter().enumerate() {
		if excluded[i] {
			writeln!(ex, "excluded\t{}", e.name).unwrap();
		} else if e.no_proof {
			writeln!(ex, "unproven\t{}", e.name).unwrap();
		}
	}
	ex.flush().unwrap();
	eprintln!("{} nodes excluded (an unpermitted axiom), {lost_proofs} proofs dropped for one", excluded.iter().filter(|&&x| x).count());

	let mut ow = BufWriter::new(std::fs::File::create(format!("{out}.order")).unwrap());
	for i in &order {
		ow.write_all(&i.to_le_bytes()).unwrap();
	}
	ow.flush().unwrap();

	let mut index = BufWriter::new(std::fs::File::create(format!("{out}.index")).unwrap());
	for e in &entries {
		write_list(&mut index, &e.imports);
		write_list(&mut index, &e.proof_imports);
	}
	index.flush().unwrap();

	let mut loader = NodeLoader::new(&pins);
	let order: Vec<u32> = order.into_iter().filter(|&i| !excluded[i as usize]).collect();
	for (i, e) in order.iter().map(|&i| &entries[i as usize]).enumerate() {
		let node = pack.get(pack::NODE, &e.hash).expect("node in pack");
		let proof = if e.no_proof { None } else { pack.get(pack::PROOF, &e.hash) };
		if let Err(err) = loader.add(e.hash, &node, proof.as_deref(), false) {
			panic!("{}: {err}", e.name);
		}
		if i % 100000 == 0 {
			eprintln!("loaded {i} in {:?}", start.elapsed());
		}
	}
	let nodes = loader.finish().expect("nodes load");
	eprintln!("all loaded in {:?}", start.elapsed());
	// Declaration index -> manifest position (the loader has the nodes in `order`).
	let mut declar_node = vec![0u32; nodes.nodes.iter().map(|n| n.declars.end).max().unwrap_or(0)];
	let mut loaded_at = vec![usize::MAX; entries.len()];
	for (k, n) in nodes.nodes.iter().enumerate() {
		let i = order[k];
		assert_eq!(n.hash, entries[i as usize].hash, "the loader keeps the load order");
		loaded_at[i as usize] = k;
		for d in n.declars.clone() {
			declar_node[d] = i;
		}
	}

	let mut w = BufWriter::new(std::fs::File::create(out).unwrap());
	let (mut failed, mut total_us) = (0usize, 0u64);
	for i in 0..entries.len() {
		if excluded[i] {
			w.write_all(&(u32::MAX - 1).to_le_bytes()).unwrap();
			write_list(&mut w, &[]);
			continue;
		}
		nanoda_lib::nodes::trace::start();
		let t = Instant::now();
		let ok = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| nodes.check(loaded_at[i]))).is_ok();
		let us = t.elapsed().as_micros().min(u32::MAX as u128 - 1) as u32;
		let looked_up = nanoda_lib::nodes::trace::stop();
		let mut touched: Vec<u32> = looked_up.into_iter().map(|d| declar_node[d]).filter(|&n| n != i as u32).collect();
		touched.sort();
		touched.dedup();
		if !ok {
			failed += 1;
			eprintln!("check failed: {}", entries[i].name);
		}
		total_us += us as u64;
		w.write_all(&(if ok { us } else { u32::MAX }).to_le_bytes()).unwrap();
		write_list(&mut w, &touched);
		if i % 100000 == 0 {
			eprintln!("checked {i} in {:?}", start.elapsed());
		}
	}
	w.flush().unwrap();
	eprintln!("{} nodes checked, {failed} failed, {:.1} s of checking, {:?} in all", nodes.nodes.len(), total_us as f64 / 1e6, start.elapsed());
}
