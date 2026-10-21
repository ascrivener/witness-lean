//! Runs the Lean check natively, as refine would, and reports how long it took.
//!
//!     lean-host attest LAYER... SUBJECT
//!     lean-host reveal STATEMENT THEOREM TRUSTED LAYER... DELTA
//!
//! `attest` checks SUBJECT after the trusted LAYERs. `reveal` checks DELTA against the LAYERs, the
//! first TRUSTED of them trusted. Prints `true` or `false` and the time; exits 1 on false.

use std::time::Instant;
use witness_types::{CheckBlob, CheckMode, check_args};

fn main() {
	let args: Vec<String> = std::env::args().skip(1).collect();
	let read = |p: &String| std::fs::read(p).unwrap_or_else(|e| panic!("cannot read {p}: {e}"));
	let (mode, blobs, params, witness) = match args.iter().map(String::as_str).collect::<Vec<_>>()[..] {
		["attest", ref files @ .., _] if !files.is_empty() || args.len() == 2 => {
			let data: Vec<Vec<u8>> = args[1..].iter().map(read).collect();
			let n = data.len();
			let blobs = data.into_iter().enumerate().map(|(i, d)| (i + 1 < n, d)).collect();
			(CheckMode::Attest, blobs, Vec::new(), Vec::new())
		},
		["reveal", statement, theorem, trusted, .., _] => {
			let trusted: usize = trusted.parse().expect("TRUSTED is a number");
			let files = &args[4..args.len() - 1];
			let blobs = files.iter().enumerate().map(|(i, f)| (i < trusted, read(f))).collect();
			let params = format!("{statement}\n{theorem}").into_bytes();
			(CheckMode::Reveal, blobs, params, read(args.last().unwrap()))
		},
		_ => {
			eprintln!("usage: lean-host attest LAYER... SUBJECT | lean-host reveal STATEMENT THEOREM TRUSTED LAYER... DELTA");
			std::process::exit(2);
		},
	};
	let blobs: Vec<(bool, Vec<u8>)> = blobs;
	let check_blobs: Vec<CheckBlob> =
		blobs.iter().map(|(trusted, data)| CheckBlob { trusted: *trusted, hash: [0; 32], data }).collect();
	let args = check_args(mode, &check_blobs, &params, &witness);
	let input = witness_check::Input::parse(&args).expect("well-formed arguments");
	let start = Instant::now();
	// Type errors panic, which counts as false, as on the PVM.
	std::panic::set_hook(Box::new(|info| eprintln!("check panicked: {info}")));
	let ok = std::panic::catch_unwind(|| lean_check::check(&input)).unwrap_or(false);
	println!("{ok} in {:?} ({} bytes of blobs, {} of witness)", start.elapsed(),
		blobs.iter().map(|(_, d)| d.len()).sum::<usize>(), witness.len());
	std::process::exit(if ok { 0 } else { 1 });
}
