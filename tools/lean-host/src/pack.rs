//! Pack storage for a lean_nodes.py output directory: nodes and proofs appended to `nodes.pack`
//! and `proofs.pack`, found through `pack.idx`, instead of a file each. All of Mathlib is over a
//! million nodes and proofs, most smaller than a disk block, so as files it takes several times
//! its size on disk.
//!
//! `pack.idx` is a list of 45-byte records: kind (0 node, 1 proof), the 32-byte hash, then the
//! offset (u64) and length (u32) in that kind's pack, little-endian. A record past the end of its
//! pack (from an interrupted write) is ignored.

use std::collections::HashMap;
use std::fs::{File, OpenOptions};
use std::io::{BufWriter, Read, Write};
use std::os::unix::fs::FileExt;

pub type Hash = [u8; 32];
pub const NODE: u8 = 0;
pub const PROOF: u8 = 1;
const FILES: [&str; 2] = ["nodes.pack", "proofs.pack"];

pub struct Pack {
	index: HashMap<(u8, Hash), (u64, u32)>,
	readers: [File; 2],
	writers: Option<([BufWriter<File>; 2], BufWriter<File>)>,
	lens: [u64; 2],
	/// Record hashes only, writing no bytes (for comparing exports by hash, where disk is short).
	pub no_data: bool,
}

pub fn exists(dir: &str) -> bool {
	std::path::Path::new(&format!("{dir}/pack.idx")).exists()
}

impl Pack {
	/// Open `dir`'s pack, creating it if `write`.
	pub fn open(dir: &str, write: bool) -> Pack {
		let open = |name: &str| {
			OpenOptions::new().read(true).append(write).create(write).open(format!("{dir}/{name}")).unwrap_or_else(|e| panic!("{dir}/{name}: {e}"))
		};
		let readers = [open(FILES[0]), open(FILES[1])];
		let lens = [readers[0].metadata().unwrap().len(), readers[1].metadata().unwrap().len()];
		let mut idx = Vec::new();
		open("pack.idx").read_to_end(&mut idx).unwrap();
		let mut index = HashMap::new();
		for r in idx.chunks_exact(45) {
			let kind = r[0];
			let h: Hash = r[1..33].try_into().unwrap();
			let off = u64::from_le_bytes(r[33..41].try_into().unwrap());
			let len = u32::from_le_bytes(r[41..45].try_into().unwrap());
			if (kind as usize) < 2 && off + len as u64 <= lens[kind as usize] {
				index.insert((kind, h), (off, len));
			}
		}
		let writers = write.then(|| {
			let w = |name: &str| BufWriter::with_capacity(1 << 20, open(name));
			([w(FILES[0]), w(FILES[1])], w("pack.idx"))
		});
		Pack { index, readers, writers, lens, no_data: false }
	}

	pub fn contains(&self, kind: u8, h: &Hash) -> bool {
		self.index.contains_key(&(kind, *h))
	}

	pub fn get(&self, kind: u8, h: &Hash) -> Option<Vec<u8>> {
		let &(off, len) = self.index.get(&(kind, *h))?;
		let mut buf = vec![0; len as usize];
		self.readers[kind as usize].read_exact_at(&mut buf, off).expect("pack read");
		Some(buf)
	}

	/// Add `data` under `h`, unless it's there already (content-addressed, so it's the same).
	pub fn put(&mut self, kind: u8, h: &Hash, data: &[u8]) {
		if self.contains(kind, h) {
			return;
		}
		let (files, idx) = self.writers.as_mut().expect("pack opened for writing");
		let off = self.lens[kind as usize];
		let data = if self.no_data { &[][..] } else { data };
		files[kind as usize].write_all(data).unwrap();
		self.lens[kind as usize] += data.len() as u64;
		let mut r = Vec::with_capacity(45);
		r.push(kind);
		r.extend_from_slice(h);
		r.extend_from_slice(&off.to_le_bytes());
		r.extend_from_slice(&(data.len() as u32).to_le_bytes());
		idx.write_all(&r).unwrap();
		self.index.insert((kind, *h), (off, data.len() as u32));
	}

	pub fn flush(&mut self) {
		if let Some((files, idx)) = self.writers.as_mut() {
			// Data before the index, so a record never points past what's written.
			files.iter_mut().for_each(|f| f.flush().unwrap());
			idx.flush().unwrap();
		}
	}
}

impl Drop for Pack {
	fn drop(&mut self) {
		self.flush();
	}
}

fn unhex(s: &str) -> Option<Hash> {
	if s.len() != 64 {
		return None;
	}
	let mut h = [0; 32];
	for i in 0..32 {
		h[i] = u8::from_str_radix(&s[2 * i..2 * i + 2], 16).ok()?;
	}
	Some(h)
}

/// Move `dir`'s node and proof files into its pack, deleting each file once it's packed.
pub fn pack_dir(dir: &str) {
	let mut pack = Pack::open(dir, true);
	let mut moved = 0usize;
	let mut done = Vec::new();
	// The files go only once what they held is on disk.
	let flush = |pack: &mut Pack, done: &mut Vec<std::path::PathBuf>| {
		pack.flush();
		done.drain(..).for_each(|p| std::fs::remove_file(p).unwrap());
	};
	for (kind, sub) in [(NODE, "nodes"), (PROOF, "proofs")] {
		let Ok(entries) = std::fs::read_dir(format!("{dir}/{sub}")) else { continue };
		for entry in entries {
			let entry = entry.unwrap();
			let Some(h) = entry.file_name().to_str().and_then(unhex) else { continue };
			pack.put(kind, &h, &std::fs::read(entry.path()).unwrap());
			done.push(entry.path());
			moved += 1;
			if done.len() == 10000 {
				flush(&mut pack, &mut done);
			}
		}
	}
	flush(&mut pack, &mut done);
	eprintln!("packed {moved} files");
}
