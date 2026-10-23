//! `lean-host convert`: lean_nodes.py in Rust, for exports too big for it (all of Mathlib is about
//! 17 times FTA's closure, which already takes lean_nodes.py 4 GB). It reads the export a line at a
//! time, keeps names, levels and expressions in compact tables, and writes each declaration's node
//! as soon as its line arrives. It writes exactly the bytes lean_nodes.py writes: see that file and
//! node_format.md for what they mean.

use serde_json::Value;
use std::collections::{HashMap, HashSet};
use std::io::{BufRead, Write};

const NODE_MAGIC: &[u8] = b"LEANNOD\x01";
const PROOF_MAGIC: &[u8] = b"LEANPRF\x01";
const TAG_STATEMENT: u8 = 23;
const TAG_PROOF: u8 = 24;

type Hash = [u8; 32];

enum NamePart {
	Str(Box<str>),
	Num(u64),
}

enum Level {
	Zero,
	Succ(u32),
	Max(u32, u32),
	IMax(u32, u32),
	Param(u32),
}

enum Expr {
	BVar(u64),
	Sort(u32),
	Const(u32, Box<[u32]>),
	App(u32, u32),
	Lam(u32, u32),
	Pi(u32, u32),
	Let(u32, u32, u32),
	Nat(Box<[u8]>),
	Str(Box<str>),
	Proj(u32, u64, u32),
}

/// The export's tables, by export index.
struct Export {
	names: Vec<(u32, NamePart)>,
	levels: Vec<Level>,
	exprs: Vec<Expr>,
	/// The level of each universe parameter, by its name (the last one exported, as in Python).
	param_levels: HashMap<u32, u32>,
}

fn u(v: &Value) -> u64 {
	v.as_u64().unwrap_or_else(|| panic!("expected a number, got {v}"))
}
fn u32_(v: &Value) -> u32 {
	u32::try_from(u(v)).expect("index fits u32")
}
fn u32s(v: &Value) -> Vec<u32> {
	v.as_array().expect("array").iter().map(u32_).collect()
}

/// A decimal string's value as minimal little-endian bytes (empty for 0).
fn nat_bytes(s: &str) -> Box<[u8]> {
	let mut digits: Vec<u8> = s.bytes().map(|b| b - b'0').collect();
	let mut out = Vec::new();
	while digits.iter().any(|&d| d != 0) {
		let mut rem = 0u32;
		for d in digits.iter_mut() {
			let cur = rem * 10 + *d as u32;
			*d = (cur / 256) as u8;
			rem = cur % 256;
		}
		out.push(rem as u8);
		while digits.first() == Some(&0) {
			digits.remove(0);
		}
	}
	out.into_boxed_slice()
}

impl Export {
	fn new() -> Export {
		Export { names: vec![(0, NamePart::Num(0))], levels: vec![Level::Zero], exprs: Vec::new(), param_levels: HashMap::new() }
	}

	fn name_str(&self, i: u32) -> String {
		if i == 0 {
			return String::new();
		}
		let (pre, part) = &self.names[i as usize];
		let pre = self.name_str(*pre);
		let last = match part {
			NamePart::Str(s) => s.to_string(),
			NamePart::Num(n) => n.to_string(),
		};
		if pre.is_empty() { last } else { format!("{pre}.{last}") }
	}

	/// Add a name, level or expression line; false if `line` is none of those.
	fn add(&mut self, line: &serde_json::Map<String, Value>) -> bool {
		let check = |i: &Value, len: usize, kind: &str| {
			assert_eq!(u(i) as usize, len, "{kind} indices must be consecutive");
		};
		if let Some(i) = line.get("in") {
			check(i, self.names.len(), "name");
			let item = if let Some(s) = line.get("str") {
				(u32_(&s["pre"]), NamePart::Str(s["str"].as_str().expect("string").into()))
			} else {
				let n = &line["num"];
				(u32_(&n["pre"]), NamePart::Num(u(&n["i"])))
			};
			self.names.push(item);
		} else if let Some(i) = line.get("il") {
			check(i, self.levels.len(), "level");
			let idx = self.levels.len() as u32;
			let l = if let Some(v) = line.get("succ") {
				Level::Succ(u32_(v))
			} else if let Some(v) = line.get("max") {
				Level::Max(u32_(&v[0]), u32_(&v[1]))
			} else if let Some(v) = line.get("imax") {
				Level::IMax(u32_(&v[0]), u32_(&v[1]))
			} else if let Some(v) = line.get("param") {
				self.param_levels.insert(u32_(v), idx);
				Level::Param(u32_(v))
			} else {
				panic!("unknown level {line:?}")
			};
			self.levels.push(l);
		} else if let Some(i) = line.get("ie") {
			check(i, self.exprs.len(), "expression");
			let e = if let Some(v) = line.get("bvar") {
				Expr::BVar(u(v))
			} else if let Some(v) = line.get("sort") {
				Expr::Sort(u32_(v))
			} else if let Some(v) = line.get("const") {
				Expr::Const(u32_(&v["name"]), u32s(&v["us"]).into_boxed_slice())
			} else if let Some(v) = line.get("app") {
				Expr::App(u32_(&v["fn"]), u32_(&v["arg"]))
			} else if let Some(v) = line.get("lam") {
				Expr::Lam(u32_(&v["type"]), u32_(&v["body"]))
			} else if let Some(v) = line.get("forallE") {
				Expr::Pi(u32_(&v["type"]), u32_(&v["body"]))
			} else if let Some(v) = line.get("letE") {
				Expr::Let(u32_(&v["type"]), u32_(&v["value"]), u32_(&v["body"]))
			} else if let Some(v) = line.get("natVal") {
				Expr::Nat(nat_bytes(v.as_str().expect("decimal string")))
			} else if let Some(v) = line.get("strVal") {
				Expr::Str(v.as_str().expect("string").into())
			} else if let Some(v) = line.get("proj") {
				Expr::Proj(u32_(&v["typeName"]), u(&v["idx"]), u32_(&v["struct"]))
			} else {
				panic!("unknown expression {:?}", line.keys().collect::<Vec<_>>())
			};
			self.exprs.push(e);
		} else {
			return false;
		}
		true
	}
}

/// Export indices in the order they were added, and each one's position.
#[derive(Default)]
struct Ordered {
	order: Vec<u32>,
	pos: HashMap<u32, u32>,
}

impl Ordered {
	fn contains(&self, i: u32) -> bool {
		self.pos.contains_key(&i)
	}
	fn insert(&mut self, i: u32) {
		if !self.contains(i) {
			self.pos.insert(i, self.order.len() as u32);
			self.order.push(i);
		}
	}
}

/// lean_nodes.py's Closure, step for step: the tables' order is the bytes' order.
struct Closure<'e> {
	ex: &'e Export,
	names: Ordered,
	levels: Ordered,
	exprs: Ordered,
	consts: HashSet<u32>,
}

impl<'e> Closure<'e> {
	fn new(ex: &'e Export) -> Self {
		Closure { ex, names: Ordered::default(), levels: Ordered::default(), exprs: Ordered::default(), consts: HashSet::new() }
	}

	fn name(&mut self, mut i: u32) {
		let mut chain = Vec::new();
		while i != 0 && !self.names.contains(i) {
			chain.push(i);
			i = self.ex.names[i as usize].0;
		}
		for i in chain.into_iter().rev() {
			self.names.insert(i);
		}
	}

	fn level(&mut self, i: u32) {
		let mut stack = vec![(i, false)];
		while let Some((i, done)) = stack.pop() {
			if i == 0 || self.levels.contains(i) {
				continue;
			}
			if done {
				self.levels.insert(i);
				continue;
			}
			stack.push((i, true));
			match self.ex.levels[i as usize] {
				Level::Succ(v) => stack.push((v, false)),
				Level::Max(a, b) | Level::IMax(a, b) => stack.extend([(b, false), (a, false)]),
				Level::Param(n) => self.name(n),
				Level::Zero => panic!("zero level at index {i}"),
			}
		}
	}

	fn expr(&mut self, i: u32) {
		let mut stack = vec![(i, false)];
		while let Some((i, done)) = stack.pop() {
			if self.exprs.contains(i) {
				continue;
			}
			if done {
				self.exprs.insert(i);
				continue;
			}
			stack.push((i, true));
			match &self.ex.exprs[i as usize] {
				Expr::BVar(_) | Expr::Nat(_) | Expr::Str(_) => {},
				Expr::Sort(l) => self.level(*l),
				Expr::Const(n, us) => {
					self.name(*n);
					self.consts.insert(*n);
					for &l in us.iter() {
						self.level(l);
					}
				},
				Expr::App(f, a) => stack.extend([(*a, false), (*f, false)]),
				Expr::Lam(t, b) | Expr::Pi(t, b) => stack.extend([(*b, false), (*t, false)]),
				Expr::Let(t, v, b) => stack.extend([(*b, false), (*v, false), (*t, false)]),
				Expr::Proj(n, _, s) => {
					self.name(*n);
					self.consts.insert(*n);
					stack.push((*s, false));
				},
			}
		}
	}

	fn param_level(&self, name: u32) -> u32 {
		*self.ex.param_levels.get(&name).unwrap_or_else(|| panic!("no level for universe parameter {}", self.ex.name_str(name)))
	}

	fn info(&mut self, d: &Info) {
		self.name(d.name);
		for &p in &d.lps {
			self.name(p);
			self.level(self.param_level(p));
		}
		self.expr(d.ty);
	}

	// Local indices: names and levels from 1 (0 is anonymous, zero), expressions from 0.
	fn n(&self, i: u32) -> u64 {
		if i == 0 { 0 } else { self.names.pos[&i] as u64 + 1 }
	}
	fn l(&self, i: u32) -> u64 {
		if i == 0 { 0 } else { self.levels.pos[&i] as u64 + 1 }
	}
	fn e(&self, i: u32) -> u64 {
		self.exprs.pos[&i] as u64
	}

	/// The tables' items, binders anonymous and default (as lean_nodes.py's remap).
	fn items(&self, w: &mut Writer) {
		for &i in &self.names.order {
			let (pre, part) = &self.ex.names[i as usize];
			match part {
				NamePart::Str(s) => {
					w.byte(1);
					w.uvar(self.n(*pre));
					w.string(s);
				},
				NamePart::Num(k) => {
					w.byte(2);
					w.uvar(self.n(*pre));
					w.uvar(*k);
				},
			}
		}
		for &i in &self.levels.order {
			match self.ex.levels[i as usize] {
				Level::Succ(v) => {
					w.byte(3);
					w.uvar(self.l(v));
				},
				Level::Max(a, b) => {
					w.byte(4);
					w.uvar(self.l(a));
					w.uvar(self.l(b));
				},
				Level::IMax(a, b) => {
					w.byte(5);
					w.uvar(self.l(a));
					w.uvar(self.l(b));
				},
				Level::Param(n) => {
					w.byte(6);
					w.uvar(self.n(n));
				},
				Level::Zero => unreachable!(),
			}
		}
		for &i in &self.exprs.order {
			match &self.ex.exprs[i as usize] {
				Expr::Nat(b) => {
					w.byte(7);
					w.raw(b);
				},
				Expr::Str(s) => {
					w.byte(8);
					w.string(s);
				},
				Expr::Let(t, v, b) => {
					w.byte(9);
					w.uvar(0);
					w.uvar(self.e(*t));
					w.uvar(self.e(*v));
					w.uvar(self.e(*b));
					w.byte(0);
				},
				Expr::Const(n, us) => {
					w.byte(10);
					w.uvar(self.n(*n));
					w.uvar(us.len() as u64);
					for &l in us.iter() {
						w.uvar(self.l(l));
					}
				},
				Expr::App(f, a) => {
					w.byte(11);
					w.uvar(self.e(*f));
					w.uvar(self.e(*a));
				},
				Expr::Pi(t, b) | Expr::Lam(t, b) => {
					w.byte(if matches!(self.ex.exprs[i as usize], Expr::Pi(..)) { 12 } else { 13 });
					w.uvar(0);
					w.uvar(self.e(*t));
					w.uvar(self.e(*b));
					w.byte(0);
				},
				Expr::Proj(n, idx, s) => {
					w.byte(14);
					w.uvar(self.n(*n));
					w.uvar(*idx);
					w.uvar(self.e(*s));
				},
				Expr::Sort(l) => {
					w.byte(15);
					w.uvar(self.l(*l));
				},
				Expr::BVar(k) => {
					w.byte(16);
					w.uvar(*k);
				},
			}
		}
	}

	fn ns(&self, w: &mut Writer, xs: &[u32]) {
		w.uvar(xs.len() as u64);
		for &x in xs {
			w.uvar(self.n(x));
		}
	}
}

#[derive(Default)]
struct Writer {
	out: Vec<u8>,
}

impl Writer {
	fn byte(&mut self, b: u8) {
		self.out.push(b);
	}
	fn uvar(&mut self, mut n: u64) {
		loop {
			let b = (n & 0x7f) as u8;
			n >>= 7;
			if n == 0 {
				self.out.push(b);
				return;
			}
			self.out.push(b | 0x80);
		}
	}
	fn boolean(&mut self, b: bool) {
		self.byte(b as u8);
	}
	fn raw(&mut self, data: &[u8]) {
		self.uvar(data.len() as u64);
		self.out.extend_from_slice(data);
	}
	fn string(&mut self, s: &str) {
		self.raw(s.as_bytes());
	}
}

/// The fields every declaration has.
struct Info {
	name: u32,
	lps: Vec<u32>,
	ty: u32,
}

fn info(v: &Value) -> Info {
	Info { name: u32_(&v["name"]), lps: u32s(&v["levelParams"]), ty: u32_(&v["type"]) }
}

const KINDS: [&str; 6] = ["axiom", "thm", "def", "opaque", "quot", "inductive"];

pub struct Converter {
	ex: Export,
	out: String,
	pack: Option<crate::pack::Pack>,
	node_of: HashMap<u32, Hash>,
	quots: Vec<Value>,
	manifest: std::io::BufWriter<std::fs::File>,
	first: bool,
	pub count: usize,
	pub node_bytes: u64,
	pub proof_bytes: u64,
}

fn blake2b256(data: &[u8]) -> Hash {
	let mut out = [0; 32];
	out.copy_from_slice(blake2b_simd::Params::new().hash_length(32).hash(data).as_bytes());
	out
}

fn hexs(h: &Hash) -> String {
	h.iter().map(|b| format!("{b:02x}")).collect()
}

fn header(magic: &[u8], imports: &[Hash]) -> Writer {
	let mut w = Writer { out: magic.to_vec() };
	w.uvar(imports.len() as u64);
	for h in imports {
		w.out.extend_from_slice(h);
	}
	w
}

impl Converter {
	pub fn new(out: &str, pack: bool, no_data: bool) -> Converter {
		std::fs::create_dir_all(format!("{out}/nodes")).unwrap();
		std::fs::create_dir_all(format!("{out}/proofs")).unwrap();
		let mut manifest = std::io::BufWriter::new(std::fs::File::create(format!("{out}/manifest.json")).unwrap());
		manifest.write_all(b"[").unwrap();
		Converter {
			ex: Export::new(),
			out: out.to_string(),
			pack: pack.then(|| {
				let mut p = crate::pack::Pack::open(out, true);
				p.no_data = no_data;
				p
			}),
			node_of: HashMap::new(),
			quots: Vec::new(),
			manifest,
			first: true,
			count: 0,
			node_bytes: 0,
			proof_bytes: 0,
		}
	}

	pub fn line(&mut self, line: &str) {
		if line.trim().is_empty() {
			return;
		}
		let v: Value = serde_json::from_str(line).expect("JSON line");
		let obj = v.as_object().expect("object");
		if obj.contains_key("meta") || self.ex.add(obj) {
			return;
		}
		let Some(kind) = KINDS.iter().find(|k| obj.contains_key(**k)) else {
			if obj.contains_key("mdata") {
				panic!("mdata is not supported");
			}
			panic!("unknown export item {:?}", obj.keys().collect::<Vec<_>>())
		};
		let decl = obj[*kind].clone();
		if *kind == "quot" {
			self.quots.push(decl);
			return;
		}
		self.flush_quots();
		self.group(kind, &[decl]);
	}

	pub fn finish(mut self) {
		self.flush_quots();
		self.manifest.write_all(b"\n]\n").unwrap();
		self.manifest.flush().unwrap();
		eprintln!("{} nodes, {} bytes of nodes, {} bytes of proofs", self.count, self.node_bytes, self.proof_bytes);
	}

	fn flush_quots(&mut self) {
		if !self.quots.is_empty() {
			let group = std::mem::take(&mut self.quots);
			self.group("quot", &group);
		}
	}

	fn declared(kind: &str, d: &Value) -> Vec<u32> {
		if kind == "inductive" {
			["types", "ctors", "recs"].iter().flat_map(|p| d[*p].as_array().unwrap().iter().map(|x| u32_(&x["name"]))).collect()
		} else {
			vec![u32_(&d["name"])]
		}
	}

	fn imports_of(&self, c: &Closure, own: &HashSet<u32>, of: u32) -> Vec<Hash> {
		let mut out: Vec<Hash> = c
			.consts
			.iter()
			.filter(|n| !own.contains(n))
			.map(|n| {
				*self.node_of.get(n).unwrap_or_else(|| {
					panic!("{} mentions {}, declared later or not at all", self.ex.name_str(of), self.ex.name_str(*n))
				})
			})
			.collect();
		out.sort();
		out.dedup();
		out
	}

	fn group(&mut self, kind: &str, group: &[Value]) {
		let ex = &self.ex;
		let d = &group[0];
		let own: HashSet<u32> = group.iter().flat_map(|d| Self::declared(kind, d)).collect();
		let mut c = Closure::new(ex);
		match kind {
			"quot" => group.iter().for_each(|d| c.info(&info(d))),
			"inductive" => {
				for part in ["types", "ctors", "recs"] {
					for x in d[part].as_array().unwrap() {
						c.info(&info(x));
						for rule in x.get("rules").and_then(Value::as_array).into_iter().flatten() {
							c.name(u32_(&rule["ctor"]));
							c.expr(u32_(&rule["rhs"]));
						}
						let mut names: Vec<u32> = x.get("all").map(u32s).unwrap_or_default();
						names.extend(x.get("ctors").map(u32s).unwrap_or_default());
						names.extend(x.get("induct").map(u32_));
						for nm in names {
							c.name(nm);
						}
					}
				}
			},
			_ => {
				c.info(&info(d));
				if kind == "def" || kind == "opaque" {
					c.expr(u32_(&d["value"]));
				}
			},
		}
		let name0 = u32_(&if kind == "inductive" { d["types"][0].clone() } else { d.clone() }["name"]);
		let imports = self.imports_of(&c, &own, name0);
		let mut w = header(NODE_MAGIC, &imports);
		c.items(&mut w);
		for d in group {
			Self::decl(&c, &mut w, kind, d);
		}
		let node = w.out;
		let h = blake2b256(&node);
		let mut proof = None;
		if kind == "thm" {
			let mut pc = Closure::new(ex);
			let value = u32_(&d["value"]);
			pc.expr(value);
			for p in u32s(&d["levelParams"]) {
				pc.name(p);
				pc.level(pc.param_level(p));
			}
			let proof_imports = self.imports_of(&pc, &HashSet::new(), name0);
			let mut pw = header(PROOF_MAGIC, &[]);
			pw.out.truncate(PROOF_MAGIC.len());
			pw.out.extend_from_slice(&h);
			pw.uvar(proof_imports.len() as u64);
			for i in &proof_imports {
				pw.out.extend_from_slice(i);
			}
			pc.items(&mut pw);
			pw.byte(TAG_PROOF);
			pw.uvar(pc.e(value));
			proof = Some((pw.out, proof_imports));
		}
		let names: Vec<String> = group.iter().flat_map(|d| Self::declared(kind, d)).map(|n| self.ex.name_str(n)).collect();
		for n in &own {
			self.node_of.insert(*n, h);
		}
		self.write(h, kind, &node, &imports, names, proof);
	}

	fn decl(c: &Closure, w: &mut Writer, kind: &str, d: &Value) {
		let head = |w: &mut Writer, tag: u8| {
			let i = info(d);
			w.byte(tag);
			w.uvar(c.n(i.name));
			c.ns(w, &i.lps);
			w.uvar(c.e(i.ty));
		};
		match kind {
			"axiom" => {
				head(w, 17);
				w.boolean(d["isUnsafe"].as_bool().unwrap());
			},
			"thm" => head(w, TAG_STATEMENT),
			"def" => {
				head(w, 19);
				w.uvar(c.e(u32_(&d["value"])));
				match &d["hints"] {
					Value::String(s) if s == "opaque" => w.byte(0),
					Value::String(s) if s == "abbrev" => w.byte(1),
					h => {
						w.byte(2);
						w.uvar(u(&h["regular"]));
					},
				}
				w.byte(match d["safety"].as_str().unwrap() {
					"safe" => 0,
					"unsafe" => 1,
					"partial" => 2,
					s => panic!("unknown safety {s}"),
				});
			},
			"opaque" => {
				head(w, 20);
				w.uvar(c.e(u32_(&d["value"])));
				w.boolean(d["isUnsafe"].as_bool().unwrap());
			},
			"quot" => {
				head(w, 21);
				w.byte(match d["kind"].as_str().unwrap() {
					"type" => 0,
					"ctor" => 1,
					"lift" => 2,
					"ind" => 3,
					s => panic!("unknown quot kind {s}"),
				});
			},
			"inductive" => {
				let b = |v: &Value| v.as_bool().unwrap();
				w.byte(22);
				let types = d["types"].as_array().unwrap();
				w.uvar(types.len() as u64);
				for t in types {
					let i = info(t);
					w.uvar(c.n(i.name));
					c.ns(w, &i.lps);
					w.uvar(c.e(i.ty));
					c.ns(w, &u32s(&t["all"]));
					c.ns(w, &u32s(&t["ctors"]));
					w.boolean(b(&t["isRec"]));
					w.boolean(b(&t["isReflexive"]));
					w.uvar(u(&t["numIndices"]));
					w.uvar(u(&t["numNested"]));
					w.uvar(u(&t["numParams"]));
					w.boolean(b(&t["isUnsafe"]));
				}
				let ctors = d["ctors"].as_array().unwrap();
				w.uvar(ctors.len() as u64);
				for k in ctors {
					let i = info(k);
					w.uvar(c.n(i.name));
					c.ns(w, &i.lps);
					w.uvar(c.e(i.ty));
					w.boolean(b(&k["isUnsafe"]));
					w.uvar(u(&k["cidx"]));
					w.uvar(u(&k["numParams"]));
					w.uvar(u(&k["numFields"]));
					w.uvar(c.n(u32_(&k["induct"])));
				}
				let recs = d["recs"].as_array().unwrap();
				w.uvar(recs.len() as u64);
				for r in recs {
					let i = info(r);
					w.uvar(c.n(i.name));
					c.ns(w, &i.lps);
					w.uvar(c.e(i.ty));
					w.boolean(b(&r["isUnsafe"]));
					w.uvar(u(&r["numParams"]));
					w.uvar(u(&r["numIndices"]));
					w.uvar(u(&r["numMotives"]));
					w.uvar(u(&r["numMinors"]));
					let rules = r["rules"].as_array().unwrap();
					w.uvar(rules.len() as u64);
					for rule in rules {
						w.uvar(c.n(u32_(&rule["ctor"])));
						w.uvar(u(&rule["nfields"]));
						w.uvar(c.e(u32_(&rule["rhs"])));
					}
					c.ns(w, &u32s(&r["all"]));
					w.boolean(b(&r["k"]));
				}
			},
			_ => unreachable!(),
		}
	}

	fn store(&mut self, kind: u8, h: &Hash, data: &[u8]) {
		if let Some(pack) = self.pack.as_mut() {
			return pack.put(kind, h, data);
		}
		let path = format!("{}/{}/{}", self.out, if kind == crate::pack::NODE { "nodes" } else { "proofs" }, hexs(h));
		if !std::path::Path::new(&path).exists() {
			std::fs::write(path, data).unwrap();
		}
	}

	fn write(&mut self, h: Hash, kind: &str, node: &[u8], imports: &[Hash], names: Vec<String>, proof: Option<(Vec<u8>, Vec<Hash>)>) {
		let hx = hexs(&h);
		// Nodes are content-addressed, so one already there (from another export) is this one.
		self.store(crate::pack::NODE, &h, node);
		let mut entry = serde_json::json!({
			"hash": hx, "names": names, "kind": kind, "size": node.len(),
			"imports": imports.iter().map(hexs).collect::<Vec<_>>(),
		});
		if let Some((p, pi)) = proof {
			self.store(crate::pack::PROOF, &h, &p);
			entry["proof_size"] = p.len().into();
			entry["proof_imports"] = pi.iter().map(hexs).collect::<Vec<_>>().into();
			self.proof_bytes += p.len() as u64;
		}
		self.manifest.write_all(if self.first { b"\n" } else { b",\n" }).unwrap();
		self.first = false;
		serde_json::to_writer(&mut self.manifest, &entry).unwrap();
		self.count += 1;
		self.node_bytes += node.len() as u64;
	}
}

/// Convert the export at `path` ("-" for stdin) into `out`, as lean_nodes.py does (or into its
/// pack, if `pack`; with `no_data`, recording only which nodes it has).
pub fn convert(path: &str, out: &str, pack: bool, no_data: bool) {
	let input: Box<dyn BufRead> = if path == "-" {
		Box::new(std::io::BufReader::with_capacity(1 << 20, std::io::stdin()))
	} else {
		Box::new(std::io::BufReader::with_capacity(1 << 20, std::fs::File::open(path).expect("export")))
	};
	let mut c = Converter::new(out, pack, no_data);
	for line in input.lines() {
		c.line(&line.expect("export line"));
	}
	c.finish();
}
