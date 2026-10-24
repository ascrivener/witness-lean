//! Judgments: kernel cache entries attested once and trusted after, so that a declaration too
//! heavy for one check can be checked in pieces (witness-lean's
//! `docs/design/heavy-declarations.md`).
//!
//! A *judgment blob* holds cache entries made while checking one declaration: `e : T`, `e`
//! reduces to `v`, `x ≡ y`, and the like, exactly as nanoda caches them (see [`Entry`]). Its
//! header names the declaration's node and, as a node's does, the nodes declaring every constant
//! its terms mention: its *imports*. An entry holds wherever its terms mean the same: in a checker
//! for that declaration, with every constant it mentions declared by one of its imports. Locals
//! are de Bruijn levels with their types, so an entry carries its whole local context.
//!
//! A *calls blob* lists kernel calls to run (an inference, a reduction, a definitional equality
//! or a lazy delta step), each from a starting depth.
//!
//! Format: a magic ([`JUDGMENT_MAGIC`] or [`CALLS_MAGIC`]); for a judgment, the declaration's
//! node hash (32 bytes) and a `u` count of import hashes (32 bytes each); then items, each a tag
//! byte and its fields, `u` being an unsigned LEB128 varint. Names count from 1 (0 is
//! anonymous), levels from 1 (0 is zero), expressions from 0, each in order of appearance; every
//! reference is to an earlier item.
//!
//! | Tag | Item | Fields |
//! |---|---|---|
//! | 1 | name str | prefix `u`, string (`u` length, UTF-8) |
//! | 2 | name num | prefix `u`, number `u` |
//! | 3, 4, 5 | level succ, max, imax | `u`, or two |
//! | 6 | level param | name `u` |
//! | 7 | nat literal | `u` length, little-endian bytes |
//! | 8 | string literal | `u` length, UTF-8 |
//! | 9 | let | name, type, value, body `u`; nondep byte |
//! | 10 | const | name `u`, `u` count, levels `u` |
//! | 11 | app | function, argument `u` |
//! | 12, 13 | pi, lambda | name `u`, binder style byte, type, body `u` |
//! | 14 | proj | structure name `u`, index `u`, structure `u` |
//! | 15 | sort | level `u` |
//! | 16 | bound variable | index `u` |
//! | 17 | local | name `u`, binder style byte, type `u`, de Bruijn level `u` |
//! | 32 | a call (calls blobs only) | kind byte, starting depth `u`, then its inputs `u` |
//! | 33 | an entry (judgments only) | cache byte, then its key and value |
//!
//! Call kinds: 0 infer (checking), 1 infer (inferring only), 2 whnf, each one input; 3 def_eq, 4
//! lazy delta step, two. Entry caches, as `TcCache`'s fields: 0 `infer_cache_check`, 1
//! `infer_cache_no_check`, 2 `whnf_cache`, 3 `whnf_no_unfolding_cache`, each a key and a value; 4
//! `defeq_fail_cache`, two expressions and the eager-mode byte; 5 `eq_cache`, 6
//! `congr_fail_cache`, two expressions.
#[allow(unused_imports)]
use crate::prelude::*;
use crate::expr::{BinderStyle, Expr, FVarId};
use crate::level::Level;
use crate::name::Name;
use crate::nodes::Hash;
use crate::tc::{DeltaResult, InferFlag, TypeChecker};
use crate::util::{CowStr, ExprPtr, FxHashMap, FxHashSet, LevelPtr, NamePtr, SortedPair, new_fx_hash_map, new_fx_hash_set};
use core::error::Error;

pub const JUDGMENT_MAGIC: &[u8] = b"LEANJDG\x01";
pub const CALLS_MAGIC: &[u8] = b"LEANCAL\x01";

/// A cache entry: what the kernel concluded, and in which cache it keeps it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Entry<'t> {
    /// `e` is well typed, of type `T` (`infer_cache_check`).
    Infer(ExprPtr<'t>, ExprPtr<'t>),
    /// `T` is `e`'s type, if `e` is well typed (`infer_cache_no_check`).
    InferOnly(ExprPtr<'t>, ExprPtr<'t>),
    /// `e`'s weak head normal form is `v` (`whnf_cache`).
    Whnf(ExprPtr<'t>, ExprPtr<'t>),
    /// `e`'s weak head normal form without unfolding definitions is `v`
    /// (`whnf_no_unfolding_cache`).
    WhnfCore(ExprPtr<'t>, ExprPtr<'t>),
    /// `x ≢ y`, in eager mode or not (`defeq_fail_cache`).
    DefEqFail(ExprPtr<'t>, ExprPtr<'t>, bool),
    /// `x ≡ y` (`eq_cache`).
    DefEq(ExprPtr<'t>, ExprPtr<'t>),
    /// Congruence fails on `x` and `y` (`congr_fail_cache`).
    CongrFail(ExprPtr<'t>, ExprPtr<'t>),
}

impl<'t> Entry<'t> {
    fn terms(&self) -> [ExprPtr<'t>; 2] {
        match *self {
            Entry::Infer(a, b)
            | Entry::InferOnly(a, b)
            | Entry::Whnf(a, b)
            | Entry::WhnfCore(a, b)
            | Entry::DefEqFail(a, b, _)
            | Entry::DefEq(a, b)
            | Entry::CongrFail(a, b) => [a, b],
        }
    }
}

/// A kernel call.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Call<'t> {
    /// Infer `e`'s type, checking it (`true`) or not.
    Infer(ExprPtr<'t>, bool),
    Whnf(ExprPtr<'t>),
    DefEq(ExprPtr<'t>, ExprPtr<'t>),
    LazyDelta(ExprPtr<'t>, ExprPtr<'t>),
}

impl<'t> Call<'t> {
    fn inputs(&self) -> Vec<ExprPtr<'t>> {
        match *self {
            Call::Infer(e, _) | Call::Whnf(e) => vec![e],
            Call::DefEq(x, y) | Call::LazyDelta(x, y) => vec![x, y],
        }
    }
}

/// A judgment blob's header.
pub struct Header<'b> {
    /// The node of the declaration it was made checking.
    pub declaration: Hash,
    /// The nodes declaring the constants it mentions.
    pub imports: Vec<Hash>,
    items: &'b [u8],
}

struct Reader<'b> {
    bytes: &'b [u8],
}

impl<'b> Reader<'b> {
    fn byte(&mut self) -> Result<u8, Box<dyn Error>> {
        let (&b, rest) = self.bytes.split_first().ok_or("ends early")?;
        self.bytes = rest;
        Ok(b)
    }
    fn u(&mut self) -> Result<u64, Box<dyn Error>> {
        let mut value = 0u64;
        for shift in (0..64).step_by(7) {
            let b = self.byte()?;
            value |= u64::from(b & 0x7f) << shift;
            if b & 0x80 == 0 {
                return Ok(value);
            }
        }
        Err("varint too long".into())
    }
    fn idx(&mut self) -> Result<usize, Box<dyn Error>> {
        Ok(usize::try_from(self.u()?)?)
    }
    fn take(&mut self, n: usize) -> Result<&'b [u8], Box<dyn Error>> {
        let (b, rest) = self.bytes.split_at_checked(n).ok_or("ends early")?;
        self.bytes = rest;
        Ok(b)
    }
    fn bytes(&mut self) -> Result<&'b [u8], Box<dyn Error>> {
        let n = self.idx()?;
        self.take(n)
    }
    fn str(&mut self) -> Result<String, Box<dyn Error>> {
        Ok(core::str::from_utf8(self.bytes()?)?.to_string())
    }
    fn hash(&mut self) -> Result<Hash, Box<dyn Error>> {
        Ok(*self.take(32)?.first_chunk::<32>().ok_or("ends early")?)
    }
}

/// Read a judgment blob's header.
pub fn header(blob: &[u8]) -> Result<Header<'_>, Box<dyn Error>> {
    let mut r = Reader { bytes: blob.strip_prefix(JUDGMENT_MAGIC).ok_or("not a judgment")? };
    let declaration = r.hash()?;
    let n = r.idx()?;
    let imports = (0..n).map(|_| r.hash()).collect::<Result<Vec<_>, _>>()?;
    Ok(Header { declaration, imports, items: r.bytes })
}

fn style(b: u8) -> Result<BinderStyle, Box<dyn Error>> {
    Ok(match b {
        0 => BinderStyle::Default,
        1 => BinderStyle::Implicit,
        2 => BinderStyle::StrictImplicit,
        3 => BinderStyle::InstanceImplicit,
        _ => return Err("bad binder style".into()),
    })
}

fn style_byte(s: BinderStyle) -> u8 {
    match s {
        BinderStyle::Default => 0,
        BinderStyle::Implicit => 1,
        BinderStyle::StrictImplicit => 2,
        BinderStyle::InstanceImplicit => 3,
    }
}

/// A blob's entries, and its calls with their starting depths.
type Items<'t> = (Vec<Entry<'t>>, Vec<(u16, Call<'t>)>);

/// Rebuild the items in `items` in `tc`, with the checker's own constructors, so that each term
/// is the pointer the checker would build: entries if `entries`, else calls.
fn read<'t>(
    tc: &mut TypeChecker<'_, 't, '_>,
    items: &[u8],
    entries: bool,
) -> Result<Items<'t>, Box<dyn Error>> {
    let ctx = &mut *tc.ctx;
    let mut r = Reader { bytes: items };
    let mut names: Vec<NamePtr<'t>> = vec![ctx.anonymous()];
    let mut levels: Vec<LevelPtr<'t>> = vec![ctx.zero()];
    let mut exprs: Vec<ExprPtr<'t>> = Vec::new();
    let (mut out, mut calls) = (Vec::new(), Vec::new());
    fn get<T: Copy>(r: &mut Reader, v: &[T]) -> Result<T, Box<dyn Error>> {
        Ok(*v.get(r.idx()?).ok_or("a reference to a later item")?)
    }
    while !r.bytes.is_empty() {
        let tag = r.byte()?;
        match tag {
            1 => {
                let pfx = get(&mut r, &names)?;
                let s = r.str()?;
                let s = ctx.alloc_string(CowStr::Owned(s));
                names.push(ctx.str(pfx, s));
            },
            2 => {
                let pfx = get(&mut r, &names)?;
                let k = r.u()?;
                names.push(ctx.num(pfx, k));
            },
            3 => {
                let a = get(&mut r, &levels)?;
                levels.push(ctx.succ(a));
            },
            4 | 5 => {
                let (a, b) = (get(&mut r, &levels)?, get(&mut r, &levels)?);
                levels.push(if tag == 4 { ctx.max(a, b) } else { ctx.imax(a, b) });
            },
            6 => {
                let n = get(&mut r, &names)?;
                levels.push(ctx.param(n));
            },
            7 => {
                let b = r.bytes()?;
                exprs.push(ctx.mk_nat_lit_quick(num_bigint::BigUint::from_bytes_le(b)).ok_or("nat literals are off")?);
            },
            8 => {
                let s = r.str()?;
                exprs.push(ctx.mk_string_lit_quick(CowStr::Owned(s)).ok_or("string literals are off")?);
            },
            9 => {
                let name = get(&mut r, &names)?;
                let (ty, val, body) = (get(&mut r, &exprs)?, get(&mut r, &exprs)?, get(&mut r, &exprs)?);
                let nondep = r.byte()? != 0;
                exprs.push(ctx.mk_let(name, ty, val, body, nondep));
            },
            10 => {
                let name = get(&mut r, &names)?;
                let k = r.idx()?;
                let ls = (0..k).map(|_| get(&mut r, &levels)).collect::<Result<Vec<_>, _>>()?;
                let ls = ctx.alloc_levels_slice(&ls);
                exprs.push(ctx.mk_const(name, ls));
            },
            11 => {
                let (f, a) = (get(&mut r, &exprs)?, get(&mut r, &exprs)?);
                exprs.push(ctx.mk_app(f, a));
            },
            12 | 13 => {
                let name = get(&mut r, &names)?;
                let s = style(r.byte()?)?;
                let (ty, body) = (get(&mut r, &exprs)?, get(&mut r, &exprs)?);
                exprs.push(if tag == 12 { ctx.mk_pi(name, s, ty, body) } else { ctx.mk_lambda(name, s, ty, body) });
            },
            14 => {
                let name = get(&mut r, &names)?;
                let i = r.idx()?;
                let s = get(&mut r, &exprs)?;
                exprs.push(ctx.mk_proj(name, i, s));
            },
            15 => {
                let l = get(&mut r, &levels)?;
                exprs.push(ctx.mk_sort(l));
            },
            16 => {
                let i = u16::try_from(r.u()?)?;
                exprs.push(ctx.mk_var(i));
            },
            17 => {
                let name = get(&mut r, &names)?;
                let s = style(r.byte()?)?;
                let ty = get(&mut r, &exprs)?;
                let level = u16::try_from(r.u()?)?;
                exprs.push(ctx.remake_dbj_level(name, s, ty, level));
            },
            32 if !entries => {
                let kind = r.byte()?;
                let depth = u16::try_from(r.u()?)?;
                let call = match kind {
                    0 | 1 => Call::Infer(get(&mut r, &exprs)?, kind == 0),
                    2 => Call::Whnf(get(&mut r, &exprs)?),
                    3 => Call::DefEq(get(&mut r, &exprs)?, get(&mut r, &exprs)?),
                    4 => Call::LazyDelta(get(&mut r, &exprs)?, get(&mut r, &exprs)?),
                    _ => return Err("bad call kind".into()),
                };
                calls.push((depth, call));
            },
            33 if entries => {
                let cache = r.byte()?;
                let (a, b) = (get(&mut r, &exprs)?, get(&mut r, &exprs)?);
                out.push(match cache {
                    0 => Entry::Infer(a, b),
                    1 => Entry::InferOnly(a, b),
                    2 => Entry::Whnf(a, b),
                    3 => Entry::WhnfCore(a, b),
                    4 => Entry::DefEqFail(a, b, r.byte()? != 0),
                    5 => Entry::DefEq(a, b),
                    6 => Entry::CongrFail(a, b),
                    _ => return Err("bad cache".into()),
                });
            },
            _ => return Err(format!("unexpected item tag {tag}").into()),
        }
    }
    Ok((out, calls))
}

/// Rebuild a judgment's entries in `tc`.
pub fn entries<'t>(tc: &mut TypeChecker<'_, 't, '_>, header: &Header) -> Result<Vec<Entry<'t>>, Box<dyn Error>> {
    Ok(read(tc, header.items, true)?.0)
}

/// Rebuild a calls blob's calls in `tc`, each with its starting depth.
pub fn calls<'t>(tc: &mut TypeChecker<'_, 't, '_>, blob: &[u8]) -> Result<Vec<(u16, Call<'t>)>, Box<dyn Error>> {
    Ok(read(tc, blob.strip_prefix(CALLS_MAGIC).ok_or("not calls")?, false)?.1)
}

/// Every node reachable from `roots`, through locals' types.
fn reachable<'t>(tc: &TypeChecker<'_, 't, '_>, roots: impl IntoIterator<Item = ExprPtr<'t>>) -> FxHashSet<ExprPtr<'t>> {
    let mut seen = new_fx_hash_set();
    let mut stack: Vec<ExprPtr<'t>> = roots.into_iter().collect();
    while let Some(e) = stack.pop() {
        if !seen.insert(e) {
            continue;
        }
        match tc.ctx.read_expr(e) {
            Expr::App { fun, arg, .. } => stack.extend([fun, arg]),
            Expr::Pi { binder_type, body, .. } | Expr::Lambda { binder_type, body, .. } => stack.extend([binder_type, body]),
            Expr::Let { binder_type, val, body, .. } => stack.extend([binder_type, val, body]),
            Expr::Proj { structure, .. } => stack.push(structure),
            Expr::Local { binder_type, .. } => stack.push(binder_type),
            _ => {},
        }
    }
    seen
}

/// The constants `entries` mention (and the structures their projections name).
pub fn mentions<'t>(tc: &TypeChecker<'_, 't, '_>, entries: &[Entry<'t>]) -> Vec<NamePtr<'t>> {
    let mut out = Vec::new();
    for e in reachable(tc, entries.iter().flat_map(|e| e.terms())) {
        match tc.ctx.read_expr(e) {
            Expr::Const { name, .. } => out.push(name),
            Expr::Proj { ty_name, .. } => out.push(ty_name),
            _ => {},
        }
    }
    out.sort_by_key(|n| n.get_hash());
    out.dedup();
    out
}

/// Put `entries` in `tc`'s caches. The caller must have checked that they hold here: attested,
/// for this declaration, with every constant they mention declared by one of their imports.
pub fn seed<'t>(tc: &mut TypeChecker<'_, 't, '_>, entries: &[Entry<'t>]) {
    let c = &mut tc.tc_cache;
    for &e in entries {
        match e {
            Entry::Infer(k, v) => _ = c.infer_cache_check.insert(k, v),
            Entry::InferOnly(k, v) => _ = c.infer_cache_no_check.insert(k, v),
            Entry::Whnf(k, v) => _ = c.whnf_cache.insert(k, v),
            Entry::WhnfCore(k, v) => _ = c.whnf_no_unfolding_cache.insert(k, v),
            Entry::DefEqFail(x, y, eager) => _ = c.defeq_fail_cache.insert((x, y, eager)),
            Entry::DefEq(x, y) => _ = c.eq_cache.insert(SortedPair::new(x, y)),
            Entry::CongrFail(x, y) => _ = c.congr_fail_cache.insert(SortedPair::new(x, y)),
        }
    }
}

/// Whether `entry` is in `tc`'s caches.
pub fn holds<'t>(tc: &TypeChecker<'_, 't, '_>, entry: &Entry<'t>) -> bool {
    let c = &tc.tc_cache;
    match *entry {
        Entry::Infer(k, v) => c.infer_cache_check.get(&k) == Some(&v),
        Entry::InferOnly(k, v) => c.infer_cache_no_check.get(&k) == Some(&v),
        Entry::Whnf(k, v) => c.whnf_cache.get(&k) == Some(&v),
        Entry::WhnfCore(k, v) => c.whnf_no_unfolding_cache.get(&k) == Some(&v),
        Entry::DefEqFail(x, y, eager) => c.defeq_fail_cache.contains(&(x, y, eager)),
        Entry::DefEq(x, y) => c.eq_cache.contains(&SortedPair::new(x, y)),
        Entry::CongrFail(x, y) => c.congr_fail_cache.contains(&SortedPair::new(x, y)),
    }
}

/// Every entry in `tc`'s caches, for writing judgments.
pub fn cached<'t>(tc: &TypeChecker<'_, 't, '_>) -> Vec<Entry<'t>> {
    let c = &tc.tc_cache;
    let mut out: Vec<Entry<'t>> = Vec::new();
    out.extend(c.infer_cache_check.iter().map(|(&k, &v)| Entry::Infer(k, v)));
    out.extend(c.infer_cache_no_check.iter().map(|(&k, &v)| Entry::InferOnly(k, v)));
    out.extend(c.whnf_cache.iter().map(|(&k, &v)| Entry::Whnf(k, v)));
    out.extend(c.whnf_no_unfolding_cache.iter().map(|(&k, &v)| Entry::WhnfCore(k, v)));
    out.extend(c.defeq_fail_cache.iter().map(|&(x, y, eager)| Entry::DefEqFail(x, y, eager)));
    out.extend(c.eq_cache.iter().map(|p| Entry::DefEq(p.0, p.1)));
    out.extend(c.congr_fail_cache.iter().map(|p| Entry::CongrFail(p.0, p.1)));
    out
}

/// What a call returned.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Outcome<'t> {
    Expr(ExprPtr<'t>),
    Bool(bool),
    /// A lazy delta step that ran out, with where it stopped.
    Exhausted(ExprPtr<'t>, ExprPtr<'t>),
}

/// Run `call` from de Bruijn depth `depth`, which must be above every local its inputs mention:
/// the locals it opens are then fresh. Type errors panic, as everywhere in the kernel.
pub fn run<'t>(tc: &mut TypeChecker<'_, 't, '_>, depth: u16, call: Call<'t>) -> Result<Outcome<'t>, Box<dyn Error>> {
    for e in reachable(tc, call.inputs()) {
        if let Expr::Local { id: FVarId::DbjLevel(level), .. } = tc.ctx.read_expr(e) {
            if level >= depth {
                return Err("a call's input mentions a local at or above its starting depth".into());
            }
        }
    }
    let before = tc.ctx.dbj_level_counter;
    tc.ctx.dbj_level_counter = depth;
    let out = match call {
        Call::Infer(e, check) => Outcome::Expr(tc.infer(e, if check { InferFlag::Check } else { InferFlag::InferOnly })),
        Call::Whnf(e) => Outcome::Expr(tc.whnf(e)),
        Call::DefEq(x, y) => Outcome::Bool(tc.def_eq(x, y)),
        Call::LazyDelta(x, y) => match tc.lazy_delta_step(x, y) {
            DeltaResult::FoundEqResult(b) => Outcome::Bool(b),
            DeltaResult::Exhausted(a, b) => Outcome::Exhausted(a, b),
        },
    };
    tc.ctx.dbj_level_counter = before;
    Ok(out)
}

/// Writes term tables, sharing subterms.
struct Writer<'a, 'x, 't, 'p> {
    tc: &'a TypeChecker<'x, 't, 'p>,
    out: Vec<u8>,
    names: FxHashMap<NamePtr<'t>, u64>,
    levels: FxHashMap<LevelPtr<'t>, u64>,
    exprs: FxHashMap<ExprPtr<'t>, u64>,
}

fn uvar(out: &mut Vec<u8>, mut n: u64) {
    loop {
        let b = (n & 0x7f) as u8;
        n >>= 7;
        if n == 0 {
            return out.push(b);
        }
        out.push(b | 0x80);
    }
}

impl<'a, 'x, 't, 'p> Writer<'a, 'x, 't, 'p> {
    fn new(tc: &'a TypeChecker<'x, 't, 'p>, out: Vec<u8>) -> Self {
        Writer { tc, out, names: new_fx_hash_map(), levels: new_fx_hash_map(), exprs: new_fx_hash_map() }
    }

    fn name(&mut self, n: NamePtr<'t>) -> u64 {
        if let Some(&i) = self.names.get(&n) {
            return i;
        }
        match self.tc.ctx.read_name(n) {
            Name::Anon => return 0,
            Name::Str(pfx, s, _) => {
                let p = self.name(pfx);
                let s = self.tc.ctx.read_string(s).to_string();
                self.out.push(1);
                uvar(&mut self.out, p);
                uvar(&mut self.out, s.len() as u64);
                self.out.extend_from_slice(s.as_bytes());
            },
            Name::Num(pfx, k, _) => {
                let p = self.name(pfx);
                self.out.push(2);
                uvar(&mut self.out, p);
                uvar(&mut self.out, k);
            },
        }
        let i = self.names.len() as u64 + 1;
        self.names.insert(n, i);
        i
    }

    fn level(&mut self, l: LevelPtr<'t>) -> u64 {
        if let Some(&i) = self.levels.get(&l) {
            return i;
        }
        match self.tc.ctx.read_level(l) {
            Level::Zero => return 0,
            Level::Succ(a, _) => {
                let a = self.level(a);
                self.out.push(3);
                uvar(&mut self.out, a);
            },
            Level::Max(a, b, _) | Level::IMax(a, b, _) => {
                let tag = if matches!(self.tc.ctx.read_level(l), Level::Max(..)) { 4 } else { 5 };
                let (a, b) = (self.level(a), self.level(b));
                self.out.push(tag);
                uvar(&mut self.out, a);
                uvar(&mut self.out, b);
            },
            Level::Param(n, _) => {
                let n = self.name(n);
                self.out.push(6);
                uvar(&mut self.out, n);
            },
        }
        let i = self.levels.len() as u64 + 1;
        self.levels.insert(l, i);
        i
    }

    /// Write `root` and what it's made of, children first, iteratively: terms can be deep.
    fn expr(&mut self, root: ExprPtr<'t>) -> u64 {
        let mut stack = vec![(root, false)];
        while let Some((e, ready)) = stack.pop() {
            if self.exprs.contains_key(&e) {
                continue;
            }
            let x = self.tc.ctx.read_expr(e);
            if !ready {
                stack.push((e, true));
                match x {
                    Expr::App { fun, arg, .. } => stack.extend([(arg, false), (fun, false)]),
                    Expr::Pi { binder_type, body, .. } | Expr::Lambda { binder_type, body, .. } => {
                        stack.extend([(body, false), (binder_type, false)])
                    },
                    Expr::Let { binder_type, val, body, .. } => {
                        stack.extend([(body, false), (val, false), (binder_type, false)])
                    },
                    Expr::Proj { structure, .. } => stack.push((structure, false)),
                    Expr::Local { binder_type, .. } => stack.push((binder_type, false)),
                    _ => {},
                }
                continue;
            }
            let mut item = Vec::new();
            match x {
                Expr::NatLit { ptr, .. } => {
                    let b = self.tc.ctx.read_bignum(ptr).unwrap().to_bytes_le();
                    item.push(7);
                    uvar(&mut item, b.len() as u64);
                    item.extend_from_slice(&b);
                },
                Expr::StringLit { ptr, .. } => {
                    let s = self.tc.ctx.read_string(ptr).to_string();
                    item.push(8);
                    uvar(&mut item, s.len() as u64);
                    item.extend_from_slice(s.as_bytes());
                },
                Expr::Let { binder_name, binder_type, val, body, nondep, .. } => {
                    let n = self.name(binder_name);
                    item.push(9);
                    for v in [n, self.exprs[&binder_type], self.exprs[&val], self.exprs[&body]] {
                        uvar(&mut item, v);
                    }
                    item.push(u8::from(nondep));
                },
                Expr::Const { name, levels, .. } => {
                    let n = self.name(name);
                    let ls: Vec<u64> = self.tc.ctx.read_levels(levels).iter().map(|&l| self.level(l)).collect();
                    item.push(10);
                    uvar(&mut item, n);
                    uvar(&mut item, ls.len() as u64);
                    for l in ls {
                        uvar(&mut item, l);
                    }
                },
                Expr::App { fun, arg, .. } => {
                    item.push(11);
                    uvar(&mut item, self.exprs[&fun]);
                    uvar(&mut item, self.exprs[&arg]);
                },
                Expr::Pi { binder_name, binder_style, binder_type, body, .. }
                | Expr::Lambda { binder_name, binder_style, binder_type, body, .. } => {
                    let n = self.name(binder_name);
                    item.push(if matches!(x, Expr::Pi { .. }) { 12 } else { 13 });
                    uvar(&mut item, n);
                    item.push(style_byte(binder_style));
                    uvar(&mut item, self.exprs[&binder_type]);
                    uvar(&mut item, self.exprs[&body]);
                },
                Expr::Proj { ty_name, idx, structure, .. } => {
                    let n = self.name(ty_name);
                    item.push(14);
                    uvar(&mut item, n);
                    uvar(&mut item, idx as u64);
                    uvar(&mut item, self.exprs[&structure]);
                },
                Expr::Sort { level, .. } => {
                    let l = self.level(level);
                    item.push(15);
                    uvar(&mut item, l);
                },
                Expr::Var { dbj_idx, .. } => {
                    item.push(16);
                    uvar(&mut item, u64::from(dbj_idx));
                },
                Expr::Local { binder_name, binder_style, binder_type, id, .. } => {
                    let FVarId::DbjLevel(level) = id else { panic!("a judgment can't hold a unique local") };
                    let n = self.name(binder_name);
                    item.push(17);
                    uvar(&mut item, n);
                    item.push(style_byte(binder_style));
                    uvar(&mut item, self.exprs[&binder_type]);
                    uvar(&mut item, u64::from(level));
                },
            }
            self.out.extend_from_slice(&item);
            let i = self.exprs.len() as u64;
            self.exprs.insert(e, i);
        }
        self.exprs[&root]
    }
}

/// A judgment blob of `entries`, made checking declaration node `declaration`, with `imports`
/// (the nodes declaring what [`mentions`] lists).
pub fn write_judgment<'t>(tc: &TypeChecker<'_, 't, '_>, declaration: &Hash, imports: &[Hash], entries: &[Entry<'t>]) -> Vec<u8> {
    let mut head = JUDGMENT_MAGIC.to_vec();
    head.extend_from_slice(declaration);
    uvar(&mut head, imports.len() as u64);
    for h in imports {
        head.extend_from_slice(h);
    }
    let mut w = Writer::new(tc, head);
    for entry in entries {
        let [a, b] = entry.terms();
        let (a, b) = (w.expr(a), w.expr(b));
        let cache = match entry {
            Entry::Infer(..) => 0,
            Entry::InferOnly(..) => 1,
            Entry::Whnf(..) => 2,
            Entry::WhnfCore(..) => 3,
            Entry::DefEqFail(..) => 4,
            Entry::DefEq(..) => 5,
            Entry::CongrFail(..) => 6,
        };
        w.out.extend_from_slice(&[33, cache]);
        uvar(&mut w.out, a);
        uvar(&mut w.out, b);
        if let Entry::DefEqFail(_, _, eager) = entry {
            w.out.push(u8::from(*eager));
        }
    }
    w.out
}

/// A calls blob of `calls`, each with its starting depth.
pub fn write_calls<'t>(tc: &TypeChecker<'_, 't, '_>, calls: &[(u16, Call<'t>)]) -> Vec<u8> {
    let mut w = Writer::new(tc, CALLS_MAGIC.to_vec());
    for &(depth, call) in calls {
        let inputs: Vec<u64> = call.inputs().into_iter().map(|e| w.expr(e)).collect();
        let kind = match call {
            Call::Infer(_, true) => 0,
            Call::Infer(_, false) => 1,
            Call::Whnf(_) => 2,
            Call::DefEq(..) => 3,
            Call::LazyDelta(..) => 4,
        };
        w.out.extend_from_slice(&[32, kind]);
        uvar(&mut w.out, u64::from(depth));
        for i in inputs {
            uvar(&mut w.out, i);
        }
    }
    w.out
}

/// For tests: the locals `e` mentions, and `e` with one of them replaced.
#[cfg(feature = "testing")]
pub mod testing {
    use super::*;

    pub fn locals<'t>(tc: &TypeChecker<'_, 't, '_>, e: ExprPtr<'t>) -> Vec<ExprPtr<'t>> {
        reachable(tc, [e]).into_iter().filter(|&x| matches!(tc.ctx.read_expr(x), Expr::Local { .. })).collect()
    }

    /// `local` (a de Bruijn level local) with its type replaced by `ty`.
    pub fn retyped<'t>(tc: &mut TypeChecker<'_, 't, '_>, local: ExprPtr<'t>, ty: ExprPtr<'t>) -> ExprPtr<'t> {
        let Expr::Local { binder_name, binder_style, id: FVarId::DbjLevel(level), .. } = tc.ctx.read_expr(local) else {
            panic!("not a level local")
        };
        tc.ctx.remake_dbj_level(binder_name, binder_style, ty, level)
    }

    /// `e` with `from` replaced by `to` wherever it occurs.
    pub fn replace<'t>(tc: &mut TypeChecker<'_, 't, '_>, e: ExprPtr<'t>, from: ExprPtr<'t>, to: ExprPtr<'t>) -> ExprPtr<'t> {
        if e == from {
            return to;
        }
        match tc.ctx.read_expr(e) {
            Expr::App { fun, arg, .. } => {
                let (f, a) = (replace(tc, fun, from, to), replace(tc, arg, from, to));
                tc.ctx.mk_app(f, a)
            },
            Expr::Pi { binder_name, binder_style, binder_type, body, .. } => {
                let (t, b) = (replace(tc, binder_type, from, to), replace(tc, body, from, to));
                tc.ctx.mk_pi(binder_name, binder_style, t, b)
            },
            Expr::Lambda { binder_name, binder_style, binder_type, body, .. } => {
                let (t, b) = (replace(tc, binder_type, from, to), replace(tc, body, from, to));
                tc.ctx.mk_lambda(binder_name, binder_style, t, b)
            },
            Expr::Let { binder_name, binder_type, val, body, nondep, .. } => {
                let (t, v, b) = (replace(tc, binder_type, from, to), replace(tc, val, from, to), replace(tc, body, from, to));
                tc.ctx.mk_let(binder_name, t, v, b, nondep)
            },
            Expr::Proj { ty_name, idx, structure, .. } => {
                let s = replace(tc, structure, from, to);
                tc.ctx.mk_proj(ty_name, idx, s)
            },
            _ => e,
        }
    }

    /// The constant `name` (dotted), with no universe levels.
    pub fn constant<'t>(tc: &mut TypeChecker<'_, 't, '_>, name: &str) -> ExprPtr<'t> {
        let mut n = tc.ctx.anonymous();
        for part in name.split('.') {
            let s = tc.ctx.alloc_string(CowStr::Owned(part.to_string()));
            n = tc.ctx.str(n, s);
        }
        let ls = tc.ctx.alloc_levels_slice(&[]);
        tc.ctx.mk_const(n, ls)
    }

    /// The type of the declaration `tc` checks.
    pub fn declaration<'t>(tc: &TypeChecker<'_, 't, '_>) -> ExprPtr<'t> {
        tc.declar_info.unwrap().ty
    }
}
