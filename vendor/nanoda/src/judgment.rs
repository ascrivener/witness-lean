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
//! | 32 | a call (calls blobs only) | kind byte (plus 128 to run it in eager mode), starting depth `u`, its inputs `u`, then a `u` count of the cited entries to seed before it, each a cited judgment's position `u` and an entry's position in it `u` |
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
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
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
    /// The entry as its cache keys it: `eq_cache` and `congr_fail_cache` hold unordered pairs.
    #[cfg_attr(not(feature = "trace"), allow(dead_code))]
    pub(crate) fn normal(self) -> Self {
        match self {
            Entry::DefEq(x, y) => {
                let p = SortedPair::new(x, y);
                Entry::DefEq(p.0, p.1)
            },
            Entry::CongrFail(x, y) => {
                let p = SortedPair::new(x, y);
                Entry::CongrFail(p.0, p.1)
            },
            e => e,
        }
    }

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

/// One call of a calls blob: its starting depth, whether it runs in eager mode, the call, and the
/// cited entries to seed before it (a cited judgment's position, an entry's position in it).
pub type CallItem<'t> = (u16, bool, Call<'t>, Vec<(usize, usize)>);

/// A blob's entries, and its calls.
type Items<'t> = (Vec<Entry<'t>>, Vec<CallItem<'t>>);

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
                let byte = r.byte()?;
                let (kind, eager) = (byte & 0x7f, byte & 0x80 != 0);
                let depth = u16::try_from(r.u()?)?;
                let call = match kind {
                    0 | 1 => Call::Infer(get(&mut r, &exprs)?, kind == 0),
                    2 => Call::Whnf(get(&mut r, &exprs)?),
                    3 => Call::DefEq(get(&mut r, &exprs)?, get(&mut r, &exprs)?),
                    4 => Call::LazyDelta(get(&mut r, &exprs)?, get(&mut r, &exprs)?),
                    _ => return Err("bad call kind".into()),
                };
                let k = r.idx()?;
                let seeds = (0..k).map(|_| Ok((r.idx()?, r.idx()?))).collect::<Result<Vec<_>, Box<dyn Error>>>()?;
                calls.push((depth, eager, call, seeds));
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

/// A judgment's entries, rebuilt in a checker only as they're asked for: a scan first finds each
/// item and checks that every reference is to an earlier item, then an entry's terms are rebuilt
/// (each once) when it's needed. Seeding only the entries a call needs costs only those.
pub struct Lazy<'b, 't> {
    bytes: &'b [u8],
    names: Vec<usize>,
    levels: Vec<usize>,
    exprs: Vec<usize>,
    entries: Vec<usize>,
    name_ptr: Vec<Option<NamePtr<'t>>>,
    level_ptr: Vec<Option<LevelPtr<'t>>>,
    expr_ptr: Vec<Option<ExprPtr<'t>>>,
}

impl<'b, 't> Lazy<'b, 't> {
    /// Scan a judgment's items.
    pub fn new(header: &Header<'b>) -> Result<Self, Box<dyn Error>> {
        let bytes = header.items;
        let mut r = Reader { bytes };
        let (mut names, mut levels, mut exprs, mut entries) = (vec![0], vec![0], Vec::new(), Vec::new());
        let check = |i: usize, n: usize| if i < n { Ok(()) } else { Err::<(), Box<dyn Error>>("a reference to a later item".into()) };
        while !r.bytes.is_empty() {
            let at = bytes.len() - r.bytes.len();
            let tag = r.byte()?;
            let (nn, nl, ne) = (names.len(), levels.len(), exprs.len());
            match tag {
                1 => {
                    check(r.idx()?, nn)?;
                    r.bytes()?;
                    names.push(at);
                },
                2 => {
                    check(r.idx()?, nn)?;
                    r.u()?;
                    names.push(at);
                },
                3 => {
                    check(r.idx()?, nl)?;
                    levels.push(at);
                },
                4 | 5 => {
                    check(r.idx()?, nl)?;
                    check(r.idx()?, nl)?;
                    levels.push(at);
                },
                6 => {
                    check(r.idx()?, nn)?;
                    levels.push(at);
                },
                7 | 8 => {
                    r.bytes()?;
                    exprs.push(at);
                },
                9 => {
                    check(r.idx()?, nn)?;
                    for _ in 0..3 {
                        check(r.idx()?, ne)?;
                    }
                    r.byte()?;
                    exprs.push(at);
                },
                10 => {
                    check(r.idx()?, nn)?;
                    for _ in 0..r.idx()? {
                        check(r.idx()?, nl)?;
                    }
                    exprs.push(at);
                },
                11 => {
                    check(r.idx()?, ne)?;
                    check(r.idx()?, ne)?;
                    exprs.push(at);
                },
                12 | 13 => {
                    check(r.idx()?, nn)?;
                    style(r.byte()?)?;
                    check(r.idx()?, ne)?;
                    check(r.idx()?, ne)?;
                    exprs.push(at);
                },
                14 => {
                    check(r.idx()?, nn)?;
                    r.idx()?;
                    check(r.idx()?, ne)?;
                    exprs.push(at);
                },
                15 => {
                    check(r.idx()?, nl)?;
                    exprs.push(at);
                },
                16 => {
                    u16::try_from(r.u()?)?;
                    exprs.push(at);
                },
                17 => {
                    check(r.idx()?, nn)?;
                    style(r.byte()?)?;
                    check(r.idx()?, ne)?;
                    u16::try_from(r.u()?)?;
                    exprs.push(at);
                },
                33 => {
                    let cache = r.byte()?;
                    if cache > 6 {
                        return Err("bad cache".into());
                    }
                    check(r.idx()?, ne)?;
                    check(r.idx()?, ne)?;
                    if cache == 4 {
                        r.byte()?;
                    }
                    entries.push(at);
                },
                _ => return Err(format!("unexpected item tag {tag}").into()),
            }
        }
        let (n, l, e) = (names.len(), levels.len(), exprs.len());
        Ok(Lazy { bytes, names, levels, exprs, entries, name_ptr: vec![None; n], level_ptr: vec![None; l], expr_ptr: vec![None; e] })
    }

    /// How many entries it holds.
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    fn at(&self, offset: usize) -> Reader<'b> {
        Reader { bytes: &self.bytes[offset..] }
    }

    fn name(&mut self, tc: &mut TypeChecker<'_, 't, '_>, i: usize) -> Result<NamePtr<'t>, Box<dyn Error>> {
        if i == 0 {
            return Ok(tc.ctx.anonymous());
        }
        if let Some(n) = self.name_ptr[i] {
            return Ok(n);
        }
        let mut r = self.at(self.names[i]);
        let out = match r.byte()? {
            1 => {
                let pfx = r.idx()?;
                let s = r.str()?;
                let pfx = self.name(tc, pfx)?;
                let s = tc.ctx.alloc_string(CowStr::Owned(s));
                tc.ctx.str(pfx, s)
            },
            _ => {
                let pfx = r.idx()?;
                let k = r.u()?;
                let pfx = self.name(tc, pfx)?;
                tc.ctx.num(pfx, k)
            },
        };
        self.name_ptr[i] = Some(out);
        Ok(out)
    }

    fn level(&mut self, tc: &mut TypeChecker<'_, 't, '_>, i: usize) -> Result<LevelPtr<'t>, Box<dyn Error>> {
        if i == 0 {
            return Ok(tc.ctx.zero());
        }
        if let Some(l) = self.level_ptr[i] {
            return Ok(l);
        }
        let mut r = self.at(self.levels[i]);
        let out = match r.byte()? {
            3 => {
                let a = r.idx()?;
                let a = self.level(tc, a)?;
                tc.ctx.succ(a)
            },
            t @ (4 | 5) => {
                let (a, b) = (r.idx()?, r.idx()?);
                let (a, b) = (self.level(tc, a)?, self.level(tc, b)?);
                if t == 4 { tc.ctx.max(a, b) } else { tc.ctx.imax(a, b) }
            },
            _ => {
                let n = r.idx()?;
                let n = self.name(tc, n)?;
                tc.ctx.param(n)
            },
        };
        self.level_ptr[i] = Some(out);
        Ok(out)
    }

    /// Expression `i`'s children, as expression positions (names and levels are rebuilt as
    /// they're met).
    fn children(&self, i: usize) -> Result<Vec<usize>, Box<dyn Error>> {
        let mut r = self.at(self.exprs[i]);
        Ok(match r.byte()? {
            9 => {
                r.idx()?;
                vec![r.idx()?, r.idx()?, r.idx()?]
            },
            11 => vec![r.idx()?, r.idx()?],
            12 | 13 => {
                r.idx()?;
                r.byte()?;
                vec![r.idx()?, r.idx()?]
            },
            14 => {
                r.idx()?;
                r.idx()?;
                vec![r.idx()?]
            },
            17 => {
                r.idx()?;
                r.byte()?;
                vec![r.idx()?]
            },
            _ => vec![],
        })
    }

    /// Rebuild expression `i`, its children first, iteratively: terms can be deep.
    fn expr(&mut self, tc: &mut TypeChecker<'_, 't, '_>, root: usize) -> Result<ExprPtr<'t>, Box<dyn Error>> {
        let mut stack = vec![root];
        while let Some(&i) = stack.last() {
            if self.expr_ptr[i].is_some() {
                stack.pop();
                continue;
            }
            let missing: Vec<usize> = self.children(i)?.into_iter().filter(|&c| self.expr_ptr[c].is_none()).collect();
            if !missing.is_empty() {
                stack.extend(missing);
                continue;
            }
            stack.pop();
            let e = |l: &Self, c: usize| l.expr_ptr[c].unwrap();
            let mut r = self.at(self.exprs[i]);
            let out = match r.byte()? {
                7 => {
                    let b = r.bytes()?;
                    tc.ctx.mk_nat_lit_quick(num_bigint::BigUint::from_bytes_le(b)).ok_or("nat literals are off")?
                },
                8 => {
                    let s = r.str()?;
                    tc.ctx.mk_string_lit_quick(CowStr::Owned(s)).ok_or("string literals are off")?
                },
                9 => {
                    let n = r.idx()?;
                    let (ty, val, body) = (r.idx()?, r.idx()?, r.idx()?);
                    let nondep = r.byte()? != 0;
                    let n = self.name(tc, n)?;
                    tc.ctx.mk_let(n, e(self, ty), e(self, val), e(self, body), nondep)
                },
                10 => {
                    let n = r.idx()?;
                    let k = r.idx()?;
                    let ls = (0..k).map(|_| r.idx()).collect::<Result<Vec<_>, _>>()?;
                    let n = self.name(tc, n)?;
                    let ls = ls.into_iter().map(|l| self.level(tc, l)).collect::<Result<Vec<_>, _>>()?;
                    let ls = tc.ctx.alloc_levels_slice(&ls);
                    tc.ctx.mk_const(n, ls)
                },
                11 => {
                    let (f, a) = (r.idx()?, r.idx()?);
                    tc.ctx.mk_app(e(self, f), e(self, a))
                },
                t @ (12 | 13) => {
                    let n = r.idx()?;
                    let st = style(r.byte()?)?;
                    let (ty, body) = (r.idx()?, r.idx()?);
                    let n = self.name(tc, n)?;
                    if t == 12 { tc.ctx.mk_pi(n, st, e(self, ty), e(self, body)) } else { tc.ctx.mk_lambda(n, st, e(self, ty), e(self, body)) }
                },
                14 => {
                    let n = r.idx()?;
                    let k = r.idx()?;
                    let st = r.idx()?;
                    let n = self.name(tc, n)?;
                    tc.ctx.mk_proj(n, k, e(self, st))
                },
                15 => {
                    let l = r.idx()?;
                    let l = self.level(tc, l)?;
                    tc.ctx.mk_sort(l)
                },
                16 => {
                    let k = u16::try_from(r.u()?)?;
                    tc.ctx.mk_var(k)
                },
                _ => {
                    let n = r.idx()?;
                    let st = style(r.byte()?)?;
                    let ty = r.idx()?;
                    let level = u16::try_from(r.u()?)?;
                    let n = self.name(tc, n)?;
                    tc.ctx.remake_dbj_level(n, st, e(self, ty), level)
                },
            };
            self.expr_ptr[i] = Some(out);
        }
        Ok(self.expr_ptr[root].unwrap())
    }

    /// Entry `k`, rebuilt in `tc`.
    pub fn entry(&mut self, tc: &mut TypeChecker<'_, 't, '_>, k: usize) -> Result<Entry<'t>, Box<dyn Error>> {
        let offset = *self.entries.get(k).ok_or("no such entry")?;
        let mut r = self.at(offset);
        r.byte()?;
        let cache = r.byte()?;
        let (a, b) = (r.idx()?, r.idx()?);
        let eager = if cache == 4 { r.byte()? != 0 } else { false };
        let (a, b) = (self.expr(tc, a)?, self.expr(tc, b)?);
        Ok(match cache {
            0 => Entry::Infer(a, b),
            1 => Entry::InferOnly(a, b),
            2 => Entry::Whnf(a, b),
            3 => Entry::WhnfCore(a, b),
            4 => Entry::DefEqFail(a, b, eager),
            5 => Entry::DefEq(a, b),
            _ => Entry::CongrFail(a, b),
        })
    }
}

/// Rebuild a judgment's entries in `tc`.
pub fn entries<'t>(tc: &mut TypeChecker<'_, 't, '_>, header: &Header) -> Result<Vec<Entry<'t>>, Box<dyn Error>> {
    Ok(read(tc, header.items, true)?.0)
}

/// Rebuild a calls blob's calls in `tc` (see [`CallItem`]; eager mode is nanoda's while it
/// reduces `eagerReduce` terms).
pub fn calls<'t>(tc: &mut TypeChecker<'_, 't, '_>, blob: &[u8]) -> Result<Vec<CallItem<'t>>, Box<dyn Error>> {
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

/// The highest de Bruijn level of a local `e` mentions (through locals' types), memoized in
/// `memo` across calls; `None` if it mentions none.
fn max_level<'t>(tc: &TypeChecker<'_, 't, '_>, root: ExprPtr<'t>, memo: &mut FxHashMap<ExprPtr<'t>, Option<u16>>) -> Option<u16> {
    let mut stack = vec![(root, false)];
    while let Some((e, ready)) = stack.pop() {
        if memo.contains_key(&e) {
            continue;
        }
        let x = tc.ctx.read_expr(e);
        if !ready {
            if !tc.ctx.has_fvars(e) {
                memo.insert(e, None);
                continue;
            }
            stack.push((e, true));
            match x {
                Expr::App { fun, arg, .. } => stack.extend([(fun, false), (arg, false)]),
                Expr::Pi { binder_type, body, .. } | Expr::Lambda { binder_type, body, .. } => stack.extend([(binder_type, false), (body, false)]),
                Expr::Let { binder_type, val, body, .. } => stack.extend([(binder_type, false), (val, false), (body, false)]),
                Expr::Proj { structure, .. } => stack.push((structure, false)),
                Expr::Local { binder_type, .. } => stack.push((binder_type, false)),
                _ => {},
            }
            continue;
        }
        let m = |c: ExprPtr<'t>| memo.get(&c).copied().flatten();
        let level = match x {
            Expr::App { fun, arg, .. } => m(fun).max(m(arg)),
            Expr::Pi { binder_type, body, .. } | Expr::Lambda { binder_type, body, .. } => m(binder_type).max(m(body)),
            Expr::Let { binder_type, val, body, .. } => m(binder_type).max(m(val)).max(m(body)),
            Expr::Proj { structure, .. } => m(structure),
            Expr::Local { binder_type, id, .. } => {
                let own = match id {
                    FVarId::DbjLevel(l) => Some(l),
                    FVarId::Unique(_) => Some(u16::MAX),
                };
                own.max(m(binder_type))
            },
            _ => None,
        };
        memo.insert(e, level);
    }
    memo[&root]
}

/// Run `call` from de Bruijn depth `depth`, which must be above every local its inputs mention
/// (the locals it opens are then fresh), in eager mode or not. Type errors panic, as everywhere in
/// the kernel.
pub fn run<'t>(tc: &mut TypeChecker<'_, 't, '_>, depth: u16, eager: bool, call: Call<'t>) -> Result<Outcome<'t>, Box<dyn Error>> {
    run_memo(tc, depth, eager, call, &mut new_fx_hash_map())
}

/// [`run`], with the inputs' highest local levels memoized in `memo` (across an op's calls).
pub fn run_memo<'t>(
    tc: &mut TypeChecker<'_, 't, '_>,
    depth: u16,
    eager: bool,
    call: Call<'t>,
    memo: &mut FxHashMap<ExprPtr<'t>, Option<u16>>,
) -> Result<Outcome<'t>, Box<dyn Error>> {
    for e in call.inputs() {
        if max_level(tc, e, memo).is_some_and(|l| l >= depth) {
            return Err("a call's input mentions a local at or above its starting depth".into());
        }
    }
    let (before, eager_before) = (tc.ctx.dbj_level_counter, tc.ctx.eager_mode);
    tc.ctx.dbj_level_counter = depth;
    tc.ctx.eager_mode = eager;
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
    tc.ctx.eager_mode = eager_before;
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

/// A calls blob of `calls` (see [`CallItem`]).
pub fn write_calls<'t>(tc: &TypeChecker<'_, 't, '_>, calls: &[CallItem<'t>]) -> Vec<u8> {
    let mut w = Writer::new(tc, CALLS_MAGIC.to_vec());
    for (depth, eager, call, seeds) in calls {
        let (depth, eager, call) = (*depth, *eager, *call);
        let inputs: Vec<u64> = call.inputs().into_iter().map(|e| w.expr(e)).collect();
        let kind = match call {
            Call::Infer(_, true) => 0,
            Call::Infer(_, false) => 1,
            Call::Whnf(_) => 2,
            Call::DefEq(..) => 3,
            Call::LazyDelta(..) => 4,
        };
        w.out.extend_from_slice(&[32, kind | if eager { 0x80 } else { 0 }]);
        uvar(&mut w.out, u64::from(depth));
        for i in inputs {
            uvar(&mut w.out, i);
        }
        uvar(&mut w.out, seeds.len() as u64);
        for &(j, k) in seeds {
            uvar(&mut w.out, j as u64);
            uvar(&mut w.out, k as u64);
        }
    }
    w.out
}

/// The replay time of each call of the last judgment op checked, in nanoseconds, for planning
/// (see `crate::plan`).
#[cfg(feature = "trace")]
pub static CALL_TIMES: std::sync::Mutex<Vec<u64>> = std::sync::Mutex::new(Vec::new());

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
