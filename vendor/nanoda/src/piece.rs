//! A *piece*: one kernel call inside a declaration's check (an inference, a reduction to weak head
//! normal form, a definitional equality or a lazy delta step), with the cache entries it uses
//! that were made outside it, its *facts*, so that it can run on its own (research, for the
//! attested-memoization study in witness-lean's `docs/design/heavy-declarations.md`).
//!
//! A piece runs in its declaration's environment, against the declaration (as
//! `with_tc_and_declar` sets up), with the de Bruijn level counter at its starting depth. Its
//! terms, and its facts' keys and values, are rebuilt with the checker's own constructors, so
//! they're the same pointers the run builds, and cache lookups match.
//!
//! Format: [`PIECE_MAGIC`], then items, each a tag byte and its fields; `u` is an unsigned
//! LEB128 varint. Names count from 1 (0 is anonymous), levels from 1 (0 is zero), expressions
//! from 0, each in order of appearance; every reference is to an earlier item.
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
//! | 32 | the call | kind byte, starting depth `u`, `u` count, inputs `u`; then the result |
//! | 33 | a fact | cache byte, then its key and value |
//!
//! Call kinds: 0 infer (checking), 1 infer (inferring only), 2 whnf, 3 def_eq, 4 lazy delta step.
//! Results: 0 then an expression; 1 then a bool byte; 2 then two expressions (a lazy delta step
//! that ran out). Caches, as `TcCache`'s fields: 0 `infer_cache_check`, 1
//! `infer_cache_no_check`, 2 `whnf_cache`, 3 `whnf_no_unfolding_cache`, each a key and value
//! expression; 4 `defeq_fail_cache`, two expressions and a flag byte; 5 `eq_cache`, 6
//! `congr_fail_cache`, two expressions.
#[allow(unused_imports)]
use crate::prelude::*;
use crate::expr::{BinderStyle, Expr};
use crate::level::Level;
use crate::name::Name;
use crate::tc::{DeltaResult, InferFlag, TypeChecker};
use crate::util::{CowStr, ExprPtr, LevelPtr, NamePtr, SortedPair};
use core::error::Error;

pub const PIECE_MAGIC: &[u8] = b"LEANPCE\x01";

fn style_byte(s: BinderStyle) -> u8 {
    match s {
        BinderStyle::Default => 0,
        BinderStyle::Implicit => 1,
        BinderStyle::StrictImplicit => 2,
        BinderStyle::InstanceImplicit => 3,
    }
}

fn byte_style(b: u8) -> Result<BinderStyle, Box<dyn Error>> {
    Ok(match b {
        0 => BinderStyle::Default,
        1 => BinderStyle::Implicit,
        2 => BinderStyle::StrictImplicit,
        3 => BinderStyle::InstanceImplicit,
        _ => return Err("bad binder style".into()),
    })
}

struct Reader<'b> {
    bytes: &'b [u8],
}

impl<'b> Reader<'b> {
    fn byte(&mut self) -> Result<u8, Box<dyn Error>> {
        let (&b, rest) = self.bytes.split_first().ok_or("piece ends early")?;
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
    fn bytes(&mut self) -> Result<&'b [u8], Box<dyn Error>> {
        let n = self.idx()?;
        let (b, rest) = self.bytes.split_at_checked(n).ok_or("piece ends early")?;
        self.bytes = rest;
        Ok(b)
    }
    fn str(&mut self) -> Result<String, Box<dyn Error>> {
        Ok(core::str::from_utf8(self.bytes()?)?.to_string())
    }
}

/// What a piece run did.
pub struct PieceRun {
    /// Whether the call returned what it did inside the whole check.
    pub same: bool,
    pub names: usize,
    pub levels: usize,
    pub exprs: usize,
    pub facts: usize,
    /// Nanoseconds spent rebuilding terms and seeding caches, and running the call (when timed).
    pub load_ns: u128,
    pub run_ns: u128,
}

enum Outcome<'t> {
    Expr(ExprPtr<'t>),
    Bool(bool),
    Exhausted(ExprPtr<'t>, ExprPtr<'t>),
}

/// Rebuild the piece in `bytes` in `tc` (which must be set up for its declaration), seed its
/// caches with its facts, and run its call from its starting depth. `now` reads a clock in
/// nanoseconds (the PVM has none: pass `|| 0`).
pub fn run<'t>(tc: &mut TypeChecker<'_, 't, '_>, bytes: &[u8], now: impl Fn() -> u128) -> Result<PieceRun, Box<dyn Error>> {
    let t0 = now();
    let mut r = Reader { bytes: bytes.strip_prefix(PIECE_MAGIC).ok_or("not a piece")? };
    let ctx = &mut *tc.ctx;
    let mut names: Vec<NamePtr<'t>> = vec![ctx.anonymous()];
    let mut levels: Vec<LevelPtr<'t>> = vec![ctx.zero()];
    let mut exprs: Vec<ExprPtr<'t>> = Vec::new();
    let mut call = None;
    let mut facts = 0;
    while !r.bytes.is_empty() {
        let tag = r.byte()?;
        let n = |r: &mut Reader, v: &Vec<NamePtr<'t>>| -> Result<NamePtr<'t>, Box<dyn Error>> { Ok(*v.get(r.idx()?).ok_or("bad name")?) };
        let l = |r: &mut Reader, v: &Vec<LevelPtr<'t>>| -> Result<LevelPtr<'t>, Box<dyn Error>> { Ok(*v.get(r.idx()?).ok_or("bad level")?) };
        let e = |r: &mut Reader, v: &Vec<ExprPtr<'t>>| -> Result<ExprPtr<'t>, Box<dyn Error>> { Ok(*v.get(r.idx()?).ok_or("bad expression")?) };
        match tag {
            1 => {
                let pfx = n(&mut r, &names)?;
                let s = r.str()?;
                let s = ctx.alloc_string(CowStr::Owned(s));
                names.push(ctx.str(pfx, s));
            },
            2 => {
                let pfx = n(&mut r, &names)?;
                let k = r.u()?;
                names.push(ctx.num(pfx, k));
            },
            3 => {
                let a = l(&mut r, &levels)?;
                levels.push(ctx.succ(a));
            },
            4 | 5 => {
                let a = l(&mut r, &levels)?;
                let b = l(&mut r, &levels)?;
                levels.push(if tag == 4 { ctx.max(a, b) } else { ctx.imax(a, b) });
            },
            6 => {
                let a = n(&mut r, &names)?;
                levels.push(ctx.param(a));
            },
            7 => {
                let b = r.bytes()?;
                exprs.push(ctx.mk_nat_lit_quick(num_bigint::BigUint::from_bytes_le(b)).ok_or("nat literals off")?);
            },
            8 => {
                let s = r.str()?;
                exprs.push(ctx.mk_string_lit_quick(CowStr::Owned(s)).ok_or("string literals off")?);
            },
            9 => {
                let name = n(&mut r, &names)?;
                let (ty, val, body) = (e(&mut r, &exprs)?, e(&mut r, &exprs)?, e(&mut r, &exprs)?);
                let nondep = r.byte()? != 0;
                exprs.push(ctx.mk_let(name, ty, val, body, nondep));
            },
            10 => {
                let name = n(&mut r, &names)?;
                let k = r.idx()?;
                let ls = (0..k).map(|_| l(&mut r, &levels)).collect::<Result<Vec<_>, _>>()?;
                let ls = ctx.alloc_levels_slice(&ls);
                exprs.push(ctx.mk_const(name, ls));
            },
            11 => {
                let (f, a) = (e(&mut r, &exprs)?, e(&mut r, &exprs)?);
                exprs.push(ctx.mk_app(f, a));
            },
            12 | 13 => {
                let name = n(&mut r, &names)?;
                let style = byte_style(r.byte()?)?;
                let (ty, body) = (e(&mut r, &exprs)?, e(&mut r, &exprs)?);
                exprs.push(if tag == 12 { ctx.mk_pi(name, style, ty, body) } else { ctx.mk_lambda(name, style, ty, body) });
            },
            14 => {
                let name = n(&mut r, &names)?;
                let i = r.idx()?;
                let s = e(&mut r, &exprs)?;
                exprs.push(ctx.mk_proj(name, i, s));
            },
            15 => {
                let a = l(&mut r, &levels)?;
                exprs.push(ctx.mk_sort(a));
            },
            16 => {
                let i = u16::try_from(r.u()?)?;
                exprs.push(ctx.mk_var(i));
            },
            17 => {
                let name = n(&mut r, &names)?;
                let style = byte_style(r.byte()?)?;
                let ty = e(&mut r, &exprs)?;
                let level = u16::try_from(r.u()?)?;
                exprs.push(ctx.remake_dbj_level(name, style, ty, level));
            },
            32 => {
                let kind = r.byte()?;
                let depth = u16::try_from(r.u()?)?;
                let k = r.idx()?;
                let inputs = (0..k).map(|_| e(&mut r, &exprs)).collect::<Result<Vec<_>, _>>()?;
                let outcome = match r.byte()? {
                    0 => Outcome::Expr(e(&mut r, &exprs)?),
                    1 => Outcome::Bool(r.byte()? != 0),
                    2 => Outcome::Exhausted(e(&mut r, &exprs)?, e(&mut r, &exprs)?),
                    _ => return Err("bad result".into()),
                };
                call = Some((kind, depth, inputs, outcome));
            },
            33 => {
                let cache = r.byte()?;
                let c = &mut tc.tc_cache;
                match cache {
                    0..=3 => {
                        let (k, v) = (e(&mut r, &exprs)?, e(&mut r, &exprs)?);
                        match cache {
                            0 => c.infer_cache_check.insert(k, v),
                            1 => c.infer_cache_no_check.insert(k, v),
                            2 => c.whnf_cache.insert(k, v),
                            _ => c.whnf_no_unfolding_cache.insert(k, v),
                        };
                    },
                    4 => {
                        let (x, y) = (e(&mut r, &exprs)?, e(&mut r, &exprs)?);
                        let flag = r.byte()? != 0;
                        c.defeq_fail_cache.insert((x, y, flag));
                    },
                    5 | 6 => {
                        let (x, y) = (e(&mut r, &exprs)?, e(&mut r, &exprs)?);
                        if cache == 5 { c.eq_cache.insert(SortedPair::new(x, y)) } else { c.congr_fail_cache.insert(SortedPair::new(x, y)) };
                    },
                    _ => return Err("bad cache".into()),
                }
                facts += 1;
            },
            _ => return Err(format!("unknown piece item tag {tag}").into()),
        }
    }
    let (kind, depth, inputs, outcome) = call.ok_or("no call")?;
    let t1 = now();
    tc.ctx.dbj_level_counter = depth;
    let input = |i: usize| inputs.get(i).copied().ok_or("too few inputs");
    let same = match (kind, outcome) {
        (0 | 1, Outcome::Expr(want)) => {
            let flag = if kind == 0 { InferFlag::Check } else { InferFlag::InferOnly };
            tc.infer(input(0)?, flag) == want
        },
        (2, Outcome::Expr(want)) => tc.whnf(input(0)?) == want,
        (3, Outcome::Bool(want)) => tc.def_eq(input(0)?, input(1)?) == want,
        (4, outcome) => {
            let got = tc.lazy_delta_step(input(0)?, input(1)?);
            match (got, outcome) {
                (DeltaResult::FoundEqResult(a), Outcome::Bool(b)) => a == b,
                (DeltaResult::Exhausted(a, b), Outcome::Exhausted(c, d)) => (a, b) == (c, d),
                _ => false,
            }
        },
        _ => return Err("call and result don't match".into()),
    };
    let t2 = now();
    tc.ctx.dbj_level_counter = 0;
    Ok(PieceRun {
        same,
        names: names.len(),
        levels: levels.len(),
        exprs: exprs.len(),
        facts,
        load_ns: t1 - t0,
        run_ns: t2 - t1,
    })
}

/// Writing pieces, from inside a whole check (profiling builds only).
#[cfg(feature = "trace")]
pub(crate) mod write {
    use super::*;
    use crate::util::TcCache;
    use std::collections::HashMap;

    /// What the call returned.
    pub(crate) enum Returned<'t> {
        Expr(ExprPtr<'t>),
        Bool(bool),
        Delta(DeltaResult<'t>),
    }

    struct W<'a, 'x, 't, 'p> {
        tc: &'a TypeChecker<'x, 't, 'p>,
        out: Vec<u8>,
        names: HashMap<NamePtr<'t>, u64>,
        levels: HashMap<LevelPtr<'t>, u64>,
        exprs: HashMap<ExprPtr<'t>, u64>,
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

    impl<'t> W<'_, '_, 't, '_> {
        fn name(&mut self, n: NamePtr<'t>) -> u64 {
            if let Some(&i) = self.names.get(&n) {
                return i;
            }
            let i = match self.tc.ctx.read_name(n) {
                Name::Anon => 0,
                Name::Str(pfx, s, _) => {
                    let p = self.name(pfx);
                    let s = self.tc.ctx.read_string(s).to_string();
                    self.out.push(1);
                    uvar(&mut self.out, p);
                    uvar(&mut self.out, s.len() as u64);
                    self.out.extend_from_slice(s.as_bytes());
                    self.names.len() as u64 + 1
                },
                Name::Num(pfx, k, _) => {
                    let p = self.name(pfx);
                    self.out.push(2);
                    uvar(&mut self.out, p);
                    uvar(&mut self.out, k);
                    self.names.len() as u64 + 1
                },
            };
            if i != 0 {
                self.names.insert(n, i);
            }
            i
        }

        fn level(&mut self, l: LevelPtr<'t>) -> u64 {
            if let Some(&i) = self.levels.get(&l) {
                return i;
            }
            let i = match self.tc.ctx.read_level(l) {
                Level::Zero => return 0,
                Level::Succ(a, _) => {
                    let a = self.level(a);
                    self.out.push(3);
                    uvar(&mut self.out, a);
                    self.levels.len() as u64 + 1
                },
                Level::Max(a, b, _) | Level::IMax(a, b, _) => {
                    let tag = if matches!(self.tc.ctx.read_level(l), Level::Max(..)) { 4 } else { 5 };
                    let (a, b) = (self.level(a), self.level(b));
                    self.out.push(tag);
                    uvar(&mut self.out, a);
                    uvar(&mut self.out, b);
                    self.levels.len() as u64 + 1
                },
                Level::Param(n, _) => {
                    let n = self.name(n);
                    self.out.push(6);
                    uvar(&mut self.out, n);
                    self.levels.len() as u64 + 1
                },
            };
            self.levels.insert(l, i);
            i
        }

        /// Iteratively, children first: terms can be deep.
        fn expr(&mut self, root: ExprPtr<'t>) -> u64 {
            use Expr::*;
            let mut stack = vec![(root, false)];
            while let Some((e, ready)) = stack.pop() {
                if self.exprs.contains_key(&e) {
                    continue;
                }
                let x = self.tc.ctx.read_expr(e);
                if !ready {
                    stack.push((e, true));
                    match x {
                        App { fun, arg, .. } => stack.extend([(arg, false), (fun, false)]),
                        Pi { binder_type, body, .. } | Lambda { binder_type, body, .. } => stack.extend([(body, false), (binder_type, false)]),
                        Let { binder_type, val, body, .. } => stack.extend([(body, false), (val, false), (binder_type, false)]),
                        Proj { structure, .. } => stack.push((structure, false)),
                        Local { binder_type, .. } => stack.push((binder_type, false)),
                        _ => {},
                    }
                    continue;
                }
                let ix = |w: &Self, c: ExprPtr<'t>| w.exprs[&c];
                let mut item = Vec::new();
                match x {
                    NatLit { ptr, .. } => {
                        let b = self.tc.ctx.read_bignum(ptr).unwrap().to_bytes_le();
                        item.push(7);
                        uvar(&mut item, b.len() as u64);
                        item.extend_from_slice(&b);
                    },
                    StringLit { ptr, .. } => {
                        let s = self.tc.ctx.read_string(ptr).to_string();
                        item.push(8);
                        uvar(&mut item, s.len() as u64);
                        item.extend_from_slice(s.as_bytes());
                    },
                    Let { binder_name, binder_type, val, body, nondep, .. } => {
                        let n = self.name(binder_name);
                        item.push(9);
                        for v in [n, ix(self, binder_type), ix(self, val), ix(self, body)] {
                            uvar(&mut item, v);
                        }
                        item.push(u8::from(nondep));
                    },
                    Const { name, levels, .. } => {
                        let n = self.name(name);
                        let ls: Vec<u64> = self.tc.ctx.read_levels(levels).iter().map(|&l| self.level(l)).collect();
                        item.push(10);
                        uvar(&mut item, n);
                        uvar(&mut item, ls.len() as u64);
                        for l in ls {
                            uvar(&mut item, l);
                        }
                    },
                    App { fun, arg, .. } => {
                        item.push(11);
                        uvar(&mut item, ix(self, fun));
                        uvar(&mut item, ix(self, arg));
                    },
                    Pi { binder_name, binder_style, binder_type, body, .. } | Lambda { binder_name, binder_style, binder_type, body, .. } => {
                        let n = self.name(binder_name);
                        item.push(if matches!(x, Pi { .. }) { 12 } else { 13 });
                        uvar(&mut item, n);
                        item.push(style_byte(binder_style));
                        uvar(&mut item, ix(self, binder_type));
                        uvar(&mut item, ix(self, body));
                    },
                    Proj { ty_name, idx, structure, .. } => {
                        let n = self.name(ty_name);
                        item.push(14);
                        uvar(&mut item, n);
                        uvar(&mut item, idx as u64);
                        uvar(&mut item, ix(self, structure));
                    },
                    Sort { level, .. } => {
                        let l = self.level(level);
                        item.push(15);
                        uvar(&mut item, l);
                    },
                    Var { dbj_idx, .. } => {
                        item.push(16);
                        uvar(&mut item, u64::from(dbj_idx));
                    },
                    Local { binder_name, binder_style, binder_type, id, .. } => {
                        let crate::expr::FVarId::DbjLevel(level) = id else { panic!("a piece with a unique local") };
                        let n = self.name(binder_name);
                        item.push(17);
                        uvar(&mut item, n);
                        item.push(style_byte(binder_style));
                        uvar(&mut item, ix(self, binder_type));
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

    /// The piece for call `kind` (see the module docs) on `inputs`, from `depth`, which returned
    /// `result`, with the entries of `seed` as its facts.
    pub(crate) fn piece<'t>(
        tc: &TypeChecker<'_, 't, '_>,
        kind: u8,
        depth: u16,
        inputs: &[ExprPtr<'t>],
        result: Returned<'t>,
        seed: &TcCache<'t>,
    ) -> Vec<u8> {
        let mut w = W { tc, out: PIECE_MAGIC.to_vec(), names: HashMap::new(), levels: HashMap::new(), exprs: HashMap::new() };
        let fact = |w: &mut W<'_, '_, 't, '_>, cache: u8, es: &[ExprPtr<'t>], flag: Option<bool>| {
            let ix: Vec<u64> = es.iter().map(|&e| w.expr(e)).collect();
            w.out.push(33);
            w.out.push(cache);
            for i in ix {
                uvar(&mut w.out, i);
            }
            if let Some(f) = flag {
                w.out.push(u8::from(f));
            }
        };
        for (&k, &v) in &seed.infer_cache_check {
            fact(&mut w, 0, &[k, v], None);
        }
        for (&k, &v) in &seed.infer_cache_no_check {
            fact(&mut w, 1, &[k, v], None);
        }
        for (&k, &v) in &seed.whnf_cache {
            fact(&mut w, 2, &[k, v], None);
        }
        for (&k, &v) in &seed.whnf_no_unfolding_cache {
            fact(&mut w, 3, &[k, v], None);
        }
        for &(x, y, f) in &seed.defeq_fail_cache {
            fact(&mut w, 4, &[x, y], Some(f));
        }
        for p in &seed.eq_cache {
            fact(&mut w, 5, &[p.0, p.1], None);
        }
        for p in &seed.congr_fail_cache {
            fact(&mut w, 6, &[p.0, p.1], None);
        }
        let ins: Vec<u64> = inputs.iter().map(|&e| w.expr(e)).collect();
        let res: Vec<u8> = {
            let mut r = Vec::new();
            match result {
                Returned::Expr(e) => {
                    let i = w.expr(e);
                    r.push(0);
                    uvar(&mut r, i);
                },
                Returned::Bool(b) | Returned::Delta(DeltaResult::FoundEqResult(b)) => {
                    r.push(1);
                    r.push(u8::from(b));
                },
                Returned::Delta(DeltaResult::Exhausted(a, b)) => {
                    let (a, b) = (w.expr(a), w.expr(b));
                    r.push(2);
                    uvar(&mut r, a);
                    uvar(&mut r, b);
                },
            }
            r
        };
        w.out.push(32);
        w.out.push(kind);
        uvar(&mut w.out, u64::from(depth));
        uvar(&mut w.out, ins.len() as u64);
        for i in ins {
            uvar(&mut w.out, i);
        }
        w.out.extend_from_slice(&res);
        w.out
    }
}
