#[allow(unused_imports)]
use crate::prelude::*;
use crate::env::ReducibilityHint;
use crate::env::{ConstructorData, Declar, DeclarInfo, Env, InductiveData, RecRule, RecursorData};
use crate::expr::Expr;
use crate::util::{
    nat_div, nat_mod, nat_sub, nat_gcd, nat_land, nat_lor, 
    nat_xor, nat_shr, nat_shl, ExportFile, ExprPtr, LevelPtr, 
    LevelsPtr, NamePtr, TcCache, TcCtx, StringPtr, SortedPair
};
use core::error::Error;
use num_traits::pow::Pow;

use DeltaResult::*;
use Expr::*;
use InferFlag::*;

/// Communicates the result of lazy delta reduction during definitional equality
/// checking; if we can no longer unfold any definitions, and we weren't already
/// able to show that the expressions were equal using a cheap method, then we return
/// `Exhaused(x, y)`, and continue with more expensive checks. If we were able to cheaply
/// determine that two expressions are or are not equal, we return `FoundEqResult`
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum DeltaResult<'a> {
    FoundEqResult(bool),
    Exhausted(ExprPtr<'a>, ExprPtr<'a>),
}

/// An enum for type safety and convenience; used during nat literal reduction, and also for testing.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum NatBinOp {
    Add,
    Sub,
    Mul,
    Pow,
    Mod,
    Div,
    Beq,
    Ble,
    Gcd,
    LAnd,
    LOr,
    XOr,
    Shl,
    Shr,
}

/// A flag that accompanies calls to type inference; if the flag is `Check`,
/// we perform additional definitional equality checks (for example, the type of an
/// argument to a lambda is the same type as the binder in the labmda). These checks
/// are costly however, and in some cases we're using inference during reduction of
/// expressions we know to be well-typed, so we can pass the flag `InferOnly` to omit
/// these checks when they are not needed.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum InferFlag {
    InferOnly,
    Check,
}

pub struct TypeChecker<'x, 't, 'p> {
    pub(crate) ctx: &'x mut TcCtx<'t, 'p>,
    /// An immutable reference to an environment, which contains declarations and notation.
    /// To accommodate the temporary declarations created while checking nested inductives,
    /// the environment may have a temporary extension which also holds declarations, and
    /// is searched before the persistent environment.
    ///
    /// This is stored as a field in `TypeChecker` rather than being placed in `TcCtx` so
    /// that the borrow checker will allow us to mutably reference `TcCtx` while we have
    /// outstanding references to environment declarations. Rust can tell that borrows
    /// of different struct fields are exclusive, but it can't analyze what fields of a given
    /// field's type are being exclusively borrowed.
    pub(crate) env: &'x Env<'x, 't>,
    /// The caches for things like inference, reduction, and equality checking.
    pub(crate) tc_cache: TcCache<'t>,
    /// If this type checker is being used to check a simple declaration, this field will
    /// contain the universe parameters of that declaration. This is used in a couple of places
    /// to make sure that all of the universe paramters actually used in a declaration `d` are
    /// properly represented in the declaration's uparams info.
    pub(crate) declar_info: Option<DeclarInfo<'t>>,
}

impl<'p> ExportFile<'p> {
    /// The entry point for checking a declaration `d`.
    pub fn check_declar(&self, d: &Declar<'p>) {
        use Declar::*;
        match d {
            Axiom { .. } => self.with_tc_and_declar(*d.info(), |tc| tc.check_declar_info(d).unwrap()),
            Inductive(..) => self.check_inductive_declar(d),
            Quot { .. } => self.with_ctx(|ctx| crate::quot::check_quot(ctx, d)),
            Definition { val, .. } | Theorem { val, .. } | Opaque { val, .. } =>
                self.with_tc_and_declar(*d.info(), |tc| {
                    tc.check_declar_info(d).unwrap();
                    let inferred_type = tc.infer(*val, crate::tc::InferFlag::Check);
                    tc.assert_def_eq(inferred_type, d.info().ty);
                }),
            Constructor(ctor_data) => {
                self.with_tc_and_declar(*d.info(), |tc| tc.check_declar_info(d).unwrap());
                assert!(self.declars.get(&ctor_data.inductive_name).is_some());
            }
            Recursor(recursor_data) => {
                self.with_tc_and_declar(*d.info(), |tc| tc.check_declar_info(d).unwrap());
                match recursor_data.all_inductives.get(0) {
                    None => self.with_ctx(|ctx| {
                        panic!("Recursors must be derived from an associated inductive type, but recursor {:?} had none", ctx.debug_print(recursor_data.info.name))
                    }),
                    Some(ind_name) => match self.declars.get(ind_name) {
                        None => self.with_ctx(|ctx| {
                            panic!("Recursors must be derived from an associated inductive declaration. Inductive declaration {:?} does not exist", ctx.debug_print(*ind_name))
                        }),
                        Some(Inductive {..}) => (),
                        Some(_) => self.with_ctx(|ctx| {
                            panic!("Recursors must be derived from an associated inductive type. Declaration {:?} is not an inductive type", ctx.debug_print(*ind_name))
                        }),
                    }
                }
                let recursor_idx = self.declars.get_index_of(&recursor_data.info.name).unwrap();
                for ind_name in recursor_data.all_inductives.iter() {
                    match self.declars.get_index_of(ind_name) {
                        None => self.with_ctx(|ctx| {
                            panic!(
                                "Recursor {:?} references inductive declaration {:?} which does not exist.",
                                ctx.debug_print(recursor_data.info.name),
                                ctx.debug_print(*ind_name)
                            )
                        }),
                        Some(ind_idx) => if recursor_idx <= ind_idx {
                            self.with_ctx(|ctx| {
                                panic!(
                                    "Inductive declarations must be exported prior to any derived recursors. ({:?}, {}), ({:?}, {})",
                                    ctx.debug_print(recursor_data.info.name),
                                    recursor_idx,
                                    ctx.debug_print(*ind_name),
                                    ind_idx
                                )
                            })
                        } 
                    }
                }
            }
        }
    }

    /// Check all declarations in this export file using a single thread.
    pub(crate) fn check_all_declars_serial(&self) {
        for declar in self.declars.values() {
            self.check_declar(declar);
        }
    }

    /// Check all of the declarations in this export file on the specified number
    /// of threads (checking will be serial on the main thread is num_threads <= 1).
    pub fn check_all_declars(&self) {
        // No threads without std: always serial.
        self.check_all_declars_serial()
    }
}

impl<'x, 't: 'x, 'p: 't> TypeChecker<'x, 't, 'p> {
    pub fn new(dag: &'x mut TcCtx<'t, 'p>, env: &'x Env<'x, 't>, declar_info: Option<DeclarInfo<'t>>) -> Self {
        assert_eq!(dag.dbj_level_counter, 0);
        Self { ctx: dag, env, tc_cache: TcCache::new(), declar_info } 
    }

    /// Conduct the preliminary checks done on all declarations; a declaration
    /// must not contain duplicate universe parameters, mut not have free variables,
    /// and must have an ascribed type that is actually a type (`infer declaration.type` must
    /// be a sort).
    pub(crate) fn check_declar_info(&mut self, d: &Declar<'t>) -> Result<(), Box<dyn Error>> {
        let info = d.info();
        assert!(self.ctx.no_dupes_all_params(info.uparams));
        assert!(!self.ctx.has_fvars(info.ty));
        let inferred_type = self.infer(info.ty, Check);
        let sort = self.ensure_sort(inferred_type);

        // This is sort of a "soft" check in terms of soundness, but for theorems, ensure 
        // that they're propositions.
        if let Declar::Theorem {..} = d {
            if !self.ctx.is_zero(sort) {
                return Err(Box::<dyn Error>::from(format!("Theorem type for {:?} must be `Prop` (sort 0); found type {:?}",
                    self.ctx.debug_print(info.name),
                    self.ctx.debug_print(sort)
                )))
            }
        } 
        Ok(())
    }

    /// Infer a `Const` by retrieving its type from the environment, then substituting
    /// the universe parameters for the ones in the declaration we're checking.
    fn infer_const(&mut self, c_name: NamePtr<'t>, c_uparams: LevelsPtr<'t>, flag: InferFlag) -> ExprPtr<'t> {
        if let Some(declar_info) = self.env.get_declar(&c_name).map(|x| x.info()).cloned() {
            if let (Check, Some(this_declar_info)) = (flag, self.declar_info) {
                for c_uparam in self.ctx.read_levels(c_uparams).iter().copied() {
                    assert!(self.ctx.all_uparams_defined(c_uparam, this_declar_info.uparams))
                }
            }
            self.ctx.subst_declar_info_levels(declar_info, c_uparams)
        } else {
            if let Some(parent_declar_info) = self.declar_info {
                panic!("infer_const: declaration {:?} depends on {:?} which was not found in the environment", self.ctx.debug_print(parent_declar_info.name), self.ctx.debug_print(c_name))
            } else {
                panic!("infer_const: declaration {:?} was not found in the environment", self.ctx.debug_print(c_name))
            }
        }
    }

    /// Retrieve the recursor rule corresponding to the constructor used in the major premise.
    fn get_rec_rule(&self, rec_rules: &[RecRule<'t>], major_const: ExprPtr<'t>) -> Option<RecRule<'t>> {
        if let Const { name: major_ctor_name, .. } = self.ctx.read_expr(major_const) {
            for r @ RecRule { ctor_name, .. } in rec_rules.iter().copied() {
                if ctor_name == major_ctor_name {
                    return Some(r)
                }
            }
        }
        None
    }

    /// Expand `(x : Prod A B)` into `Prod.mk (Prod.fst x) (Prod.snd x)`
    fn expand_eta_struct_aux(&mut self, e_type: ExprPtr<'t>, e: ExprPtr<'t>) -> Option<ExprPtr<'t>> {
        // `c_name = Point`
        let (_f, c_name, c_levels, args) = self.ctx.unfold_const_apps(e_type)?;
        // `Point` declaration
        let InductiveData { all_ctor_names, .. } = self.env.get_structure(&c_name, false)?;
        // Name = `Point.mk`
        let ctor_name0 = all_ctor_names.get(0).copied()?;
        // Ctor data for `Point.mk`
        let ConstructorData { num_params, num_fields, .. } = self.env.get_constructor(&ctor_name0).unwrap();
        // Const { name := Point.mk, levels := .. }
        let mut out = self.ctx.mk_const(ctor_name0, c_levels);
        // apply the params taken from the inferred type
        // `Point.mk (A : Type) (B : Type)`
        for i in 0..((*num_params) as usize) {
            out = self.ctx.mk_app(out, args[i])
        }
        // for (a : A) and (b : B),
        // `Proj {idx := 0, struct := e}`
        // `Point.mk A B (Point.0 e) (Point.1 e)`
        for i in 0..((*num_fields) as usize) {
            let proj = self.ctx.mk_proj(c_name, i, e);
            out = self.ctx.mk_app(out, proj);
        }
        Some(out)
    }

    pub(crate) fn ensure_infers_as_sort(&mut self, e: ExprPtr<'t>) -> LevelPtr<'t> {
        let infd = self.infer(e, Check);
        self.ensure_sort(infd)
    }

    pub(crate) fn ensure_sort(&mut self, e: ExprPtr<'t>) -> LevelPtr<'t> {
        if let Sort { level, .. } = self.ctx.read_expr(e) {
            return level
        }
        let whnfd = self.whnf(e);
        match self.ctx.read_expr(whnfd) {
            Sort { level, .. } => level,
            _ => panic!("ensur_sort could not produce a sort"),
        }
    }

    fn ensure_pi(&mut self, e: ExprPtr<'t>) -> ExprPtr<'t> {
        if let Pi { .. } = self.ctx.read_expr(e) {
            return e
        }
        let whnfd = self.whnf(e);
        match self.ctx.read_expr(whnfd) {
            Pi { .. } => whnfd,
            _ => panic!("ensure_pi could not produce a pi"),
        }
    }

    pub(crate) fn infer_sort_of(&mut self, e: ExprPtr<'t>, flag: InferFlag) -> LevelPtr<'t> {
        let whnfd = self.infer_then_whnf(e, flag);
        match self.ctx.read_expr(whnfd) {
            Sort { level, .. } => level,
            _ => panic!("infer_sort_of could not infer a sort"),
        }
    }

    fn try_eta_struct(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> bool {
        matches!(self.try_eta_struct_aux(x, y), Some(true)) || matches!(self.try_eta_struct_aux(y, x), Some(true))
    }

    fn try_eta_struct_aux(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> Option<bool> {
        let (_, name, _, args) = self.ctx.unfold_const_apps(y)?;
        let ConstructorData { inductive_name, num_params, num_fields, .. } = self.env.get_constructor(&name)?;
        if args.len() == (*num_params + *num_fields) as usize && self.env.can_be_struct(inductive_name) {
            let (x_type, y_type) = (self.infer(x, InferOnly), self.infer(y, InferOnly));
            if self.def_eq(x_type, y_type) {
                for i in (*num_params as usize)..args.len() {
                    let proj = self.ctx.mk_proj(*inductive_name, i - *num_params as usize, x);
                    let rhs = args[i];
                    if !self.def_eq(proj, rhs) {
                        return None
                    }
                }
                return Some(true)
            }
        }
        None
    }

    fn str_lit_to_ctor_reducing(&mut self, x: StringPtr<'t>) -> Option<ExprPtr<'t>> {
        self.ctx.str_lit_to_constructor(x).map(|x| self.whnf(x))
    }

    fn try_string_lit_expansion_aux(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> Option<bool> {
        if let (StringLit { ptr, .. }, App { fun, .. }) = self.ctx.read_expr_pair(x, y) {
            if let Some((name, _levels)) = self.ctx.try_const_info(fun) {
                if name == self.ctx.export_file.name_cache.string_of_list? {
                    // levels should be empty
                    let lhs = self.str_lit_to_ctor_reducing(ptr)?;
                    return Some(self.def_eq(lhs, y))
                }
            }
        }
        None
    }

    fn try_string_lit_expansion(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> bool {
        if !self.ctx.export_file.config.string_extension {
            return false
        }
        matches!(self.try_string_lit_expansion_aux(x, y), Some(true))
            || matches!(self.try_string_lit_expansion_aux(y, x), Some(true))
    }

    // For structures that carry no additional information, elements with the same type are def_eq.
    fn def_eq_unit(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> Option<bool> {
        let x_ty = self.infer_then_whnf(x, InferOnly);
        let (_, name, _levels, _) = self.ctx.unfold_const_apps(x_ty)?;
        let InductiveData { all_ctor_names, .. } = self.env.get_structure(&name, false)?;
        let ctor_name = &all_ctor_names[0];
        let ctor = self.env.get_constructor(ctor_name)?;
        if ctor.num_fields != 0 {
            return None
        }
        let y_type = self.infer(y, InferOnly);
        Some(self.def_eq(x_ty, y_type))
    }

    fn do_nat_bin(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>, op: NatBinOp) -> Option<ExprPtr<'t>> {
        use NatBinOp::*;
        let x = self.whnf(x);
        let arg1 = self.ctx.get_bignum_from_expr(x)?;
        let y = self.whnf(y);
        let arg2 = self.ctx.get_bignum_from_expr(y)?;
        match op {
            Add => self.ctx.mk_nat_lit_quick(arg1 + arg2),
            Sub => self.ctx.mk_nat_lit_quick(nat_sub(arg1, arg2)),
            Mul => self.ctx.mk_nat_lit_quick(arg1 * arg2),
            Pow => self.ctx.mk_nat_lit_quick(arg1.pow(arg2)),
            Div => self.ctx.mk_nat_lit_quick(nat_div(arg1, arg2)),
            Mod => self.ctx.mk_nat_lit_quick(nat_mod(arg1, arg2)),
            Gcd => self.ctx.mk_nat_lit_quick(nat_gcd(&arg1, &arg2)),
            LAnd => self.ctx.mk_nat_lit_quick(nat_land(arg1, arg2)),
            LOr => self.ctx.mk_nat_lit_quick(nat_lor(arg1, arg2)),
            XOr => self.ctx.mk_nat_lit_quick(nat_xor(&arg1, &arg2)),
            Shl => self.ctx.mk_nat_lit_quick(nat_shl(arg1, arg2)),
            Shr => self.ctx.mk_nat_lit_quick(nat_shr(arg1, arg2)),
            Beq => self.ctx.bool_to_expr(arg1 == arg2),
            Ble => self.ctx.bool_to_expr(arg1 <= arg2),
        }
    }
    
    /// Try to reduce an expression `e` which is an application of `Nat.succ`,
    /// or an application of a supported binary operation. `e` must have no free
    /// variables.
    pub(crate) fn try_reduce_nat(&mut self, e: ExprPtr<'t>) -> Option<ExprPtr<'t>> {
        if !self.ctx.export_file.config.nat_extension {
            return None
        }
        let (f, args) = self.ctx.unfold_apps(e);
        let out = match (self.ctx.read_expr(f), args.as_slice()) {
            (Const { name, .. }, [arg]) if Some(name) == self.ctx.export_file.name_cache.nat_succ => {
                let v_expr = self.whnf(*arg);
                self.ctx.get_bignum_succ_from_expr(v_expr)
            }
            (Const { name, .. }, [arg1, arg2]) => {
                let op = if Some(name) == self.ctx.export_file.name_cache.nat_add {
                    NatBinOp::Add
                } else if Some(name) == self.ctx.export_file.name_cache.nat_sub {
                    NatBinOp::Sub
                } else if Some(name) == self.ctx.export_file.name_cache.nat_mul {
                    NatBinOp::Mul
                } else if Some(name) == self.ctx.export_file.name_cache.nat_pow {
                    NatBinOp::Pow
                } else if Some(name) == self.ctx.export_file.name_cache.nat_mod {
                    NatBinOp::Mod
                } else if Some(name) == self.ctx.export_file.name_cache.nat_div {
                    NatBinOp::Div
                } else if Some(name) == self.ctx.export_file.name_cache.nat_beq {
                    NatBinOp::Beq
                } else if Some(name) == self.ctx.export_file.name_cache.nat_ble {
                    NatBinOp::Ble
                } else if Some(name) == self.ctx.export_file.name_cache.nat_land {
                    NatBinOp::LAnd
                } else if Some(name) == self.ctx.export_file.name_cache.nat_lor {
                    NatBinOp::LOr
                } else if Some(name) == self.ctx.export_file.name_cache.nat_xor {
                    NatBinOp::XOr
                } else if Some(name) == self.ctx.export_file.name_cache.nat_gcd {
                    NatBinOp::Gcd
                } else if Some(name) == self.ctx.export_file.name_cache.nat_shl {
                    NatBinOp::Shl
                } else if Some(name) == self.ctx.export_file.name_cache.nat_shr {
                    NatBinOp::Shr
                } else {
                    return None
                };
                self.do_nat_bin(*arg1, *arg2, op)
            }
            _ => None,
        };
        out
    }

    fn reduce_proj(&mut self, idx: usize, structure: ExprPtr<'t>, cheap: bool) -> Option<ExprPtr<'t>> {
        let structure = if cheap { self.whnf_no_unfolding_cheap_proj(structure) } else { self.whnf(structure) };
        self.reduce_proj_core(idx, structure)
    }

    fn reduce_proj_core(&mut self, idx: usize, mut structure: ExprPtr<'t>) -> Option<ExprPtr<'t>> {
        if let StringLit { ptr, .. } = self.ctx.read_expr(structure) {
            if let Some(s) = self.str_lit_to_ctor_reducing(ptr) {
                structure = s;
            }
        }
        let (_, name, _, args) = self.ctx.unfold_const_apps(structure)?;
        let ConstructorData { num_params, .. } = self.env.get_constructor(&name)?;
        let i = (*num_params as usize) + idx;
        args.get(i).copied()
    }

    /// `x.i =?= y.i` by their structures, as the reference kernel's
    /// `lazy_delta_proj_reduction` (src/kernel/type_checker.cpp): lazy-delta
    /// steps on the two structures; once neither unfolds any further, project
    /// both and compare just the projected fields, and only if a side is not a
    /// constructor application compare the structures themselves.  Comparing the
    /// whole structures first would also compare (and evaluate) the fields the
    /// projection discards.
    fn lazy_delta_proj_reduction(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>, idx: usize) -> bool {
        match self.lazy_delta_step(x, y) {
            FoundEqResult(r) => r,
            Exhausted(x, y) => match (self.reduce_proj_core(idx, x), self.reduce_proj_core(idx, y)) {
                (Some(x_i), Some(y_i)) => self.def_eq(x_i, y_i),
                _ => self.def_eq(x, y),
            },
        }
    }

    pub(crate) fn infer_then_whnf(&mut self, e: ExprPtr<'t>, flag: InferFlag) -> ExprPtr<'t> {
        let ty = self.infer(e, flag);
        self.whnf(ty)
    }

    fn infer_proj(&mut self, ty_name: NamePtr<'t>, idx: usize, structure: ExprPtr<'t>, flag: InferFlag) -> ExprPtr<'t> {
        let structure_ty = self.infer_then_whnf(structure, flag);
        let structure_ty_may_be_prop = self.may_be_prop(structure_ty).0;
        let (_, struct_ty_name, struct_ty_levels, struct_ty_args) = self.ctx.unfold_const_apps(structure_ty).unwrap();

        let InductiveData { info: inductive_info, all_ctor_names, num_params, .. } =
            self.env.get_structure(&struct_ty_name, true).unwrap();
        if inductive_info.name != ty_name {
            panic!("Invalid projection: {:?} != {:?}", self.ctx.debug_print(inductive_info.name), self.ctx.debug_print(ty_name));
        }
        let ConstructorData { info: ctor_info, .. } = self.env.get_constructor(&all_ctor_names[0]).unwrap();
        let mut ctor_ty = self.ctx.subst_declar_info_levels(*ctor_info, struct_ty_levels);
        for i in 0..(*num_params) {
            ctor_ty = self.whnf(ctor_ty);
            match self.ctx.read_expr(ctor_ty) {
                Pi { body, .. } => {
                    ctor_ty = self.ctx.inst(body, &[struct_ty_args[i as usize]]);
                }
                _ => panic!("Ran out of param telescope"),
            }
        }
        for i in 0..idx {
            ctor_ty = self.whnf(ctor_ty);
            match self.ctx.read_expr(ctor_ty) {
                Pi { binder_type, body, .. } => {
                    if self.ctx.num_loose_bvars(body) != 0 {
                      if structure_ty_may_be_prop && !self.is_prop(binder_type).0 {
                          panic!("infer_proj prop")
                      }
                      let arg = self.ctx.mk_proj(inductive_info.name, i, structure);
                      ctor_ty = self.ctx.inst(body, &[arg]);
                    } else {
                      ctor_ty = body;
                    }
                }
                _ => panic!("Ran out of constructor telescope"),
            }
        }
        let reduced = self.whnf(ctor_ty);
        match self.ctx.read_expr(reduced) {
            Pi { binder_type, .. } => {
                if structure_ty_may_be_prop && !self.is_prop(binder_type).0 {
                    panic!("infer_proj prop")
                }
                binder_type
            }
            _ => panic!("Ran out of constructor telescope getting field"),
        }
    }

    pub(crate) fn infer(&mut self, e: ExprPtr<'t>, flag: InferFlag) -> ExprPtr<'t> {
        #[cfg(feature = "trace")]
        {
            let t = prof::enter(self, "infer");
            prof::piece_start(self, &t, &[e]);
            let r = self.infer_inner(e, flag);
            let cold = if prof::wants_cold(&t) {
                let saved = core::mem::replace(&mut self.tc_cache, TcCache::new());
                let c = prof::begin_cold(self);
                let _ = self.infer_inner(e, flag);
                let m = prof::end_cold(self, c);
                self.tc_cache = saved;
                Some(m)
            } else {
                None
            };
            if let Some((seed, n, warm_us)) = prof::seed(self, &t) {
                let saved = core::mem::replace(&mut self.tc_cache, seed);
                let c = prof::begin_cold(self);
                let r2 = self.infer_inner(e, flag);
                let m = prof::end_cold(self, c);
                self.tc_cache = saved;
                prof::replayed(self, &t, r2 == r, n, warm_us, m);
            }
            prof::piece_end(&t);
            prof::exit(self, t, &[e], cold);
            return r;
        }
        #[cfg(not(feature = "trace"))]
        self.infer_inner(e, flag)
    }

    fn infer_inner(&mut self, e: ExprPtr<'t>, flag: InferFlag) -> ExprPtr<'t> {
        if let Some(cached) = self.tc_cache.infer_cache_check.get(&e).copied() {
            #[cfg(feature = "trace")] prof::hit(0, &e);
            return cached
        }
        if flag == InferFlag::InferOnly {
            if let Some(cached) = self.tc_cache.infer_cache_no_check.get(&e).copied() {
                #[cfg(feature = "trace")] prof::hit(1, &e);
                return cached
            }
        }
        let r = match self.ctx.read_expr(e) {
            Local { binder_type, .. } => binder_type,
            Var { .. } => panic!("no loose bvars allowed in infer"),
            Sort { level, .. } => self.infer_sort(level, flag),
            App { .. } => self.infer_app(e, flag),
            Pi { .. } => self.infer_pi(e, flag),
            Lambda { .. } => self.infer_lambda(e, flag),
            Let { binder_type, val, body, .. } => self.infer_let(binder_type, val, body, flag),
            Const { name, levels, .. } => self.infer_const(name, levels, flag),
            Proj { ty_name, idx, structure, .. } => self.infer_proj(ty_name, idx, structure, flag),
            NatLit { .. } => {
                assert!(self.ctx.export_file.config.nat_extension);
                self.ctx.nat_type().unwrap()
            }
            StringLit { .. } => {
                assert!(self.ctx.export_file.config.string_extension);
                self.ctx.string_type().unwrap()
            }
        };
        match flag {
            InferFlag::InferOnly => {
                #[cfg(feature = "trace")] prof::ins(self, 1, &e, &[e, r]);
                self.tc_cache.infer_cache_no_check.insert(e, r);
            }
            InferFlag::Check => {
                #[cfg(feature = "trace")] prof::ins(self, 0, &e, &[e, r]);
                self.tc_cache.infer_cache_check.insert(e, r);
            }
        }
        r
    }

    fn infer_sort(&mut self, l: LevelPtr<'t>, flag: InferFlag) -> ExprPtr<'t> {
        if let (Check, Some(declar_info)) = (flag, self.declar_info) {
            assert!(self.ctx.all_uparams_defined(l, declar_info.uparams))
        }
        let out = self.ctx.succ(l);
        self.ctx.mk_sort(out)
    }

    fn infer_app(&mut self, e: ExprPtr<'t>, flag: InferFlag) -> ExprPtr<'t> {
        let (mut fun, mut args) = self.ctx.unfold_apps_stack(e);
        let mut ctx = Vec::new();
        fun = self.infer(fun, flag);
        while !args.is_empty() {
            match self.ctx.read_expr(fun) {
                Pi { binder_type, body, .. } => {
                    let arg = args.pop().unwrap();
                    if flag == Check {
                        let arg_type = self.infer(arg, flag);
                        let binder_type = self.ctx.inst(binder_type, ctx.as_slice());
                        let outer_scope_eager_setting = self.ctx.eager_mode;
                        if self.ctx.is_eager_reduce_app(arg) {
                            self.ctx.eager_mode = true;
                        }
                        // `arg_type` and `binder_type` get swapped here to accommodate the 
                        // eager reduction branch in `def_eq` being focused on reducing the lhs.
                        self.assert_def_eq(binder_type, arg_type);
                        // replace the outer scope's setting before next iteration
                        self.ctx.eager_mode = outer_scope_eager_setting;
                    }
                    ctx.push(arg);
                    fun = body;
                }
                _ => {
                    let as_pi = self.ctx.inst(fun, ctx.as_slice());
                    let as_pi = self.ensure_pi(as_pi);
                    match self.ctx.read_expr(as_pi) {
                        Pi { .. } => {
                            // Only clear what we just instantiated.
                            ctx.clear();
                            fun = as_pi;
                        }
                        _ => panic!(),
                    }
                }
            }
        }
        self.ctx.inst(fun, ctx.as_slice())
    }

    //fn infer_app(&mut self, e: ExprPtr<'t>, flag: InferFlag) -> ExprPtr<'t> {
    //    match self.ctx.read_expr(e) {
    //        App {fun, arg, ..} => {
    //            let fun_ty = self.infer_then_whnf(fun, flag);
    //            match self.ctx.read_expr(fun_ty) {
    //                Pi {binder_type, body, ..} => {
    //                    if flag == InferFlag::Check {
    //                        let arg_ty = self.infer(arg, flag);
    //                        let outer_scope_eager_setting = self.ctx.eager_mode;
    //                        if self.ctx.is_eager_reduce_app(arg) {
    //                            self.ctx.eager_mode = true;
    //                        }
    //                        self.assert_def_eq(binder_type, arg_ty);
    //                        self.ctx.eager_mode = outer_scope_eager_setting;
    //                    }
    //                    self.ctx.inst(body, &[arg])
    //                },
    //                _ => panic!()
    //            }
    //        },
    //        _ => panic!()
    //    }
    //}

    fn infer_lambda(&mut self, mut e: ExprPtr<'t>, flag: InferFlag) -> ExprPtr<'t> {
        let mut locals = Vec::new();
        let start_pos = self.ctx.dbj_level_counter;
        while let Lambda { binder_name, binder_style, binder_type, body, .. } = self.ctx.read_expr(e) {
            let binder_type = self.ctx.inst(binder_type, locals.as_slice());
            if let Check = flag {
                self.infer_sort_of(binder_type, flag);
            }

            let local = self.ctx.mk_dbj_level(binder_name, binder_style, binder_type);
            locals.push(local);
            e = body;
        }

        let instd = self.ctx.inst(e, locals.as_slice());
        let infd = self.infer(instd, flag);
        let mut abstrd = self.ctx.abstr_levels(infd, start_pos);
        while let Some(local) = locals.pop() {
            match self.ctx.read_expr(local) {
                Local { binder_name, binder_style, binder_type, .. } => {
                    self.ctx.replace_dbj_level(local);
                    let t = self.ctx.abstr_levels(binder_type, start_pos);
                    abstrd = self.ctx.mk_pi(binder_name, binder_style, t, abstrd);
                }
                _ => panic!(),
            }
        }
        abstrd
    }

    fn infer_pi(&mut self, mut e: ExprPtr<'t>, flag: InferFlag) -> ExprPtr<'t> {
        let mut universes = Vec::new();
        let mut locals = Vec::new();
        let c0 = self.ctx.dbj_level_counter;
        while let Pi { binder_name, binder_style, binder_type, body, .. } = self.ctx.read_expr(e) {
            let binder_type = self.ctx.inst(binder_type, locals.as_slice());
            let dom_univ = self.infer_sort_of(binder_type, flag);
            universes.push(dom_univ);
            locals.push(self.ctx.mk_dbj_level(binder_name, binder_style, binder_type));
            e = body;
        }
        let instd = self.ctx.inst(e, locals.as_slice());
        let mut infd = self.infer_sort_of(instd, flag);
        while let (Some(universe), Some(local)) = (universes.pop(), locals.pop()) {
            infd = self.ctx.imax(universe, infd);
            self.ctx.replace_dbj_level(local);
        }
        assert_eq!(c0, self.ctx.dbj_level_counter);
        self.ctx.mk_sort(infd)
    }

    fn infer_let(
        &mut self,
        binder_type: ExprPtr<'t>,
        val: ExprPtr<'t>,
        body: ExprPtr<'t>,
        flag: InferFlag,
    ) -> ExprPtr<'t> {
        if flag == Check {
            // The binder type has to be a type
            self.infer_sort_of(binder_type, flag);
            let val_ty = self.infer(val, flag);
            // assert that the type annotation of the let value is appropriate.
            self.assert_def_eq(val_ty, binder_type);
        }
        let body = self.ctx.inst(body, &[val]);
        self.infer(body, flag)
    }
    
    // Not well tested, used for introspection/debugging.
    #[allow(dead_code)]
    pub(crate) fn strong_reduce(&mut self, e: ExprPtr<'t>, reduce_types: bool, reduce_proofs: bool) -> ExprPtr<'t> {
        if (!reduce_types) || (!reduce_proofs) {
            let ty = self.infer(e, InferOnly);
            if !reduce_types && matches!(self.ctx.read_expr(ty), Sort {..}) {
                return e
            }
            if !reduce_proofs && self.is_prop(ty).0 {
                return e
            }
        }
        let e = self.whnf(e);
        if let Some(cached) = self.tc_cache.strong_cache.get(&(e, reduce_types, reduce_proofs)).copied() {
            return cached
        }

        let out = match self.ctx.read_expr(e) {
            Expr::App {fun, arg, ..} => {
                let f = self.strong_reduce(fun, reduce_types, reduce_proofs);
                let arg = self.strong_reduce(arg, reduce_types, reduce_proofs);
                self.ctx.mk_app(f, arg)
            }
            Expr::Lambda {binder_name, binder_style, binder_type, body, ..} => {
                let start_pos = self.ctx.dbj_level_counter;
                let local = self.ctx.mk_dbj_level(binder_name, binder_style, binder_type);
                let instd = self.ctx.inst(body, &[local]);
                let body = self.strong_reduce(instd, reduce_types, reduce_proofs);
                let abstrd = self.ctx.abstr_levels(body, start_pos);
                match self.ctx.read_expr(local) {
                    Local {binder_name, binder_style, binder_type, ..} => {
                        self.ctx.replace_dbj_level(local);
                        let t = self.ctx.abstr_levels(binder_type, start_pos);
                        self.ctx.mk_lambda(binder_name, binder_style, t, abstrd)
                    },
                    _ => panic!()
                }
            }
            Expr::Pi {binder_name, binder_style, binder_type, body, ..} => {
                let start_pos = self.ctx.dbj_level_counter;
                let local = self.ctx.mk_dbj_level(binder_name, binder_style, binder_type);
                let instd = self.ctx.inst(body, &[local]);
                let body = self.strong_reduce(instd, reduce_types, reduce_proofs);
                let abstrd = self.ctx.abstr_levels(body, start_pos);
                match self.ctx.read_expr(local) {
                    Local {binder_name, binder_style, binder_type, ..} => {
                        self.ctx.replace_dbj_level(local);
                        let t = self.ctx.abstr_levels(binder_type, start_pos);
                        self.ctx.mk_pi(binder_name, binder_style, t, abstrd)
                    },
                    _ => panic!()
                }
            }
            Expr::Proj {ty_name, idx, structure, ..} => {
                let structure = self.strong_reduce(structure, reduce_types, reduce_proofs);
                let x = self.ctx.mk_proj(ty_name, idx, structure);
                let y = self.whnf(x);
                if y != x {
                    self.strong_reduce(y, reduce_types, reduce_proofs)
                } else {
                    x
                }
                
            }
            _ => e
        };
        self.tc_cache.strong_cache.insert((e, reduce_types, reduce_proofs), out);
        out
    }

    pub fn whnf(&mut self, e: ExprPtr<'t>) -> ExprPtr<'t> {
        #[cfg(feature = "trace")]
        {
            // NANODA_FLUSH_EVERY=N: clear every cache each N calls, to measure what they save.
            use core::sync::atomic::{AtomicU64, Ordering};
            static CALLS: AtomicU64 = AtomicU64::new(0);
            static EVERY: std::sync::OnceLock<u64> = std::sync::OnceLock::new();
            let every = *EVERY.get_or_init(|| std::env::var("NANODA_FLUSH_EVERY").ok().and_then(|v| v.parse().ok()).unwrap_or(0));
            if every > 0 && CALLS.fetch_add(1, Ordering::Relaxed) % every == every - 1 {
                self.tc_cache = TcCache::new();
            }
        }
        #[cfg(feature = "trace")]
        {
            let t = prof::enter(self, "whnf");
            prof::piece_start(self, &t, &[e]);
            let r = self.whnf_inner(e);
            let cold = if prof::wants_cold(&t) {
                let saved = core::mem::replace(&mut self.tc_cache, TcCache::new());
                let c = prof::begin_cold(self);
                let _ = self.whnf_inner(e);
                let m = prof::end_cold(self, c);
                self.tc_cache = saved;
                Some(m)
            } else {
                None
            };
            if let Some((seed, n, warm_us)) = prof::seed(self, &t) {
                let saved = core::mem::replace(&mut self.tc_cache, seed);
                let c = prof::begin_cold(self);
                let r2 = self.whnf_inner(e);
                let m = prof::end_cold(self, c);
                self.tc_cache = saved;
                prof::replayed(self, &t, r2 == r, n, warm_us, m);
            }
            prof::piece_end(&t);
            prof::exit(self, t, &[e], cold);
            return r;
        }
        #[cfg(not(feature = "trace"))]
        self.whnf_inner(e)
    }

    fn whnf_inner(&mut self, e: ExprPtr<'t>) -> ExprPtr<'t> {
        if matches!(self.ctx.read_expr(e), NatLit { .. } | StringLit { .. }) {
            return e
        }
        if let Some(cached) = self.tc_cache.whnf_cache.get(&e).copied() {
            #[cfg(feature = "trace")] prof::hit(2, &e);
            return cached
        }
        let mut cursor = e;
        loop {
            let whnfd = self.whnf_no_unfolding(cursor);
            if let Some(reduce_nat_ok) = self.try_reduce_nat(whnfd) {
                cursor = reduce_nat_ok;
            } else if let Some(next_term) = self.unfold_def(whnfd) {
                cursor = next_term;
            } else {
                #[cfg(feature = "trace")] prof::ins(self, 2, &e, &[e, whnfd]);
                self.tc_cache.whnf_cache.insert(e, whnfd);
                return whnfd
            }
        }
    }

    fn whnf_no_unfolding_cheap_proj(&mut self, e: ExprPtr<'t>) -> ExprPtr<'t> { self.whnf_no_unfolding_aux(e, true) }

    pub fn whnf_no_unfolding(&mut self, e: ExprPtr<'t>) -> ExprPtr<'t> { self.whnf_no_unfolding_aux(e, false) }

    fn whnf_no_unfolding_aux(&mut self, e: ExprPtr<'t>, cheap_proj: bool) -> ExprPtr<'t> {
        if let Some(cached) = self.tc_cache.whnf_no_unfolding_cache.get(&e).copied() {
            #[cfg(feature = "trace")] prof::hit(3, &e);
            return cached
        }
        let (e_fun, args) = self.ctx.unfold_apps(e);
        let (should_cache, eprime) = match self.ctx.read_expr(e_fun) {
            Proj { idx, structure, .. } =>
                if let Some(e) = self.reduce_proj(idx, structure, cheap_proj) {
                    let e = self.ctx.foldl_apps(e, args.into_iter());
                    let e = self.whnf_no_unfolding_aux(e, cheap_proj);
                    (true, e)
                } else {
                    // No reduction: `e` is the application rebuilt, so skip rebuilding it.
                    (false, e)
                },
            Sort { level, .. } => {
                debug_assert!(args.is_empty());
                let level = self.ctx.simplify(level);
                (false, self.ctx.mk_sort(level))
            }
            Lambda { .. } if !args.is_empty() => {
                let (mut e, mut n_args) = (e_fun, 0usize);
                while let (Lambda { body, .. }, [_arg, _rest @ ..]) = (self.ctx.read_expr(e), &args[n_args..]) {
                    n_args += 1;
                    e = body;
                }
                e = self.ctx.inst(e, &args[..n_args]);
                e = self.ctx.foldl_apps(e, args.into_iter().skip(n_args));
                (true, self.whnf_no_unfolding_aux(e, cheap_proj))
            }
            Lambda { .. } => {
                debug_assert!(args.is_empty());
                (false, e)
            }
            Let { val, body, .. } => {
                let e = self.ctx.inst(body, &[val]);
                let e = self.ctx.foldl_apps(e, args.into_iter());
                (true, self.whnf_no_unfolding_aux(e, cheap_proj))
            }
            Const { name, levels, .. } =>
                if let Some(reduced) = self.reduce_quot(name, &args) {
                    (true, self.whnf_no_unfolding_aux(reduced, cheap_proj))
                } else if let Some(reduced) = self.reduce_rec(name, levels, &args) {
                    (true, self.whnf_no_unfolding_aux(reduced, cheap_proj))
                } else {
                    (false, e)
                },
            Var { .. } => panic!("Loose bvars are not allowed"),
            Pi { .. } => {
                debug_assert!(args.is_empty());
                (false, e_fun)
            }
            App { .. } => panic!(),
            Local { .. } | NatLit { .. } | StringLit { .. } => (false, e),
        };
        if should_cache && !cheap_proj {
            #[cfg(feature = "trace")] prof::ins(self, 3, &e, &[e, eprime]);
            self.tc_cache.whnf_no_unfolding_cache.insert(e, eprime);
        }
        eprime
    }

    fn def_eq_nat(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> Option<bool> {
        if self.ctx.is_nat_zero(x) && self.ctx.is_nat_zero(y) {
            return Some(true)
        }
        if let (NatLit { .. }, NatLit { .. }) = (self.ctx.read_expr(x), self.ctx.read_expr(y)) {
            assert!(self.ctx.export_file.config.nat_extension);
            return Some(x == y)
        }
        if let (Some(x_pred), Some(y_pred)) = (self.ctx.pred_of_nat_succ(x), self.ctx.pred_of_nat_succ(y)) {
            Some(self.def_eq(x_pred, y_pred))
        } else {
            None
        }
    }

    fn def_eq_binder_multi(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> Option<bool> {
        if matches!(self.ctx.read_expr_pair(x, y), (Pi { .. }, Pi { .. }) | (Lambda { .. }, Lambda { .. })) {
            self.def_eq_binder_aux(x, y)
        } else {
            None
        }
    }

    #[allow(unused_parens)]
    fn def_eq_binder_aux(&mut self, mut x: ExprPtr<'t>, mut y: ExprPtr<'t>) -> Option<bool> {
        let mut locals = Vec::new();
        while let (
            Pi { binder_name, binder_style, binder_type: t1, body: body1, .. },
            Pi { binder_type: t2, body: body2, .. },
        )
        | (
            Lambda { binder_name, binder_style, binder_type: t1, body: body1, .. },
            Lambda { binder_type: t2, body: body2, .. },
        ) = self.ctx.read_expr_pair(x, y)
        {
            let t1 = self.ctx.inst(t1, locals.as_slice());
            let t2 = self.ctx.inst(t2, locals.as_slice());
            if self.def_eq(t1, t2) {
                locals.push(self.ctx.mk_dbj_level(binder_name, binder_style, t1));
                x = body1;
                y = body2;
            } else {
                self.ctx.dbj_level_counter -= u16::try_from(locals.len()).unwrap();
                return Some(false)
            }
        }

        let x = self.ctx.inst(x, locals.as_slice());
        let y = self.ctx.inst(y, locals.as_slice());
        let r = self.def_eq(x, y);
        self.ctx.dbj_level_counter -= u16::try_from(locals.len()).unwrap();
        Some(r)
    }

    fn def_eq_proj(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> bool {
        match self.ctx.read_expr_pair(x, y) {
            (
                Proj { ty_name: ty_name_l, idx: idx_l, structure: structure_l, .. },
                Proj { ty_name: ty_name_r, idx: idx_r, structure: structure_r, .. }
            ) => ty_name_l == ty_name_r && idx_l == idx_r && self.lazy_delta_proj_reduction(structure_l, structure_r, idx_l),
            _ => false,
        }
    }

    fn def_eq_local(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> bool {
        match self.ctx.read_expr_pair(x, y) {
            (Local { id: x_id, binder_type: tx, .. }, Local { id: y_id, binder_type: ty, .. }) =>
                x_id == y_id && self.def_eq(tx, ty),
            _ => false,
        }
    }
    fn def_eq_const(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> bool {
        match self.ctx.read_expr_pair(x, y) {
            (Const { name: x_name, levels: x_levels, .. }, Const { name: y_name, levels: y_levels, .. }) =>
                x_name == y_name && self.ctx.eq_antisymm_many(x_levels, y_levels),
            _ => false,
        }
    }

    fn def_eq_app(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> bool {
        let (f1, args1) = self.ctx.unfold_apps(x);
        if args1.is_empty() {
            return false
        }

        let (f2, args2) = self.ctx.unfold_apps(y);
        if args2.is_empty() {
            return false
        }

        if args1.len() != args2.len() {
            return false
        }

        let args_eq = args1.into_iter().zip(args2).all(|(xx, yy)| self.def_eq(xx, yy));

        if !args_eq {
            return false
        }

        if !self.def_eq(f1, f2) {
            return false
        }
        true
    }

    pub fn assert_def_eq(&mut self, u: ExprPtr<'t>, v: ExprPtr<'t>) { assert!(self.def_eq(u, v)) }

    pub fn def_eq(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> bool {
        #[cfg(feature = "trace")]
        {
            let t = prof::enter(self, "def_eq");
            prof::piece_start(self, &t, &[x, y]);
            let r = self.def_eq_inner(x, y);
            let cold = if prof::wants_cold(&t) {
                let saved = core::mem::replace(&mut self.tc_cache, TcCache::new());
                let c = prof::begin_cold(self);
                let _ = self.def_eq_inner(x, y);
                let m = prof::end_cold(self, c);
                self.tc_cache = saved;
                Some(m)
            } else {
                None
            };
            if let Some((seed, n, warm_us)) = prof::seed(self, &t) {
                let saved = core::mem::replace(&mut self.tc_cache, seed);
                let c = prof::begin_cold(self);
                let r2 = self.def_eq_inner(x, y);
                let m = prof::end_cold(self, c);
                self.tc_cache = saved;
                prof::replayed(self, &t, r2 == r, n, warm_us, m);
            }
            prof::piece_end(&t);
            prof::exit(self, t, &[x, y], cold);
            return r;
        }
        #[cfg(not(feature = "trace"))]
        self.def_eq_inner(x, y)
    }

    fn def_eq_inner(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> bool {
        if let Some(easy) = self.def_eq_quick_check(x, y) {
            return easy
        }
        let defeq_fail_cache_key = (x, y, self.ctx.eager_mode);
        if self.tc_cache.defeq_fail_cache.contains(&defeq_fail_cache_key) {
            #[cfg(feature = "trace")] prof::hit(4, &defeq_fail_cache_key);
            return false
        }
        let x_n = self.whnf_no_unfolding_cheap_proj(x);
        let y_n = self.whnf_no_unfolding_cheap_proj(y);

        if ((!self.ctx.has_fvars(x_n)) || self.ctx.eager_mode) && Some(y_n) == self.ctx.c_bool_true() {
            let x_nn = self.whnf(x_n);
            if Some(x_nn) == self.ctx.c_bool_true() {
                return true
            }
        }

        if let Some(easy) = self.def_eq_quick_check(x_n, y_n) {
            return easy
        }

        let result = if let Some(short) = self.proof_irrel_eq(x_n, y_n) {
            short
        } else {
            match self.lazy_delta_step(x_n, y_n) {
                FoundEqResult(short) => short,
                Exhausted(x_n, y_n) => {
                    if self.def_eq_const(x_n, y_n) || self.def_eq_local(x_n, y_n) || self.def_eq_proj(x_n, y_n) {
                        true
                    } else {
                        let (xn0, yn0) = (x_n, y_n);
                        let (x_n, y_n) = (self.whnf_no_unfolding(xn0), self.whnf_no_unfolding(yn0));
                        if x_n != xn0 || y_n != yn0 {
                            self.def_eq(x_n, y_n)
                        } else {
                            self.def_eq_app(x_n, y_n)
                                || self.try_eta_expansion(x_n, y_n)
                                || self.try_eta_struct(x_n, y_n)
                                || self.try_string_lit_expansion(x_n, y_n)
                                || matches!(self.def_eq_unit(x_n, y_n), Some(true))
                        }
                    }
                }
            }
        };
        if result {
            #[cfg(feature = "trace")] prof::ins(self, 5, &SortedPair::new(x, y), &[x, y]);
            self.tc_cache.eq_cache.insert(SortedPair::new(x, y));
        } else {
            #[cfg(feature = "trace")] prof::ins(self, 4, &defeq_fail_cache_key, &[defeq_fail_cache_key.0, defeq_fail_cache_key.1]);
            self.tc_cache.defeq_fail_cache.insert(defeq_fail_cache_key);        
        }
        result
    }

    fn mk_nullary_ctor(&mut self, e: ExprPtr<'t>, num_params: usize) -> Option<ExprPtr<'t>> {
        let (_fun, name, levels, args) = self.ctx.unfold_const_apps(e)?;
        let InductiveData { all_ctor_names, .. } = self.env.get_inductive(&name)?;
        let ctor_name = all_ctor_names[0];
        let new_const = self.ctx.mk_const(ctor_name, levels);
        let args = args.into_iter().take(num_params);
        Some(self.ctx.foldl_apps(new_const, args))
    }

    fn to_ctor_when_k(
        &mut self,
        major: ExprPtr<'t>,
        rec: &RecursorData<'t>,
    ) -> Option<ExprPtr<'t>> {
        if !rec.is_k {
            return None
        }
        let major_ty = self.infer_then_whnf(major, InferOnly);
        let f = self.ctx.unfold_apps_fun(major_ty);
        match (self.ctx.read_expr(f), self.ctx.get_major_induct(rec)) {
            (Const { name, .. }, Some(n)) if name == n => {
                let new_ctor_app = self.mk_nullary_ctor(major_ty, rec.num_params as usize)?;
                // This sometimes has free variables.
                let new_type = self.infer(new_ctor_app, InferOnly);
                if self.def_eq(major_ty, new_type) {
                    Some(new_ctor_app)
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    fn is_ctor_app(&self, e: ExprPtr<'t>) -> Option<NamePtr<'t>> {
        if let Const { name, .. } = self.ctx.read_expr(self.ctx.unfold_apps_fun(e)) {
            if let Some(Declar::Constructor { .. }) = self.env.get_declar(&name) {
                return Some(name)
            }
        }
        None
    }

    fn iota_try_eta_struct(&mut self, ind_name: NamePtr<'t>, e: ExprPtr<'t>) -> ExprPtr<'t> {
        if (!self.env.can_be_struct(&ind_name)) || self.is_ctor_app(e).is_some() {
            e
        } else {
            let e_type = self.infer_then_whnf(e, InferOnly);
            let e_type_f = self.ctx.unfold_apps_fun(e_type);
            match self.ctx.read_expr(e_type_f) {
                Const { name, .. } if name == ind_name => {
                    // If it's a prop, return the original `e`
                    if self.may_be_prop(e_type).0 {
                        e
                    } else {
                        // if it's not a prop, try to eta expand
                        self.expand_eta_struct_aux(e_type, e).unwrap_or(e)
                    }
                }
                _ => e,
            }
        }
    }
    
    fn reduce_rec(
        &mut self,
        const_name: NamePtr<'t>,
        const_levels: LevelsPtr<'t>,
        args: &[ExprPtr<'t>],
    ) -> Option<ExprPtr<'t>> {
        let rec @ RecursorData { info, rec_rules, num_params, num_motives, num_minors, .. } =
            self.env.get_recursor(&const_name)?;
        let major = args.get(rec.major_idx()).copied()?;
        let major = self.to_ctor_when_k(major, rec).unwrap_or(major);
        let major = self.whnf(major);
        let major = match self.ctx.read_expr(major) {
            NatLit { ptr, .. } => self.ctx.nat_lit_to_constructor(ptr).unwrap_or(major),
            StringLit { ptr, .. } => self.str_lit_to_ctor_reducing(ptr).unwrap_or(major),
            _ => {
                let ind_rec_name_prefix = self.ctx.get_major_induct(rec).unwrap();
                self.iota_try_eta_struct(ind_rec_name_prefix, major)
            }
        };
        let (major_ctor, major_ctor_args) = self.ctx.unfold_apps(major);
        let rec_rule = self.get_rec_rule(rec_rules, major_ctor)?;

        // The number of parameters in the constructor is not necessarily
        // equal to the number of parameters in the recursor when we have
        // nested inductive types.
        let num_extra_params_to_major =
            major_ctor_args.len().checked_sub(rec_rule.ctor_telescope_size_wo_params as usize).unwrap();
        let major_ctor_args_wo_params = major_ctor_args.into_iter().skip(num_extra_params_to_major).collect::<Vec<_>>();
        let r = self.ctx.subst_expr_levels(rec_rule.val, info.uparams, const_levels);
        let r = self.ctx.foldl_apps(r, args.iter().copied().take((num_params + num_motives + num_minors) as usize));
        let r = self.ctx.foldl_apps(r, major_ctor_args_wo_params.into_iter());
        Some(self.ctx.foldl_apps(r, args.iter().skip(rec.major_idx() + 1).copied()))
    }

    pub fn reduce_quot(&mut self, c_name: NamePtr<'t>, args: &[ExprPtr<'t>]) -> Option<ExprPtr<'t>> {
        if !matches!(self.env.get_declar(&c_name), Some(Declar::Quot {..})) {
            return None
        }
        let (qmk, rest_idx) = if c_name == self.ctx.export_file.name_cache.quot_lift? {
            let qmk = args.get(5).copied()?;
            (self.whnf(qmk), 6)
        } else if c_name == self.ctx.export_file.name_cache.quot_ind? {
            let qmk = args.get(4).copied()?;
            (self.whnf(qmk), 5)
        } else {
            return None
        };
        {
            let (qmk_const, qmk_args) = self.ctx.unfold_apps(qmk);
            match self.ctx.read_expr(qmk_const) {
                Const { name, .. } if name == self.ctx.export_file.name_cache.quot_mk? && qmk_args.len() == 3 => (),
                _ => return None,
            };
        }
        let f = args.get(3).copied()?;
        let appd = match self.ctx.read_expr(qmk) {
            App { arg, .. } => self.ctx.mk_app(f, arg),
            _ => panic!("Quot iota"),
        };
        Some(self.ctx.foldl_apps(appd, args.iter().copied().skip(rest_idx)))
    }

    // We only need the name and reducibility from this.
    fn get_applied_def(&mut self, e: ExprPtr<'t>) -> Option<(NamePtr<'t>, ReducibilityHint)> {
        if let Const { name, .. } = self.ctx.read_expr(self.ctx.unfold_apps_fun(e)) {
            if let Some(Declar::Definition { info, hint, .. }) = self.env.get_declar(&name) {
                return Some((info.name, *hint))
            } else if let Some(Declar::Theorem { info, .. }) = self.env.get_declar(&name) {
                return Some((info.name, ReducibilityHint::Opaque))
            }
        }
        None
    }

    /// For an expression already known to be an applied definition, unfold
    /// the definition and perform cheap reduction on the unfolded result.
    fn delta(&mut self, e: ExprPtr<'t>) -> ExprPtr<'t> {
        let unfolded = self.unfold_def(e).unwrap();
        self.whnf_no_unfolding_cheap_proj(unfolded)
    }

    /// Try to unfold the base `Const` and re-fold applications, but don't
    /// do any further reduction.
    fn unfold_def(&mut self, e: ExprPtr<'t>) -> Option<ExprPtr<'t>> {
        #[cfg(feature = "trace")]
        prof::count_unfold(self, e);
        let (fun, args) = self.ctx.unfold_apps(e);
        let (name, levels) = self.ctx.try_const_info(fun)?;
        let (def_uparams, def_value) = self.env.get_declar_val(&name)?;
        if self.ctx.read_levels(levels).len() == self.ctx.read_levels(def_uparams).len() {
            let def_val = self.ctx.subst_expr_levels(def_value, def_uparams, levels);
            Some(self.ctx.foldl_apps(def_val, args.into_iter()))
        } else {
            None
        }
    }

    fn def_eq_sort(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> Option<bool> {
        match self.ctx.read_expr_pair(x, y) {
            (Sort { level: l, .. }, Sort { level: r, .. }) => Some(self.ctx.eq_antisymm(l, r)),
            _ => None,
        }
    }

    fn def_eq_quick_check(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> Option<bool> {
        if x == y {
            return Some(true)
        }
        if self.tc_cache.eq_cache.contains(&SortedPair::new(x, y)) {
            #[cfg(feature = "trace")] prof::hit(5, &SortedPair::new(x, y));
            return Some(true)
        }
        if self.ctx.alpha_eq(x, y) {
            #[cfg(feature = "trace")] prof::ins(self, 5, &SortedPair::new(x, y), &[x, y]);
            self.tc_cache.eq_cache.insert(SortedPair::new(x, y));
            return Some(true)
        }
        if let Some(r) = self.def_eq_sort(x, y) {
            return Some(r)
        }
        if let Some(r) = self.def_eq_binder_multi(x, y) {
            return Some(r)
        }
        None
    }

    fn failure_cache_contains(&self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> bool {
        let failed = self.tc_cache.congr_fail_cache.contains(&SortedPair::new(x, y));
        #[cfg(feature = "trace")]
        if failed {
            prof::hit(6, &SortedPair::new(x, y));
        }
        failed
    }

    fn failure_cache_insert(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) {
        #[cfg(feature = "trace")] prof::ins(self, 6, &SortedPair::new(x, y), &[x, y]);
        self.tc_cache.congr_fail_cache.insert(SortedPair::new(x, y));
    }

    fn try_eq_const_app(
        &mut self,
        x: ExprPtr<'t>,
        x_defname: NamePtr<'t>,
        x_hint: ReducibilityHint,
        y: ExprPtr<'t>,
        y_defname: NamePtr<'t>,
        y_hint: ReducibilityHint,
    ) -> Option<DeltaResult<'t>> {
        if x_defname != y_defname {
            return None
        }
        if !matches!((x_hint, y_hint), (ReducibilityHint::Regular(..), ReducibilityHint::Regular(..))) {
            return None
        }
        if x_hint != y_hint {
            return None
        }
        if self.failure_cache_contains(x, y) {
            return None
        }

        match self.ctx.read_expr_pair(x, y) {
            (App { .. }, App { .. }) if (x_defname == y_defname) => {
                let (l_fun, l_args) = self.ctx.unfold_apps(x);
                let (r_fun, r_args) = self.ctx.unfold_apps(y);
                match self.ctx.read_expr_pair(l_fun, r_fun) {
                    (Const { levels: l_levels, .. }, Const { levels: r_levels, .. })
                        if l_args.len() == r_args.len()
                            && !self.failure_cache_contains(x, y)
                            && l_args.iter().copied().zip(r_args.iter().copied()).rev().all(|(x, y)| self.def_eq(x, y))
                            && self.ctx.eq_antisymm_many(l_levels, r_levels) =>
                        Some(FoundEqResult(true)),
                    (Const { .. }, Const { .. }) => {
                        self.failure_cache_insert(x, y);
                        None
                    }
                    _ => panic!(),
                }
            }
            _ => None,
        }
    }

    fn try_unfold_proj_app(&mut self, e: ExprPtr<'t>) -> Option<ExprPtr<'t>> {
        if let Proj { .. } = self.ctx.read_expr(self.ctx.unfold_apps_fun(e)) {
            let eprime = self.whnf_no_unfolding(e);
            if eprime != e {
                return Some(eprime)
            }
        }
        None
    }

    fn delta_try_nat(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> Option<DeltaResult<'t>> {
        if let Some(short) = self.def_eq_nat(x, y) {
            return Some(DeltaResult::FoundEqResult(short))
        }
        if (!self.ctx.has_fvars(x) && !self.ctx.has_fvars(y)) || self.ctx.eager_mode {
            if let Some(xprime) = self.try_reduce_nat(x) {
                return Some(DeltaResult::FoundEqResult(self.def_eq(xprime, y)))
            } else if let Some(yprime) = self.try_reduce_nat(y) {
                return Some(DeltaResult::FoundEqResult(self.def_eq(x, yprime)))
            }
        }
        None
    }

    /// If `x` and/or `y` are definitions that need to be unfolded, try to lazily unfold
    /// the "higher" definition to bring it closer to the lower one. Also try to efficiently
    /// check for congruence if `x` and `y` apply the same definitions.
    ///
    /// After each reduction, check whether we can show definitional equality without having
    /// to continue unfolding.
    fn lazy_delta_step(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> DeltaResult<'t> {
        #[cfg(feature = "trace")]
        {
            let t = prof::enter(self, "lazy_delta");
            prof::piece_start(self, &t, &[x, y]);
            let r = self.lazy_delta_step_inner(x, y);
            let cold = if prof::wants_cold(&t) {
                let saved = core::mem::replace(&mut self.tc_cache, TcCache::new());
                let c = prof::begin_cold(self);
                let _ = self.lazy_delta_step_inner(x, y);
                let m = prof::end_cold(self, c);
                self.tc_cache = saved;
                Some(m)
            } else {
                None
            };
            if let Some((seed, n, warm_us)) = prof::seed(self, &t) {
                let saved = core::mem::replace(&mut self.tc_cache, seed);
                let c = prof::begin_cold(self);
                let r2 = self.lazy_delta_step_inner(x, y);
                let m = prof::end_cold(self, c);
                self.tc_cache = saved;
                prof::replayed(self, &t, r2 == r, n, warm_us, m);
            }
            prof::piece_end(&t);
            prof::exit(self, t, &[x, y], cold);
            return r;
        }
        #[cfg(not(feature = "trace"))]
        self.lazy_delta_step_inner(x, y)
    }

    fn lazy_delta_step_inner(&mut self, mut x: ExprPtr<'t>, mut y: ExprPtr<'t>) -> DeltaResult<'t> {
        loop {
            if let Some(r) = self.delta_try_nat(x, y) {
                return r
            }
            let (r1, r2) = (self.get_applied_def(x), self.get_applied_def(y));
            match (r1, r2) {
                (None, None) => return Exhausted(x, y),
                (Some(..), None) =>
                    if let Some(yprime) = self.try_unfold_proj_app(y) {
                        y = yprime;
                    } else {
                        x = self.delta(x);
                    },
                (None, Some(..)) =>
                    if let Some(xprime) = self.try_unfold_proj_app(x) {
                        x = xprime;
                    } else {
                        y = self.delta(y);
                    },
                (Some((_, l_hint)), Some((_, r_hint))) if l_hint.is_lt(&r_hint) => {
                    y = self.delta(y);
                }
                (Some((_, l_hint)), Some((_, r_hint))) if r_hint.is_lt(&l_hint) => {
                    x = self.delta(x);
                }
                (Some((x_name, l_hint)), Some((y_name, r_hint))) => {
                    if let Some(r) = self.try_eq_const_app(x, x_name, l_hint, y, y_name, r_hint) {
                        return r
                    } else {
                        x = self.delta(x);
                        y = self.delta(y);
                    }
                }
            }
            if let Some(quick_result) = self.def_eq_quick_check(x, y) {
                return FoundEqResult(quick_result)
            }
        }
    }

    pub fn is_prop(&mut self, e: ExprPtr<'t>) -> (bool, ExprPtr<'t>) {
        let ty = self.infer_then_whnf(e, InferOnly);
        match self.ctx.read_expr(ty) {
            Sort { level, .. } => (self.ctx.is_zero(level), ty),
            _ => panic!("expected a sort")
        }
    }

    pub fn may_be_prop(&mut self, e: ExprPtr<'t>) -> (bool, ExprPtr<'t>) {
        let ty = self.infer_then_whnf(e, InferOnly);
        match self.ctx.read_expr(ty) {
            Sort { level, .. } => (self.ctx.may_be_prop(level), ty),
            _ => panic!("expected a sort")
        }
    }

    pub fn is_proof(&mut self, e: ExprPtr<'t>) -> (bool, ExprPtr<'t>) {
        let infd = self.infer(e, InferOnly);
        (self.is_prop(infd).0, infd)
    }

    fn proof_irrel_eq(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> Option<bool> {
        match self.is_proof(x) {
            (false, _) => None,
            (true, l_type) => {
                let r_type = self.infer(y, InferOnly);
                Some(self.def_eq(l_type, r_type))
            }
        }
    }

    fn try_eta_expansion(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> bool {
        self.try_eta_expansion_aux(x, y) || self.try_eta_expansion_aux(y, x)
    }

    fn try_eta_expansion_aux(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> bool {
        if let Lambda { .. } = self.ctx.read_expr(x) {
            let y_ty = self.infer_then_whnf(y, InferOnly);
            if let Pi { binder_name, binder_type, binder_style, .. } = self.ctx.read_expr(y_ty) {
                let v0 = self.ctx.mk_var(0);
                let new_body = self.ctx.mk_app(y, v0);
                let new_lambda = self.ctx.mk_lambda(binder_name, binder_style, binder_type, new_body);
                return self.def_eq(x, new_lambda)
            }
        }
        false
    }
}

#[cfg(feature = "trace")]
impl<'x, 't, 'p> TypeChecker<'x, 't, 'p> {
    /// After a declaration slower than 100 ms: what its checker built, by structure.
    pub(crate) fn mem_report(&self, elapsed: core::time::Duration) {
        if elapsed.as_millis() < 100 {
            return;
        }
        prof::summary();
        prof::fact_report();
        let dag = &*self.ctx.dag;
        let c = &self.tc_cache;
        let e = core::mem::size_of::<crate::expr::Expr<'t>>() + 16;
        let map = 2 * core::mem::size_of::<usize>() + 8;
        let exprs = dag.exprs.len();
        let caches = [
            ("infer_check", c.infer_cache_check.len()),
            ("infer_no_check", c.infer_cache_no_check.len()),
            ("whnf", c.whnf_cache.len()),
            ("whnf_no_unfolding", c.whnf_no_unfolding_cache.len()),
            ("eq", c.eq_cache.len()),
            ("congr_fail", c.congr_fail_cache.len()),
            ("defeq_fail", c.defeq_fail_cache.len()),
        ];
        let entries: usize = caches.iter().map(|(_, n)| n).sum();
        std::eprintln!(
            "nanoda mem: {:?}: {} exprs (~{} MiB), {} levels, {} names; caches {} entries (~{} MiB): {}",
            elapsed,
            exprs,
            exprs * e >> 20,
            dag.levels.len(),
            dag.names.len(),
            entries,
            entries * (map + 8) >> 20,
            caches.iter().map(|(k, n)| std::format!("{k} {n}")).collect::<Vec<_>>().join(", ")
        );
    }
}

/// Where a check's time goes (`trace` builds only): calls of infer, whnf, def_eq and the lazy
/// delta step slower than NANODA_PROF_MS (default 10), as a tree printed children first, and
/// how often each definition was unfolded.
#[cfg(feature = "trace")]
pub(crate) mod prof {
    use super::TypeChecker;
    use crate::util::ExprPtr;
    use std::cell::RefCell;
    use std::collections::HashMap;
    use std::string::String;
    use std::time::Instant;

    std::thread_local! {
        static DEPTH: RefCell<usize> = const { RefCell::new(0) };
        static UNFOLDS: RefCell<HashMap<String, u64>> = RefCell::new(HashMap::new());
        static CALLS: RefCell<HashMap<&'static str, (u64, u128)>> = RefCell::new(HashMap::new());
    }

    fn threshold() -> u128 {
        static T: std::sync::OnceLock<u128> = std::sync::OnceLock::new();
        *T.get_or_init(|| std::env::var("NANODA_PROF_MS").ok().and_then(|v| v.parse().ok()).unwrap_or(10))
    }

    pub(crate) struct Entry {
        name: &'static str,
        start: Instant,
        exprs: usize,
        depth: usize,
        idx: u64,
        cold: bool,
        /// Total cold re-run time so far, at entry: what of the elapsed time wasn't this call's.
        cold_before: u128,
    }

    std::thread_local! {
        /// Inside a cold re-run: no logging, no nested re-runs.
        static COLD: RefCell<bool> = const { RefCell::new(false) };
        static INDEX: RefCell<u64> = const { RefCell::new(0) };
        static COLD_US: RefCell<u128> = const { RefCell::new(0) };
    }

    pub(crate) fn enter(tc: &TypeChecker<'_, '_, '_>, name: &'static str) -> Entry {
        let depth = DEPTH.with(|d| {
            let mut d = d.borrow_mut();
            *d += 1;
            *d - 1
        });
        let cold = COLD.with(|c| *c.borrow());
        let idx = INDEX.with(|i| {
            let mut i = i.borrow_mut();
            if !cold {
                *i += 1;
            }
            *i
        });
        let cold_before = COLD_US.with(|c| *c.borrow());
        Entry { name, start: Instant::now(), exprs: tc.ctx.dag.exprs.len(), depth, idx, cold, cold_before }
    }

    std::thread_local! {
        /// Each cache entry's key, hashed, with the call index it was created at; and every hit,
        /// as (call index of the hit, call index the entry was created at).
        static CREATED: RefCell<HashMap<u64, u64>> = RefCell::new(HashMap::new());
        static HITS: RefCell<std::vec::Vec<(u64, u64)>> = const { RefCell::new(std::vec::Vec::new()) };
        /// Every call's (index, last index in its subtree, warm µs), for NANODA_SPANS.
        static SPANS: RefCell<std::vec::Vec<(u64, u64, u64)>> = const { RefCell::new(std::vec::Vec::new()) };
    }

    fn key<K: core::hash::Hash>(cache: u8, k: &K) -> u64 {
        use core::hash::{Hash, Hasher};
        let mut h = std::collections::hash_map::DefaultHasher::new();
        cache.hash(&mut h);
        k.hash(&mut h);
        h.finish()
    }

    fn now() -> u64 {
        INDEX.with(|i| *i.borrow())
    }

    std::thread_local! {
        /// NANODA_PIECES: each piece's call index and the creation indices of the entries it
        /// needs; and, for each needed entry, the ids of the nodes its terms reach.
        static PIECES: RefCell<Option<std::vec::Vec<std::vec::Vec<u64>>>> = const { RefCell::new(None) };
        static NEEDED: RefCell<std::collections::HashSet<u64>> = RefCell::new(std::collections::HashSet::new());
        static FACTS: RefCell<HashMap<u64, std::vec::Vec<u64>>> = RefCell::new(HashMap::new());
        /// Whether a needed entry's terms mention a local variable (aren't closed).
        static OPEN: RefCell<HashMap<u64, bool>> = RefCell::new(HashMap::new());
        /// The locals each needed entry's terms reach; the piece being run, with its inputs'
        /// locals; and (outside hits checked, facts with a local outside the piece's inputs).
        static FACT_LOCALS: RefCell<HashMap<u64, std::vec::Vec<(u64, u16)>>> = RefCell::new(HashMap::new());
        /// The piece being run: its start, its inputs' locals, and the live local at each level.
        static ACTIVE: RefCell<Option<(u64, std::collections::HashSet<u64>, std::vec::Vec<u64>)>> = const { RefCell::new(None) };
        /// Outside hits in pieces, and of their facts' locals: [input, live context, made inside, dead, unique].
        static SCOPE: RefCell<(u64, [u64; 5], [std::collections::HashSet<u64>; 5])> = RefCell::new((0, [0; 5], Default::default()));
        static STARTS: RefCell<std::collections::HashSet<u64>> = RefCell::new(std::collections::HashSet::new());
    }

    /// The ids of the locals `roots` reach, through locals' types.
    fn locals<'t>(tc: &TypeChecker<'_, 't, '_>, roots: &[ExprPtr<'t>]) -> std::vec::Vec<(u64, u16)> {
        use crate::expr::Expr::*;
        let mut seen = std::collections::HashSet::new();
        let mut out = std::vec::Vec::new();
        let mut stack: std::vec::Vec<ExprPtr<'t>> = roots.to_vec();
        while let Some(e) = stack.pop() {
            if !seen.insert(e) {
                continue;
            }
            match tc.ctx.read_expr(e) {
                App { fun, arg, .. } => stack.extend([fun, arg]),
                Pi { binder_type, body, .. } | Lambda { binder_type, body, .. } => stack.extend([binder_type, body]),
                Let { binder_type, val, body, .. } => stack.extend([binder_type, val, body]),
                Proj { structure, .. } => stack.push(structure),
                Local { binder_type, id, .. } => {
                    let level = match id { crate::expr::FVarId::DbjLevel(l) => l, _ => u16::MAX };
                    out.push((node_id(e), level));
                    stack.push(binder_type)
                },
                _ => {},
            }
        }
        out
    }

    pub(crate) fn piece_start<'t>(tc: &TypeChecker<'_, 't, '_>, e: &Entry, terms: &[ExprPtr<'t>]) {
        if e.cold {
            return;
        }
        load_pieces();
        if STARTS.with(|s| s.borrow().contains(&e.idx)) {
            let ls = locals(tc, terms).into_iter().map(|(id, _)| id).collect();
            let live = crate::util::LIVE.with(|l| l.borrow()[..usize::from(tc.ctx.dbj_level_counter)].to_vec());
            ACTIVE.with(|a| *a.borrow_mut() = Some((e.idx, ls, live)));
        }
    }

    /// NANODA_REPLAY: for a piece's call, a cache seeded with the entries created in the calls
    /// the piece needs (and how many), plus the piece's warm time so far.
    pub(crate) fn seed<'t>(tc: &TypeChecker<'_, 't, '_>, e: &Entry) -> Option<(crate::util::TcCache<'t>, usize, u128)> {
        static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
        if e.cold || !*ON.get_or_init(|| std::env::var("NANODA_REPLAY").is_ok()) || !STARTS.with(|s| s.borrow().contains(&e.idx)) {
            return None;
        }
        let warm_us = e.start.elapsed().as_micros() - (COLD_US.with(|c| *c.borrow()) - e.cold_before);
        let t0 = Instant::now();
        let needed: std::collections::HashSet<u64> = PIECES.with(|p| {
            p.borrow().as_ref().unwrap().iter().find(|ids| ids[0] == e.idx).unwrap()[1..].iter().copied().collect()
        });
        let mut n = 0;
        let mut out = crate::util::TcCache::new();
        // NANODA_REPLAY=empty: the same re-run with nothing seeded, for comparison.
        if std::env::var("NANODA_REPLAY").is_ok_and(|v| v == "empty") {
            return Some((out, 0, warm_us));
        }
        let c = &tc.tc_cache;
        CREATED.with(|cr| {
            let cr = cr.borrow();
            let mut ok = |id: u8, h: u64| {
                let yes = cr.get(&h).is_some_and(|at| needed.contains(at));
                n += usize::from(yes);
                let _ = id;
                yes
            };
            for (&k, &v) in &c.infer_cache_check {
                if ok(0, key(0, &k)) { out.infer_cache_check.insert(k, v); }
            }
            for (&k, &v) in &c.infer_cache_no_check {
                if ok(1, key(1, &k)) { out.infer_cache_no_check.insert(k, v); }
            }
            for (&k, &v) in &c.whnf_cache {
                if ok(2, key(2, &k)) { out.whnf_cache.insert(k, v); }
            }
            for (&k, &v) in &c.whnf_no_unfolding_cache {
                if ok(3, key(3, &k)) { out.whnf_no_unfolding_cache.insert(k, v); }
            }
            for &k in &c.defeq_fail_cache {
                if ok(4, key(4, &k)) { out.defeq_fail_cache.insert(k); }
            }
            for &k in &c.eq_cache {
                if ok(5, key(5, &k)) { out.eq_cache.insert(k); }
            }
            for &k in &c.congr_fail_cache {
                if ok(6, key(6, &k)) { out.congr_fail_cache.insert(k); }
            }
        });
        // Seeding isn't the enclosing calls' work.
        COLD_US.with(|t| *t.borrow_mut() += t0.elapsed().as_micros());
        Some((out, n, warm_us))
    }

    pub(crate) fn replayed(tc: &TypeChecker<'_, '_, '_>, e: &Entry, same: bool, seeded: usize, warm_us: u128, m: (u128, usize)) {
        let _ = tc;
        std::eprintln!("replay {} {} warm_us {} replay_us {} same {} seeded {} new_exprs {}", e.idx, e.name, warm_us, m.0, same, seeded, m.1);
    }

    pub(crate) fn piece_end(e: &Entry) {
        if e.cold {
            return;
        }
        ACTIVE.with(|a| {
            let mut a = a.borrow_mut();
            if a.as_ref().is_some_and(|(idx, ..)| *idx == e.idx) {
                *a = None;
            }
        });
    }

    fn load_pieces() {
        PIECES.with(|p| {
            if p.borrow().is_some() {
                return;
            }
            let mut pieces = std::vec::Vec::new();
            if let Some(path) = std::env::var_os("NANODA_PIECES") {
                for line in std::fs::read_to_string(path).unwrap().lines() {
                    let ids: std::vec::Vec<u64> = line.split_whitespace().map(|x| x.parse().unwrap()).collect();
                    NEEDED.with(|n| n.borrow_mut().extend(ids[1..].iter().copied()));
                    STARTS.with(|s| s.borrow_mut().insert(ids[0]));
                    pieces.push(ids);
                }
            }
            *p.borrow_mut() = Some(pieces);
        });
    }

    fn node_id<'t>(e: ExprPtr<'t>) -> u64 {
        use core::hash::{Hash, Hasher};
        let mut h = std::collections::hash_map::DefaultHasher::new();
        e.hash(&mut h);
        h.finish()
    }

    pub(crate) fn ins<'t, K: core::hash::Hash>(tc: &TypeChecker<'_, 't, '_>, cache: u8, k: &K, roots: &[ExprPtr<'t>]) {
        if COLD.with(|c| *c.borrow()) {
            return;
        }
        let at = now();
        CREATED.with(|c| {
            c.borrow_mut().entry(key(cache, k)).or_insert(at);
        });
        load_pieces();
        if NEEDED.with(|n| n.borrow().contains(&at)) {
            use crate::expr::Expr::*;
            let mut seen = std::collections::HashSet::new();
            let mut stack: std::vec::Vec<ExprPtr<'t>> = roots.to_vec();
            while let Some(e) = stack.pop() {
                if !seen.insert(e) {
                    continue;
                }
                match tc.ctx.read_expr(e) {
                    App { fun, arg, .. } => stack.extend([fun, arg]),
                    Pi { binder_type, body, .. } | Lambda { binder_type, body, .. } => stack.extend([binder_type, body]),
                    Let { binder_type, val, body, .. } => stack.extend([binder_type, val, body]),
                    Proj { structure, .. } => stack.push(structure),
                    Local { binder_type, .. } => stack.push(binder_type),
                    _ => {},
                }
            }
            let open = roots.iter().any(|&r| match tc.ctx.read_expr(r) {
                App { has_fvars, .. } | Pi { has_fvars, .. } | Lambda { has_fvars, .. } | Let { has_fvars, .. } | Proj { has_fvars, .. } => has_fvars,
                Local { .. } => true,
                _ => false,
            });
            OPEN.with(|o| *o.borrow_mut().entry(at).or_insert(false) |= open);
            let ls = locals(tc, roots);
            FACT_LOCALS.with(|f| f.borrow_mut().entry(at).or_default().extend(ls));
            FACTS.with(|f| f.borrow_mut().entry(at).or_default().extend(seen.into_iter().map(node_id)));
        }
    }

    /// For each piece: the nodes its needed facts reach, shared, against the plain sum.
    pub(crate) fn fact_report() {
        let pieces = PIECES.with(|p| p.borrow().clone()).unwrap_or_default();
        if pieces.is_empty() {
            return;
        }
        let mut rows = std::vec::Vec::new();
        FACTS.with(|f| {
            let f = f.borrow();
            for piece in &pieces {
                let mut union = std::collections::HashSet::new();
                let mut sum = 0usize;
                for id in &piece[1..] {
                    if let Some(nodes) = f.get(id) {
                        sum += nodes.len();
                        union.extend(nodes.iter().copied());
                    }
                }
                rows.push((union.len(), sum, piece.len() - 1));
            }
        });
        for (shared, sum, facts) in &rows {
            std::eprintln!("piecefacts {facts} {shared} {sum}");
        }
        SCOPE.with(|s| {
            let s = s.borrow();
            let n: std::vec::Vec<usize> = s.2.iter().map(|p| p.len()).collect();
            std::eprintln!("scope: {} outside hits in pieces; worst local: input-only {} ({} pieces), live context {} ({}), made inside {} ({}), dead {} ({}), unique {} ({})",
                s.0, s.1[0], n[0], s.1[1], n[1], s.1[2], n[2], s.1[3], n[3], s.1[4], n[4]);
        });
        OPEN.with(|o| {
            let o = o.borrow();
            for piece in &pieces {
                let open = piece[1..].iter().filter(|id| o.get(id) == Some(&true)).count();
                std::eprintln!("pieceopen {} {}", piece.len() - 1, open);
            }
        });
    }

    pub(crate) fn hit<K: core::hash::Hash>(cache: u8, k: &K) {
        if COLD.with(|c| *c.borrow()) {
            return;
        }
        if let Some(made) = CREATED.with(|c| c.borrow().get(&key(cache, k)).copied()) {
            let at = now();
            HITS.with(|h| h.borrow_mut().push((at, made)));
            ACTIVE.with(|a| {
                if let Some((start, inputs, live)) = a.borrow().as_ref() {
                    if made < *start {
                        // The worst kind among the fact's locals.
                        let kind = FACT_LOCALS.with(|f| {
                            f.borrow().get(&made).map_or(0, |ls| {
                                ls.iter()
                                    .map(|&(id, lv)| {
                                        if inputs.contains(&id) {
                                            0
                                        } else if lv == u16::MAX {
                                            4
                                        } else if usize::from(lv) >= live.len() {
                                            2
                                        } else if live[usize::from(lv)] == id {
                                            1
                                        } else {
                                            3
                                        }
                                    })
                                    .max()
                                    .unwrap_or(0)
                            })
                        });
                        SCOPE.with(|s| {
                            let mut s = s.borrow_mut();
                            s.0 += 1;
                            s.1[kind] += 1;
                            s.2[kind].insert(*start);
                        });
                    }
                }
            });
        }
    }

    /// Re-run this call with empty caches if it took 2–50 ms warm (NANODA_COLD=1).
    pub(crate) fn wants_cold(e: &Entry) -> bool {
        static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
        let on = *ON.get_or_init(|| std::env::var("NANODA_COLD").is_ok());
        let ms = e.start.elapsed().as_micros() - (COLD_US.with(|c| *c.borrow()) - e.cold_before);
        on && !e.cold && (2_000..=50_000).contains(&ms)
    }

    pub(crate) struct Cold {
        start: Instant,
        exprs: usize,
    }

    pub(crate) fn begin_cold(tc: &TypeChecker<'_, '_, '_>) -> Cold {
        COLD.with(|c| *c.borrow_mut() = true);
        Cold { start: Instant::now(), exprs: tc.ctx.dag.exprs.len() }
    }

    pub(crate) fn end_cold(tc: &TypeChecker<'_, '_, '_>, c: Cold) -> (u128, usize) {
        COLD.with(|c| *c.borrow_mut() = false);
        let us = c.start.elapsed().as_micros();
        COLD_US.with(|t| *t.borrow_mut() += us);
        (us, tc.ctx.dag.exprs.len() - c.exprs)
    }

    /// Distinct nodes reachable from `terms`, through locals' types; and how many locals.
    fn size<'t>(tc: &TypeChecker<'_, 't, '_>, terms: &[ExprPtr<'t>]) -> (usize, usize) {
        use crate::expr::Expr::*;
        let mut seen = std::collections::HashSet::new();
        let mut stack: std::vec::Vec<ExprPtr<'t>> = terms.to_vec();
        let mut locals = 0;
        while let Some(e) = stack.pop() {
            if !seen.insert(e) {
                continue;
            }
            match tc.ctx.read_expr(e) {
                App { fun, arg, .. } => stack.extend([fun, arg]),
                Pi { binder_type, body, .. } | Lambda { binder_type, body, .. } => stack.extend([binder_type, body]),
                Let { binder_type, val, body, .. } => stack.extend([binder_type, val, body]),
                Proj { structure, .. } => stack.push(structure),
                Local { binder_type, .. } => {
                    locals += 1;
                    stack.push(binder_type)
                },
                _ => {},
            }
        }
        (seen.len(), locals)
    }

    fn head<'t>(tc: &TypeChecker<'_, 't, '_>, e: ExprPtr<'t>) -> String {
        let (f, args) = tc.ctx.unfold_apps(e);
        match tc.ctx.read_expr(f) {
            crate::expr::Expr::Const { name, .. } => std::format!("{:?}/{}", tc.ctx.debug_print(name), args.len()),
            other => std::format!("{}/{}", std::format!("{:?}", other).split([' ', '{', '(']).next().unwrap_or("?"), args.len()),
        }
    }

    pub(crate) fn exit<'t>(tc: &TypeChecker<'_, 't, '_>, e: Entry, terms: &[ExprPtr<'t>], cold: Option<(u128, usize)>) {
        DEPTH.with(|d| *d.borrow_mut() -= 1);
        if e.cold {
            return;
        }
        // Warm time only: a cold re-run, if any, came after.
        let us = e.start.elapsed().as_micros() - (COLD_US.with(|c| *c.borrow()) - e.cold_before);
        if (std::env::var_os("NANODA_COLD").is_some() || std::env::var_os("NANODA_HITS").is_some()) && us >= 2_000 {
            let (nodes, locals) = size(tc, terms);
            let (cold_us, cold_exprs) = cold.unwrap_or((0, 0));
            std::eprintln!(
                "node {} {} {} {} {} {} {} {} {}",
                e.idx, e.depth, e.name, us, cold_us, cold_exprs, nodes, locals, now()
            );
        }
        SPANS.with(|s| s.borrow_mut().push((e.idx, now(), us as u64)));
        CALLS.with(|c| {
            let mut c = c.borrow_mut();
            let v = c.entry(e.name).or_insert((0, 0));
            v.0 += 1;
            if e.depth == 0 || true { v.1 += us; }
        });
        if us / 1000 >= threshold() {
            let heads: std::vec::Vec<String> = terms.iter().map(|t| head(tc, *t)).collect();
            std::eprintln!(
                "prof {:indent$}{} {} ms, +{} exprs: {}",
                "",
                e.name,
                us / 1000,
                tc.ctx.dag.exprs.len() - e.exprs,
                heads.join(" =?= "),
                indent = 2 * e.depth
            );
        }
    }

    pub(crate) fn count_unfold<'t>(tc: &TypeChecker<'_, 't, '_>, e: ExprPtr<'t>) {
        let (f, _) = tc.ctx.unfold_apps(e);
        if let crate::expr::Expr::Const { name, .. } = tc.ctx.read_expr(f) {
            let n = std::format!("{:?}", tc.ctx.debug_print(name));
            UNFOLDS.with(|u| *u.borrow_mut().entry(n).or_insert(0) += 1);
        }
    }

    /// Print call counts and the most unfolded definitions, then reset.
    pub(crate) fn summary() {
        if let Some(path) = std::env::var_os("NANODA_HITS") {
            use std::io::Write;
            let mut f = std::io::BufWriter::new(std::fs::File::create(path).unwrap());
            HITS.with(|h| {
                for (at, made) in h.borrow_mut().drain(..) {
                    f.write_all(&at.to_le_bytes()).unwrap();
                    f.write_all(&made.to_le_bytes()).unwrap();
                }
            });
        }
        if let Some(path) = std::env::var_os("NANODA_SPANS") {
            use std::io::Write;
            let mut f = std::io::BufWriter::new(std::fs::File::create(path).unwrap());
            SPANS.with(|s| {
                for (idx, end, us) in s.borrow_mut().drain(..) {
                    for x in [idx, end, us] {
                        f.write_all(&x.to_le_bytes()).unwrap();
                    }
                }
            });
        }
        CALLS.with(|c| {
            let mut v: std::vec::Vec<_> = c.borrow_mut().drain().collect();
            v.sort();
            for (name, (n, _)) in v {
                std::eprintln!("prof calls: {name} {n}");
            }
        });
        UNFOLDS.with(|u| {
            let mut v: std::vec::Vec<_> = u.borrow_mut().drain().collect();
            let total: u64 = v.iter().map(|(_, n)| n).sum();
            v.sort_by(|a, b| b.1.cmp(&a.1));
            std::eprintln!("prof unfolds: {total} in all, {} definitions", v.len());
            for (name, n) in v.into_iter().take(15) {
                std::eprintln!("prof unfold {n:>9} {name}");
            }
        });
    }
}
