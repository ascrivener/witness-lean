#[allow(unused_imports)]
use crate::prelude::*;
use crate::env::{
    ConstructorData, Declar, DeclarInfo, InductiveData, Notation, RecursorData, ReducibilityHint,
};
use crate::expr::{BinderStyle, Expr};
use crate::hash64;
use crate::level::Level;
use crate::name::Name;
use crate::util::{
    new_fx_hash_map, new_fx_index_map, new_fx_hash_set, BigUintPtr, Config, DagMarker, ExprPtr, FxHashMap, FxIndexMap,
    LeanDag, LevelPtr, LevelsPtr, NamePtr, StringPtr,
};
use num_bigint::BigUint;
use serde::{ Deserialize, Deserializer };
use serde::de::{Error as DeError, Visitor};
use core::error::Error;
use alloc::sync::Arc;
use alloc::borrow::Cow;
use core::fmt;

fn check_semver<'a>(meta: &FileMeta<'a>) -> Result<(), Box<dyn Error>> {
    const MIN_SEMVER : semver::Version = semver::Version::new(3, 1, 0);
    const MAX_SEMVER : semver::Version = semver::Version::new(3, 2, 0);
    let export_file_semver = semver::Version::parse(&meta.format.version).map_err(|e| format!("bad export format version: {e}"))?;
    if export_file_semver < MIN_SEMVER {
        return Err(Box::from(format!(
            "export format version is less than the minimum supported version. Found {}, but min supported is {}",
            export_file_semver, MIN_SEMVER
        )))
    } else if export_file_semver >= MAX_SEMVER {
        return Err(Box::from(format!(
            "export format version is greater than the maximum supported version. Found {}, but max (exclusive) supported is {}",
            export_file_semver, MAX_SEMVER
        )))
    } else {
        Ok(())
    }
}

pub struct Parser<'a> {
    line_num: usize,
    pub(crate) dag: LeanDag<'a>,
    pub(crate) declars: FxIndexMap<NamePtr<'a>, Declar<'a>>,
    notations: FxHashMap<NamePtr<'a>, Notation<'a>>,
    config: Config,
    /// Tracks axiom names that were found in the export file, but not white-listed,
    /// for use when `unpermitted_axiom_hard_error: false`
    skipped: Vec<String>,
    mutual_block_sizes: FxHashMap<NamePtr<'a>, (usize, usize)>,
    /// Reading a content-addressed node: duplicate names, levels and expressions are allowed.
    node_mode: bool,
    /// A theorem statement read from a node, waiting for its proof (or to become an assumption).
    pub(crate) statement: Option<DeclarInfo<'a>>,
    /// A proof's value, read from a proof blob.
    pub(crate) proof_value: Option<ExprPtr<'a>>,
}

/// A node's local indices, mapped to the shared tables'.
struct LocalMap {
    names: Vec<u32>,
    levels: Vec<u32>,
    exprs: Vec<u32>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Deserialize)]
struct LeanMeta<'a> {
    version: Cow<'a, str>,
    githash: Cow<'a, str>
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Deserialize)]
struct ExporterMeta<'a> {
    name: Cow<'a, str>,
    version: Cow<'a, str>
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Deserialize)]
struct FormatMeta<'a> {
    version: Cow<'a, str>
}

#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
struct FileMeta<'a> {
    lean: LeanMeta<'a>,
    exporter: ExporterMeta<'a>,
    format: FormatMeta<'a>
}

#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
enum BackRef {
    #[serde(alias = "in")]
    In(u32),
    #[serde(alias = "il")]
    Il(u32),
    #[serde(alias = "ie")]
    Ie(u32),
}

impl BackRef {
    fn assert_in(self, (idx, inserted): (usize, bool)) {
        if !inserted {
            panic!("Attempted to insert duplicate Name");
        }
        let lhs = u32::try_from(idx).unwrap();
        if self != BackRef::In(lhs) {
            panic!("Declined: Name back-reference mismatch, expected {:?}, found {:?}. Back-refs must be continuous.", BackRef::In(lhs), self);
        }
    }

    fn assert_il(self, (idx, inserted): (usize, bool)) {
        if !inserted {
            panic!("Attempted to insert duplicate Level");
        }
        let lhs = u32::try_from(idx).unwrap();
        if self != BackRef::Il(lhs) {
            panic!("Declined: Level back-reference mismatch, expected {:?}, found {:?}. Back-refs must be continuous.", BackRef::Il(lhs), self);
        }
    }

    fn assert_ie(self, (idx, inserted): (usize, bool)) {
        if !inserted {
            panic!("Attempted to insert duplicate Expr");
        }
        let lhs = u32::try_from(idx).unwrap();
        if self != BackRef::Ie(lhs) {
            panic!("Declined: Expr back-reference mismatch, expected {:?}, found {:?}. Back-refs must be continuous.", BackRef::Ie(lhs), self);
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
struct ExportJsonObject<'a> {
    #[serde(flatten)]
    val: ExportJsonVal<'a>,
    #[serde(flatten)]
    i: Option<BackRef>
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Deserialize)]
enum DefinitionSafety {
    #[serde(rename = "unsafe")]
    Unsafe,
    #[serde(rename = "safe")]
    Safe,
    #[serde(rename = "partial")]
    Partial,
}

#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
enum QuotKind {
    #[serde(rename = "type")]
    Ty,
    #[serde(rename = "ctor")]
    Ctor,
    #[serde(rename = "lift")]
    Lift,
    #[serde(rename = "ind")]
    Ind,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Deserialize)]
struct RecursorRule {
    ctor: u32,
    nfields: u16,
    rhs: u32,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Deserialize)]
struct IndInfo {
    name: u32,
    #[serde(rename = "levelParams")]
    uparams: Vec<u32>,
    #[serde(rename = "type")]
    ty: u32,
    all: Vec<u32>,
    ctors: Vec<u32>,
    #[serde(rename = "isRec")]
    is_rec: bool,
    #[serde(rename = "isReflexive")]
    is_reflexive: bool,
    #[serde(rename = "numIndices")]
    num_indices: u16,
    #[serde(rename = "numNested")]
    num_nested: u16,
    #[serde(rename = "numParams")]
    num_params: u16,
    #[serde(rename = "isUnsafe")]
    is_unsafe: bool
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Deserialize)]
struct Constructor {
    name: u32,
    #[serde(rename = "levelParams")]
    uparams: Vec<u32>,
    #[serde(rename = "type")]
    ty: u32,
    #[serde(rename = "isUnsafe")]
    is_unsafe: bool,
    cidx: u16,
    #[serde(rename = "numParams")]
    num_params: u16,
    #[serde(rename = "numFields")]
    num_fields: u16,
    induct: u32
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Deserialize)]
struct Recursor {
    name: u32,
    #[serde(rename = "levelParams")]
    uparams: Vec<u32>,
    #[serde(rename = "type")]
    ty: u32,
    #[serde(rename = "isUnsafe")]
    is_unsafe: bool,
    #[serde(rename = "numParams")]
    num_params: u16,
    #[serde(rename = "numIndices")]
    num_indices: u16,
    #[serde(rename = "numMotives")]
    num_motives: u16,
    #[serde(rename = "numMinors")]
    num_minors: u16,
    rules: Vec<RecursorRule>,
    all: Vec<u32>,
    k: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
enum ExportJsonVal<'a> {
    // The exporter metadata, incl. info about the lean, exporter, and format versions used
    // to create the export file.
    #[serde(rename = "meta")]
    Metadata(FileMeta<'a>),
    #[serde(rename = "str")]
    NameStr {
        pre: u32,
        str: Cow<'a, str>
    },
    #[serde(rename = "num")]
    NameNum {
        pre: u32,
        i: u32
    },
    #[serde(rename = "succ")]
    LevelSucc(u32),
    #[serde(rename = "max")]
    LevelMax([u32; 2]),
    #[serde(rename = "imax")]
    LevelIMax([u32; 2]),
    #[serde(rename = "param")]
    LevelParam(u32),
    #[serde(rename = "natVal", deserialize_with = "deserialize_biguint_from_string")]
    NatLit(BigUint),
    #[serde(rename = "strVal")]
    StrLit(Cow<'a, str>),
    #[serde(rename = "mdata")]
    ExprMData {
        expr: u32,
        data: serde_json::Value
    },
    #[serde(rename = "letE")]
    ExprLet {
        name: u32,
        #[serde(rename = "type")]
        ty: u32,
        value: u32,
        body: u32,
        nondep: bool
    },
    #[serde(rename = "const")]
    ExprConst {
        name: u32,
        #[serde(rename = "us")]
        levels: Vec<u32>
    },
    #[serde(rename = "app")]
    ExprApp {
        #[serde(rename = "fn")]
        fun: u32,
        arg: u32 
    },
    #[serde(rename = "forallE")]
    ExprPi {
        #[serde(rename = "name")]
        binder_name: u32,
        #[serde(rename = "type")]
        binder_type: u32,
        body: u32,
        #[serde(rename = "binderInfo")]
        binder_info: BinderStyle

    },
    #[serde(rename = "lam")]
    ExprLambda {
        #[serde(rename = "name")]
        binder_name: u32,
        #[serde(rename = "type")]
        binder_type: u32,
        body: u32,
        #[serde(rename = "binderInfo")]
        binder_info: BinderStyle
    },
    #[serde(rename = "proj")]
    ExprProj {
        #[serde(rename = "typeName")]
        type_name: u32,
        idx: usize,
        #[serde(rename = "struct")]
        structure: u32,
    },
    #[serde(rename = "sort")]
    ExprSort(u32),
    #[serde(rename = "bvar")]
    ExprBVar(u16),
    #[serde(rename = "axiom")]
    Axiom {
        name: u32,
        #[serde(rename = "levelParams")]
        uparams: Vec<u32>,
        #[serde(rename = "type")]
        ty: u32,
        #[serde(rename = "isUnsafe")]
        is_unsafe: bool
    },
    /// A theorem's statement, in a content-addressed node (binary only).
    #[serde(skip)]
    Statement {
        name: u32,
        uparams: Vec<u32>,
        ty: u32,
    },
    /// A theorem's proof, in a proof blob (binary only).
    #[serde(skip)]
    ProofValue(u32),
    #[serde(rename = "thm")]
    Thm {
        name: u32,
        #[serde(rename = "levelParams")]
        uparams: Vec<u32>,
        #[serde(rename = "type")]
        ty: u32,
        value: u32,
    },
    #[serde(rename = "def")]
    Defn {
        name: u32,
        #[serde(rename = "levelParams")]
        uparams: Vec<u32>,
        #[serde(rename = "type")]
        ty: u32,
        value: u32,
        #[serde(rename = "hints")]
        hint: ReducibilityHint,
        //all: Vec<usize>,
        safety: DefinitionSafety
    },
    #[serde(rename = "opaque")]
    Opaque {
        name: u32,
        #[serde(rename = "levelParams")]
        uparams: Vec<u32>,
        #[serde(rename = "type")]
        ty: u32,
        value: u32,
        #[serde(rename = "isUnsafe")]
        is_unsafe: bool
    },
    #[serde(rename = "quot")]
    Quot {
        name: u32,
        #[serde(rename = "levelParams")]
        uparams: Vec<u32>,
        #[serde(rename = "type")]
        ty: u32,
        #[serde(rename = "kind")]
        kind: QuotKind
    },
    #[serde(rename = "inductive")]
    Inductive {
        #[serde(rename = "types")]
        ind_vals: Vec<IndInfo>,
        #[serde(rename = "ctors")]
        ctor_vals: Vec<Constructor>,
        #[serde(rename = "recs")]
        rec_vals: Vec<Recursor>
    },
}

pub(crate) fn parse_export_str<'p>(
    export: &str,
    config: Config,
) -> Result<(crate::util::ExportFile<'p>, Vec<String>), Box<dyn Error>> {
    parse_export_parts(&[export.as_bytes()], config).map(|(file, skipped, _)| (file, skipped))
}

/// Parse several byte strings as consecutive parts of one export (each continuing the previous
/// one's indices). Each part is either lean4export NDJSON or the binary format (see
/// `binary_format.md`), told apart by the binary format's magic. Also returns, for each part, how
/// many declarations had been read by its end.
pub(crate) fn parse_export_parts<'p>(
    parts: &[&[u8]],
    config: Config,
) -> Result<(crate::util::ExportFile<'p>, Vec<String>, Vec<usize>), Box<dyn Error>> {
    let mut parser = Parser::new(config);
    let mut part_ends: Vec<usize> = Vec::with_capacity(parts.len());
    for part in parts {
        if let Some(body) = part.strip_prefix(BINARY_MAGIC) {
            parser.go_binary(body)?;
        } else {
            for line in core::str::from_utf8(part)?.lines() {
                parser.go1(line)?;
                parser.line_num += 1;
            }
        }
        part_ends.push(parser.declars.len());
    }
    
    // If the execution config has `unknown_pp_declar_hard_error: true`, and a `pp_declars` 
    // that includes `foo`, then we return early with an error if no `foo` declaration is present 
    // in the export file.
    if parser.config.unknown_pp_declar_hard_error {
        if let Some(pp_declars) = parser.config.pp_declars.as_ref() {
            let mut pp_declar_names = pp_declars.iter().map(|s| s.as_str()).collect::<crate::util::FxHashSet<&str>>();
            for declar_name in parser.declars.keys() {
                let n = parser.name_to_string(*declar_name);
                pp_declar_names.remove(n.as_str());
            }
            if pp_declar_names.len() > 0 {
                let list = pp_declar_names.into_iter().collect::<Vec<&str>>();
                return Err(Box::from(format!("these pp_declars were not found in the exported environment: {:#?}", list)))
            }
        }
    }
    
    let skipped = core::mem::take(&mut parser.skipped);
    Ok((finish(parser), skipped, part_ends))
}

/// Build the export file from everything `parser` has read.
pub(crate) fn finish<'p>(parser: Parser<'p>) -> crate::util::ExportFile<'p> {
    let name_cache = parser.dag.mk_name_cache();
    // Maps inductive names to exported recursor names. This is later reused in the inductive
    // module to require that the set of derived recursors matches the set of exported recursors,
    // so that additional "unassociated" recursors cannot be added to the environment.
    let mut ind_name_to_recursor_names = new_fx_hash_map();
    for declar in parser.declars.values() {
        match declar {
            Declar::Constructor(ConstructorData {inductive_name, info, ..}) => {
                match parser.declars.get(inductive_name).unwrap() {
                    Declar::Inductive(InductiveData {all_ctor_names, ..}) => {
                        assert!(all_ctor_names.contains(&info.name))
                    },
                    _ => panic!("failed to find inductive {:?}", parser.name_to_string(*inductive_name))
                }
            }
            Declar::Recursor(RecursorData {all_inductives, info, ..}) => {
                for ind_name in all_inductives.iter().copied() {
                    ind_name_to_recursor_names.entry(ind_name).or_insert(new_fx_hash_set()).insert(info.name);
                }
            },
            _ => continue
        }
    }
    
    let export_file = crate::util::ExportFile {
        dag: parser.dag,
        declars: parser.declars,
        notations: parser.notations,
        name_cache,
        config: parser.config,
        mutual_block_sizes: parser.mutual_block_sizes,
        ind_name_to_recursor_names,
    };
    export_file
}

impl<'a> Parser<'a> {
    pub fn new(config: Config) -> Self {
        Self {
            line_num: 0usize,
            dag: LeanDag::new(&config),
            declars: new_fx_index_map(),
            notations: new_fx_hash_map(),
            config,
            skipped: Vec::new(),
            mutual_block_sizes: new_fx_hash_map(),
            node_mode: false,
            statement: None,
            proof_value: None,
        }
    }
    
    fn axiom_permitted(&self, n: NamePtr<'a>) -> bool {
        self.config.unsafe_permit_all_axioms ||
            self.config.permitted_axioms.as_ref().map(|v| v.contains(&self.name_to_string(n))).unwrap_or(false)
    }

    fn num_loose_bvars(&self, e: ExprPtr<'a>) -> u16 {
        self.dag.exprs.get_index(e.idx()).unwrap().num_loose_bvars()
    }

    fn has_fvars(&self, e: ExprPtr<'a>) -> bool { self.dag.exprs.get_index(e.idx()).unwrap().has_fvars() }

    fn get_name_ptr(&self, idx: u32) -> NamePtr<'a> {
        let out = crate::util::Ptr::from(DagMarker::ExportFile, idx as usize);
        assert!((idx as usize) < self.dag.names.len());
        out
    }

    fn get_level_ptr(&self, idx: u32) -> LevelPtr<'a> {
        let out = crate::util::Ptr::from(DagMarker::ExportFile, idx as usize);
        assert!((idx as usize) < self.dag.levels.len());
        out
    }
    fn get_names(&self, idxs: &[u32]) -> Vec<NamePtr<'a>> {
        let mut names = Vec::new();
        for idx in idxs.iter().copied() {
            assert!(self.dag.names.get_index(idx as usize).is_some());
            names.push(NamePtr::from(DagMarker::ExportFile, idx as usize));
        }
        names
    }

    fn get_uparams_ptr(&mut self, name_idxs: &[u32]) -> LevelsPtr<'a> {
        let mut levels = Vec::new();
        for name_idx in name_idxs.iter().copied() {
            let name_ptr = self.get_name_ptr(name_idx);
            let hash = hash64!(crate::level::PARAM_HASH, name_ptr);
            // Has to already exist
            let idx = self.dag.levels.get_index_of(&Level::Param(name_ptr, hash)).unwrap();
            levels.push(LevelPtr::from(DagMarker::ExportFile, idx as usize));
        }
        LevelsPtr::from(DagMarker::ExportFile, self.dag.uparams.insert_full(Arc::from(levels)).0)
    }

    fn get_levels_ptr(&mut self, idxs: &[u32]) -> LevelsPtr<'a> {
        let mut levels = Vec::new();
        for idx in idxs.iter().copied() {
            levels.push(LevelPtr::from(DagMarker::ExportFile, idx as usize));
        }
        LevelsPtr::from(DagMarker::ExportFile, self.dag.uparams.insert_full(Arc::from(levels)).0)
    }

    fn get_expr_ptr(&self, idx: u32) -> ExprPtr<'a> {
        let out = crate::util::Ptr::from(DagMarker::ExportFile, idx as usize);
        assert!((idx as usize) < self.dag.exprs.len());
        out
    }

    // Used for the axiom whitelist feature.
    pub(crate) fn name_to_string(&self, n: NamePtr<'a>) -> String {
        match self.dag.names.get_index(n.idx()).copied().unwrap() {
            Name::Anon => String::new(),
            Name::Str(pfx, sfx, _) => {
                let mut s = self.name_to_string(pfx);
                if !s.is_empty() {
                    s.push('.');
                }
                s + self.dag.strings.get_index(sfx.idx()).unwrap()
            }
            Name::Num(pfx, sfx, _) => {
                let mut s = self.name_to_string(pfx);
                if !s.is_empty() {
                    s.push('.');
                }
                s + format!("{}", sfx).as_str()
            }
        }
    }

    fn go1(&mut self, line: &str) -> Result<(), Box<dyn Error>> {
        let ExportJsonObject {val, i: assigned_idx} = serde_json::from_str::<ExportJsonObject>(line)?;
        self.apply(val, assigned_idx, line).map(|_| ())
    }

    /// Read a binary-format part (after its magic). Indices are implicit: each name, level or
    /// expression gets the next free index of its kind, and a duplicate is still rejected.
    fn go_binary(&mut self, bytes: &[u8]) -> Result<(), Box<dyn Error>> {
        let mut r = BinReader { bytes, pos: 0, map: None };
        while r.pos < r.bytes.len() {
            let (val, kind) = r.item()?;
            let idx = |n: usize| u32::try_from(n).map_err(|_| "too many items");
            let backref = match kind {
                ItemKind::Name => Some(BackRef::In(idx(self.dag.names.len())?)),
                ItemKind::Level => Some(BackRef::Il(idx(self.dag.levels.len())?)),
                ItemKind::Expr => Some(BackRef::Ie(idx(self.dag.exprs.len())?)),
                ItemKind::Other => None,
            };
            self.apply(val, backref, "<binary item>")?;
            self.line_num += 1;
        }
        Ok(())
    }

    /// Read the items of a content-addressed node or proof (see `node_format.md`), which number
    /// their names, levels and expressions locally, from scratch. Each item is added to the
    /// shared tables, or found there if an earlier node added it. Returns the global index of
    /// each local expression.
    pub(crate) fn go_node(&mut self, bytes: &[u8]) -> Result<Vec<u32>, Box<dyn Error>> {
        let mut map = LocalMap { names: vec![0], levels: vec![0], exprs: Vec::new() };
        let mut pos = 0;
        self.node_mode = true;
        while pos < bytes.len() {
            let mut r = BinReader { bytes, pos, map: Some(&map) };
            let (val, kind) = r.item()?;
            pos = r.pos;
            let idx = self.apply(val, None, "<node item>")?;
            let idx = idx.map(|i| u32::try_from(i)).transpose()?;
            match (kind, idx) {
                (ItemKind::Name, Some(i)) => map.names.push(i),
                (ItemKind::Level, Some(i)) => map.levels.push(i),
                (ItemKind::Expr, Some(i)) => map.exprs.push(i),
                (ItemKind::Other, None) => {},
                _ => return Err("node item of unexpected kind".into()),
            }
        }
        self.node_mode = false;
        Ok(map.exprs)
    }

    /// Add one decoded export item, returning its index if it is a name, level or expression.
    /// `line` is only used in error messages.
    fn apply(&mut self, val: ExportJsonVal<'_>, assigned_idx: Option<BackRef>, line: &str) -> Result<Option<usize>, Box<dyn Error>> {
        use ExportJsonVal::*;
        match val {
            Metadata(json_val) => {
                let _ = check_semver(&json_val)?;
            }
            NameStr {pre, str} => {
                let pfx = self.get_name_ptr(pre);
                let sfx = StringPtr::from(
                    DagMarker::ExportFile, 
                    self.dag.strings.insert_full(alloc::borrow::Cow::Owned(str.to_string())).0
                );

                let insert_result = {
                    let hash = hash64!(crate::name::STR_HASH, pfx, sfx);
                    self.dag.names.insert_full(Name::Str(pfx, sfx, hash))
                };
                return Ok(Some(self.assign_in(assigned_idx, insert_result)));
            }
            NameNum {pre, i} => {
                let pfx = self.get_name_ptr(pre);
                let sfx = i as u64;
                let insert_result = {
                    let hash = hash64!(crate::name::NUM_HASH, pfx, sfx);
                    self.dag.names.insert_full(Name::Num(pfx, sfx, hash))
                };
                return Ok(Some(self.assign_in(assigned_idx, insert_result)));
            }
            NatLit(big_uint) => {
                if !self.config.nat_extension {
                    return Err(Box::<dyn Error>::from(
                        format!("Nat lit extension disallowed by checker execution config, but export file contains a nat literal {:?}", line)
                    ))
                }
                let num_ptr = BigUintPtr::from(DagMarker::ExportFile, self.dag.bignums.as_mut().unwrap().insert_full(big_uint).0);
                let insert_result = {
                    let hash = hash64!(crate::expr::NAT_LIT_HASH, num_ptr);
                    self.dag.exprs.insert_full(Expr::NatLit { ptr: num_ptr, hash })
                };
                if !self.config.nat_extension {
                    return Err(Box::<dyn Error>::from(
                        format!("Nat lit extension disallowed by checker execution config, found {:?}", line)
                    ))
                }
                return Ok(Some(self.assign_ie(assigned_idx, insert_result)));
            }
            StrLit(cow_str) => {
                if !self.config.string_extension {
                    return Err(Box::<dyn Error>::from(
                        format!("String lit extension disallowed by checker execution config, but export file contains a string literal {:?}", line)
                    ))
                }
                let s = cow_str.to_string();
                let string_ptr = StringPtr::from(
                    DagMarker::ExportFile,
                    self.dag.strings.insert_full(crate::util::CowStr::Owned(s)).0
                );
                let insert_result = {
                    let hash = hash64!(crate::expr::STRING_LIT_HASH, string_ptr);
                    self.dag.exprs.insert_full(Expr::StringLit { ptr: string_ptr, hash })
                };
                return Ok(Some(self.assign_ie(assigned_idx, insert_result)));
            }
            LevelSucc(l) => {
                let l = self.get_level_ptr(l);
                let insert_result = {
                    let hash = hash64!(crate::level::SUCC_HASH, l);
                    self.dag.levels.insert_full(Level::Succ(l, hash))
                };
                return Ok(Some(self.assign_il(assigned_idx, insert_result)));
            }
            LevelMax([l, r]) => {
                let l = self.get_level_ptr(l);
                let r = self.get_level_ptr(r);
                let insert_result = {
                    let hash = hash64!(crate::level::MAX_HASH, l, r);
                    self.dag.levels.insert_full(Level::Max(l, r, hash))
                };
                return Ok(Some(self.assign_il(assigned_idx, insert_result)));
            }
            LevelIMax([l, r]) => {
                let l = self.get_level_ptr(l);
                let r = self.get_level_ptr(r);
                let insert_result = {
                    let hash = hash64!(crate::level::IMAX_HASH, l, r);
                    self.dag.levels.insert_full(Level::IMax(l, r, hash))
                };
                return Ok(Some(self.assign_il(assigned_idx, insert_result)));
            }
            LevelParam(var_idx) => {
                 let n = self.get_name_ptr(var_idx);
                 let insert_result = {
                     let hash = hash64!(crate::level::PARAM_HASH, n);
                     self.dag.levels.insert_full(Level::Param(n, hash))
                 };
                return Ok(Some(self.assign_il(assigned_idx, insert_result)));
            }
            ExprSort(level) => {
                let level = self.get_level_ptr(level);
                let insert_result = {
                    let hash = hash64!(crate::expr::SORT_HASH, level);
                    self.dag.exprs.insert_full(Expr::Sort { level, hash })
                };
                return Ok(Some(self.assign_ie(assigned_idx, insert_result)));
            }
            ExprMData {..} => {
                panic!("Expr.mdata not supported");
            }
            ExprConst {name, levels} => {
                let name = self.get_name_ptr(name);
                let levels = self.get_levels_ptr(&levels);
                let insert_result = {
                    let hash = hash64!(crate::expr::CONST_HASH, name, levels);
                    self.dag.exprs.insert_full(Expr::Const { name, levels, hash })
                };
                return Ok(Some(self.assign_ie(assigned_idx, insert_result)));
            }
            ExprApp {fun, arg} => {
                let fun = self.get_expr_ptr(fun);
                let arg = self.get_expr_ptr(arg);
                let insert_result = {
                    let hash = hash64!(crate::expr::APP_HASH, fun, arg);
                    let num_bvars = self.num_loose_bvars(fun).max(self.num_loose_bvars(arg));
                    let locals = self.has_fvars(fun) || self.has_fvars(arg);
                    self.dag.exprs.insert_full(Expr::App { fun, arg, num_loose_bvars: num_bvars, has_fvars: locals, hash })
                };
                return Ok(Some(self.assign_ie(assigned_idx, insert_result)));
            }
            ExprBVar(dbj_idx) => {
                let insert_result = {
                    let hash = hash64!(crate::expr::VAR_HASH, dbj_idx);
                    self.dag.exprs.insert_full(Expr::Var { dbj_idx, hash })
                };
                return Ok(Some(self.assign_ie(assigned_idx, insert_result)));
            }
            ExprLambda {binder_name, binder_type, binder_info, body} => {
                let binder_name = self.get_name_ptr(binder_name);
                let binder_type = self.get_expr_ptr(binder_type);
                let body = self.get_expr_ptr(body);
                let insert_result = {
                    let hash = hash64!(crate::expr::LAMBDA_HASH, binder_name, binder_info, binder_type, body);
                    let num_bvars = self.num_loose_bvars(binder_type).max(self.num_loose_bvars(body).saturating_sub(1));
                    let locals = self.has_fvars(binder_type) || self.has_fvars(body);
                    self.dag.exprs.insert_full(Expr::Lambda {
                        binder_name,
                        binder_style: binder_info,
                        binder_type,
                        body,
                        num_loose_bvars: num_bvars,
                        has_fvars: locals,
                        hash,
                    })
                };
                return Ok(Some(self.assign_ie(assigned_idx, insert_result)));
            }
            ExprPi {binder_name, binder_type, binder_info, body} => {
                let binder_name = self.get_name_ptr(binder_name);
                let binder_type = self.get_expr_ptr(binder_type);
                let body = self.get_expr_ptr(body);
                let insert_result = {
                    let hash = hash64!(crate::expr::PI_HASH, binder_name, binder_info, binder_type, body);
                    let num_bvars = self.num_loose_bvars(binder_type).max(self.num_loose_bvars(body).saturating_sub(1));
                    let locals = self.has_fvars(binder_type) || self.has_fvars(body);
                    self.dag.exprs.insert_full(Expr::Pi {
                        binder_name,
                        binder_style: binder_info,
                        binder_type,
                        body,
                        num_loose_bvars: num_bvars,
                        has_fvars: locals,
                        hash,
                    })
                };
                return Ok(Some(self.assign_ie(assigned_idx, insert_result)));
            }
            ExprLet {name, ty, value, body, nondep} => {
                let binder_name = self.get_name_ptr(name);
                let binder_type = self.get_expr_ptr(ty);
                let val = self.get_expr_ptr(value);
                let body = self.get_expr_ptr(body);
                let insert_result = {
                    let hash = hash64!(crate::expr::LET_HASH, binder_name, binder_type, val, body, nondep);
                    let num_bvars = self
                        .num_loose_bvars(binder_type)
                        .max(self.num_loose_bvars(val).max(self.num_loose_bvars(body).saturating_sub(1)));
                    let locals = self.has_fvars(binder_type) || self.has_fvars(val) || self.has_fvars(body);
                    self.dag.exprs.insert_full(Expr::Let {
                        binder_name,
                        binder_type,
                        val,
                        body,
                        num_loose_bvars: num_bvars,
                        has_fvars: locals,
                        hash,
                        nondep
                    })
                };
                return Ok(Some(self.assign_ie(assigned_idx, insert_result)));
            }
            ExprProj {type_name, idx, structure: struct_} => {
                let ty_name = self.get_name_ptr(type_name);
                let structure = self.get_expr_ptr(struct_);
                let insert_result = {
                    let hash = hash64!(crate::expr::PROJ_HASH, ty_name, idx, structure);
                    let num_bvars = self.num_loose_bvars(structure);
                    let locals = self.has_fvars(structure);
                    self.dag.exprs.insert_full(Expr::Proj {
                        ty_name,
                        idx,
                        structure,
                        num_loose_bvars: num_bvars,
                        has_fvars: locals,
                        hash,
                    })
                };
                return Ok(Some(self.assign_ie(assigned_idx, insert_result)));
            }
            Axiom {name, ty, uparams, is_unsafe} => {
                assert!(!is_unsafe);
                let name = self.get_name_ptr(name);
                let uparams = self.get_uparams_ptr(&uparams);
                let ty = self.get_expr_ptr(ty);
                let info = DeclarInfo { name, ty, uparams };
                let axiom = Declar::Axiom { info };
                if self.axiom_permitted(name) {
                    assert!(self.declars.insert(name, axiom).is_none());
                } else {
                    let name_string = self.name_to_string(name);
                    if self.config.unpermitted_axiom_hard_error {
                        return Err(Box::from(format!("export file declares unpermitted axiom {:?}", name_string)))
                    } else {
                        self.skipped.push(name_string)
                    }
                }
            }
            Defn {name, ty, uparams, value, hint, safety} => {
                assert!(!matches!(safety, DefinitionSafety::Unsafe | DefinitionSafety::Partial));
                let name = self.get_name_ptr(name);
                let ty = self.get_expr_ptr(ty);
                let val = self.get_expr_ptr(value);
                let uparams = self.get_uparams_ptr(&uparams);
                let info = DeclarInfo { name, ty, uparams };
                let definition = Declar::Definition { info, val, hint };
                assert!(self.declars.insert(name, definition).is_none());
            }
            Thm {name, ty, uparams, value} => {
                let name = self.get_name_ptr(name);
                let ty = self.get_expr_ptr(ty);
                let val = self.get_expr_ptr(value);
                let uparams = self.get_uparams_ptr(&uparams);
                let info = DeclarInfo { name, ty, uparams };
                let theorem = Declar::Theorem { info, val };
                assert!(self.declars.insert(name, theorem).is_none());
            }
            Opaque {name, ty, uparams, value, is_unsafe} => {
                assert!(!is_unsafe);
                let name = self.get_name_ptr(name);
                let ty = self.get_expr_ptr(ty);
                let val = self.get_expr_ptr(value);
                let uparams = self.get_uparams_ptr(&uparams);
                let info = DeclarInfo { name, ty, uparams };
                let definition = Declar::Opaque { info, val };
                assert!(self.declars.insert(name, definition).is_none());
            }
            Quot {name, ty, uparams, ..} => {
                let name = self.get_name_ptr(name);
                let ty = self.get_expr_ptr(ty);
                let uparams = self.get_uparams_ptr(&uparams);
                let info = DeclarInfo { name, ty, uparams };
                let quot = Declar::Quot { info };
                assert!(self.declars.insert(name, quot).is_none());
            }
            Inductive {ind_vals, ctor_vals, rec_vals} => {
                let block_start = self.declars.len();
                let block_size = ind_vals.len() + ctor_vals.len() + rec_vals.len();
                for IndInfo {name, ty, uparams, all, ctors, is_rec, num_nested, num_params, num_indices, is_unsafe, ..} in ind_vals {
                    assert!(!is_unsafe);
                    let name = self.get_name_ptr(name);
                    self.mutual_block_sizes.insert(name, (block_start, block_size));
                    let uparams = self.get_uparams_ptr(&uparams);
                    let ty = self.get_expr_ptr(ty);
                    let all_ind_names =  Arc::from(self.get_names(&all)); 
                    let all_ctor_names = Arc::from(self.get_names(&ctors)); 
                    let inductive = Declar::Inductive(InductiveData {
                        info: DeclarInfo { name, uparams, ty },
                        is_recursive: is_rec,
                        is_nested: num_nested > 0,
                        num_params,
                        num_indices,
                        all_ind_names,
                        all_ctor_names,
                    });
                    assert!(self.declars.insert(name, inductive).is_none());
                }
                for Constructor {name, uparams, ty, is_unsafe, induct, cidx, num_params, num_fields, ..}  in ctor_vals {
                    assert!(!is_unsafe);
                    let name = self.get_name_ptr(name);
                    let ty = self.get_expr_ptr(ty);
                    let uparams = self.get_uparams_ptr(&uparams);
                    let info = DeclarInfo { name, ty, uparams };
                    let parent_inductive = self.get_name_ptr(induct);
                    let ctor_idx = cidx;
                    let ctor = Declar::Constructor(ConstructorData {
                        info,
                        inductive_name: parent_inductive,
                        ctor_idx,
                        num_params,
                        num_fields,
                    });
                    assert!(self.declars.insert(name, ctor).is_none());
                }
                for Recursor {name, uparams, ty, rules, is_unsafe, num_params, num_indices, num_motives, num_minors, k, all, ..} in rec_vals {
                    assert!(!is_unsafe);
                    let name = self.get_name_ptr(name);
                    let ty = self.get_expr_ptr(ty);
                    let uparams = self.get_uparams_ptr(&uparams);
                    let info = DeclarInfo { name, ty, uparams };
                    let rules = rules.into_iter().map(|RecursorRule {rhs, ctor, nfields}| 
                        crate::env::RecRule {
                            val: self.get_expr_ptr(rhs),
                            ctor_name: self.get_name_ptr(ctor),
                            ctor_telescope_size_wo_params: nfields
                        }
                    ).collect::<Vec<_>>();
                    let all_inductives = self.get_names(&all);
                    let recursor = Declar::Recursor(RecursorData {
                        info,
                        all_inductives: Arc::from(all_inductives),
                        num_params,
                        num_indices,
                        num_motives,
                        num_minors,
                        rec_rules: Arc::from(rules),
                        is_k: k,
                    });
                    assert!(self.declars.insert(name, recursor).is_none())
                }
            }
            Statement {name, uparams, ty} => {
                let name = self.get_name_ptr(name);
                let ty = self.get_expr_ptr(ty);
                let uparams = self.get_uparams_ptr(&uparams);
                assert!(self.statement.replace(DeclarInfo { name, ty, uparams }).is_none());
            }
            ProofValue(value) => {
                assert!(self.proof_value.replace(self.get_expr_ptr(value)).is_none());
            }
        }
        Ok(None)
    }

    fn assign_in(&self, backref: Option<BackRef>, inserted: (usize, bool)) -> usize {
        if !self.node_mode {
            backref.unwrap().assert_in(inserted);
        }
        inserted.0
    }

    fn assign_il(&self, backref: Option<BackRef>, inserted: (usize, bool)) -> usize {
        if !self.node_mode {
            backref.unwrap().assert_il(inserted);
        }
        inserted.0
    }

    fn assign_ie(&self, backref: Option<BackRef>, inserted: (usize, bool)) -> usize {
        if !self.node_mode {
            backref.unwrap().assert_ie(inserted);
        }
        inserted.0
    }
}

/// Decimal string -> BigUint in sub-quadratic time. `BigUint::from_str` is quadratic in the digit count,
/// which makes nat literals with millions of digits (as in large `decide`/`norm_num` proofs) take days.
/// This splits the digit string by 10^(BASE_DIGITS * 2^j) and combines with big multiplications
/// (Karatsuba/Toom-3), so cost is that of multiplication times a log factor. Same value as `from_str`.
pub(crate) fn parse_decimal_fast(s: &str) -> Result<BigUint, String> {
    use core::str::FromStr;
    const BASE_DIGITS: usize = 2048;
    if s.is_empty() || !s.bytes().all(|b| b.is_ascii_digit()) {
        return Err("expected a non-empty string of ASCII digits".to_string());
    }
    let s = s.trim_start_matches('0');
    if s.is_empty() {
        return Ok(BigUint::ZERO);
    }
    fn go(s: &str, pows: &mut Vec<BigUint>) -> BigUint {
        if s.len() <= 2 * BASE_DIGITS {
            return BigUint::from_str(s).expect("validated nonempty ASCII digits");
        }
        // largest j with BASE_DIGITS * 2^j < s.len()
        let mut j = 0usize;
        while BASE_DIGITS << (j + 1) < s.len() { j += 1; }
        while pows.len() <= j {
            let next = match pows.last() {
                None => num_traits::pow::pow(BigUint::from(10u8), BASE_DIGITS),
                Some(last) => last * last,
            };
            pows.push(next);
        }
        let m = BASE_DIGITS << j;
        let (hi, lo) = s.split_at(s.len() - m);
        let hi_v = go(hi, pows);
        let lo_v = go(lo, pows);
        hi_v * &pows[j] + lo_v
    }
    let mut pows: Vec<BigUint> = Vec::new();
    Ok(go(s, &mut pows))
}

#[cfg(test)]
mod parse_decimal_fast_tests {
    use super::*;
    use core::str::FromStr;
    #[test]
    fn matches_from_str() {
        let mut x: u64 = 88172645463325252;
        let mut next = || { x ^= x << 13; x ^= x >> 7; x ^= x << 17; x };
        let lens = [1usize, 2, 9, 4095, 4096, 4097, 4098, 6144, 8191, 8192, 8193, 12345, 40000, 100_000, 300_001];
        for &l in &lens {
            for trial in 0..3 {
                let mut st = String::with_capacity(l);
                for i in 0..l {
                    let d = if trial == 1 && i < l / 2 { 0 } else { (next() % 10) as u8 }; // leading zeros too
                    st.push((b'0' + d) as char);
                }
                assert_eq!(parse_decimal_fast(&st).unwrap(), BigUint::from_str(&st).unwrap(), "len {l} trial {trial}");
            }
        }
        assert_eq!(parse_decimal_fast("0").unwrap(), BigUint::from(0u8));
        let nines = "9".repeat(20000);
        assert_eq!(parse_decimal_fast(&nines).unwrap(), BigUint::from_str(&nines).unwrap());
        assert!(parse_decimal_fast("").is_err());
        assert!(parse_decimal_fast("12a").is_err());
    }
}

/// Needed because the lean4export format serializes nat literals as strings: 
/// https://github.com/leanprover/lean4export/blob/ddeb0869b0b5679b0104e16291ffd929fbaa6a48/format_ndjson.md?plain=1#L186
fn deserialize_biguint_from_string<'de, D>(deserializer: D) -> Result<BigUint, D::Error>
where D: Deserializer<'de> {
    struct BigUintStringVisitor;

    impl<'de> Visitor<'de> for BigUintStringVisitor {
        type Value = BigUint;

        fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.write_str("a string containing a natural number")
        }

        fn visit_str<E>(self, v: &str) -> Result<BigUint, E> where E: DeError {
            parse_decimal_fast(v).map_err(|e| E::custom(format!("invalid BigUint decimal string: {e}")))
        }

        fn visit_string<E>(self, v: String) -> Result<BigUint, E> where E: DeError {
            self.visit_str(&v)
        }
    }
    deserializer.deserialize_str(BigUintStringVisitor)
}

mod semver_tests {
    use super::*;
    #[allow(dead_code)]
    fn mk_meta(s: &'static str) -> FileMeta<'static> {
        FileMeta {
            lean: LeanMeta { version: Cow::Borrowed(""), githash: Cow::Borrowed("") },
            exporter: ExporterMeta { version: Cow::Borrowed(""), name: Cow::Borrowed("") },
            format :FormatMeta { version: Cow::Borrowed(s) }
        }
    }

    #[test]
    fn test_ng() {
        let too_small = [
            "2.9.9",
            "2.9.99",
        ];
        let too_big = [
            "4.0.0",
            "4.1.0",
            "3.2.0",
            "3.2.1",
        ];

        for v in too_small {
            assert!(check_semver(&mk_meta(v)).is_err())
        }
        for v in too_big {
            assert!(check_semver(&mk_meta(v)).is_err())
        }
    }

    #[test]
    fn test_ok() {
        let ok = [
            "3.1.0",
            "3.1.9",
        ];
        for v in ok {
            assert!(check_semver(&mk_meta(v)).is_ok())
        }
    }
}

/// Starts a binary-format export part.
pub(crate) const BINARY_MAGIC: &[u8] = b"LEANBIN\x01";

enum ItemKind { Name, Level, Expr, Other }

/// Reads the binary format described in `binary_format.md`.
struct BinReader<'a, 'm> {
    bytes: &'a [u8],
    pos: usize,
    /// For a node, its local indices so far; indices are read as they are otherwise.
    map: Option<&'m LocalMap>,
}

impl<'a> BinReader<'a, '_> {
    /// A name, level or expression reference: local in a node, global otherwise.
    fn index(&mut self, local: impl Fn(&LocalMap) -> &[u32]) -> Result<u32, Box<dyn Error>> {
        let i = self.u32()?;
        match self.map {
            None => Ok(i),
            Some(map) => local(map).get(i as usize).copied().ok_or_else(|| "node refers to a later or missing item".into()),
        }
    }
    fn n(&mut self) -> Result<u32, Box<dyn Error>> { self.index(|m| &m.names) }
    fn l(&mut self) -> Result<u32, Box<dyn Error>> { self.index(|m| &m.levels) }
    fn e(&mut self) -> Result<u32, Box<dyn Error>> { self.index(|m| &m.exprs) }
    fn ns(&mut self) -> Result<Vec<u32>, Box<dyn Error>> {
        let n = self.uvar()?;
        (0..n).map(|_| self.n()).collect()
    }
    fn ls(&mut self) -> Result<Vec<u32>, Box<dyn Error>> {
        let n = self.uvar()?;
        (0..n).map(|_| self.l()).collect()
    }

    fn byte(&mut self) -> Result<u8, Box<dyn Error>> {
        let b = *self.bytes.get(self.pos).ok_or("binary export ends early")?;
        self.pos += 1;
        Ok(b)
    }

    /// Unsigned LEB128.
    fn uvar(&mut self) -> Result<u64, Box<dyn Error>> {
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

    fn u32(&mut self) -> Result<u32, Box<dyn Error>> { Ok(u32::try_from(self.uvar()?)?) }
    fn u16(&mut self) -> Result<u16, Box<dyn Error>> { Ok(u16::try_from(self.uvar()?)?) }

    fn boolean(&mut self) -> Result<bool, Box<dyn Error>> {
        match self.byte()? {
            0 => Ok(false),
            1 => Ok(true),
            _ => Err("bad boolean".into()),
        }
    }

    fn slice(&mut self) -> Result<&'a [u8], Box<dyn Error>> {
        let len = usize::try_from(self.uvar()?)?;
        let end = self.pos.checked_add(len).filter(|&e| e <= self.bytes.len()).ok_or("binary export ends early")?;
        let s = &self.bytes[self.pos..end];
        self.pos = end;
        Ok(s)
    }

    fn string(&mut self) -> Result<Cow<'a, str>, Box<dyn Error>> {
        Ok(Cow::Borrowed(core::str::from_utf8(self.slice()?)?))
    }

    fn list<T>(&mut self, mut f: impl FnMut(&mut Self) -> Result<T, Box<dyn Error>>) -> Result<Vec<T>, Box<dyn Error>> {
        let n = self.uvar()?;
        (0..n).map(|_| f(self)).collect()
    }

    fn binder(&mut self) -> Result<BinderStyle, Box<dyn Error>> {
        Ok(match self.byte()? {
            0 => BinderStyle::Default,
            1 => BinderStyle::Implicit,
            2 => BinderStyle::StrictImplicit,
            3 => BinderStyle::InstanceImplicit,
            _ => return Err("bad binder info".into()),
        })
    }

    fn item(&mut self) -> Result<(ExportJsonVal<'a>, ItemKind), Box<dyn Error>> {
        use ExportJsonVal::*;
        use ItemKind::*;
        let tag = self.byte()?;
        Ok(match tag {
            0 => (Metadata(FileMeta {
                exporter: ExporterMeta { name: self.string()?, version: self.string()? },
                lean: LeanMeta { githash: self.string()?, version: self.string()? },
                format: FormatMeta { version: self.string()? },
            }), Other),
            1 => (NameStr { pre: self.n()?, str: self.string()? }, Name),
            2 => (NameNum { pre: self.n()?, i: self.u32()? }, Name),
            3 => (LevelSucc(self.l()?), Level),
            4 => (LevelMax([self.l()?, self.l()?]), Level),
            5 => (LevelIMax([self.l()?, self.l()?]), Level),
            6 => (LevelParam(self.n()?), Level),
            7 => (NatLit(BigUint::from_bytes_le(self.slice()?)), Expr),
            8 => (StrLit(self.string()?), Expr),
            9 => (ExprLet { name: self.n()?, ty: self.e()?, value: self.e()?, body: self.e()?, nondep: self.boolean()? }, Expr),
            10 => (ExprConst { name: self.n()?, levels: self.ls()? }, Expr),
            11 => (ExprApp { fun: self.e()?, arg: self.e()? }, Expr),
            12 => (ExprPi { binder_name: self.n()?, binder_type: self.e()?, body: self.e()?, binder_info: self.binder()? }, Expr),
            13 => (ExprLambda { binder_name: self.n()?, binder_type: self.e()?, body: self.e()?, binder_info: self.binder()? }, Expr),
            14 => (ExprProj { type_name: self.n()?, idx: usize::try_from(self.uvar()?)?, structure: self.e()? }, Expr),
            15 => (ExprSort(self.l()?), Expr),
            16 => (ExprBVar(self.u16()?), Expr),
            17 => (Axiom { name: self.n()?, uparams: self.ns()?, ty: self.e()?, is_unsafe: self.boolean()? }, Other),
            18 => (Thm { name: self.n()?, uparams: self.ns()?, ty: self.e()?, value: self.e()? }, Other),
            19 => (Defn {
                name: self.n()?,
                uparams: self.ns()?,
                ty: self.e()?,
                value: self.e()?,
                hint: match self.byte()? {
                    0 => ReducibilityHint::Opaque,
                    1 => ReducibilityHint::Abbrev,
                    2 => ReducibilityHint::Regular(self.u16()?),
                    _ => return Err("bad reducibility hint".into()),
                },
                safety: match self.byte()? {
                    0 => DefinitionSafety::Safe,
                    1 => DefinitionSafety::Unsafe,
                    2 => DefinitionSafety::Partial,
                    _ => return Err("bad definition safety".into()),
                },
            }, Other),
            20 => (Opaque { name: self.n()?, uparams: self.ns()?, ty: self.e()?, value: self.e()?, is_unsafe: self.boolean()? }, Other),
            21 => (Quot {
                name: self.n()?,
                uparams: self.ns()?,
                ty: self.e()?,
                kind: match self.byte()? {
                    0 => QuotKind::Ty,
                    1 => QuotKind::Ctor,
                    2 => QuotKind::Lift,
                    3 => QuotKind::Ind,
                    _ => return Err("bad quot kind".into()),
                },
            }, Other),
            22 => (Inductive {
                ind_vals: self.list(|r| Ok(IndInfo {
                    name: r.n()?,
                    uparams: r.ns()?,
                    ty: r.e()?,
                    all: r.ns()?,
                    ctors: r.ns()?,
                    is_rec: r.boolean()?,
                    is_reflexive: r.boolean()?,
                    num_indices: r.u16()?,
                    num_nested: r.u16()?,
                    num_params: r.u16()?,
                    is_unsafe: r.boolean()?,
                }))?,
                ctor_vals: self.list(|r| Ok(Constructor {
                    name: r.n()?,
                    uparams: r.ns()?,
                    ty: r.e()?,
                    is_unsafe: r.boolean()?,
                    cidx: r.u16()?,
                    num_params: r.u16()?,
                    num_fields: r.u16()?,
                    induct: r.n()?,
                }))?,
                rec_vals: self.list(|r| Ok(Recursor {
                    name: r.n()?,
                    uparams: r.ns()?,
                    ty: r.e()?,
                    is_unsafe: r.boolean()?,
                    num_params: r.u16()?,
                    num_indices: r.u16()?,
                    num_motives: r.u16()?,
                    num_minors: r.u16()?,
                    rules: r.list(|r| Ok(RecursorRule { ctor: r.n()?, nfields: r.u16()?, rhs: r.e()? }))?,
                    all: r.ns()?,
                    k: r.boolean()?,
                }))?,
            }, Other),
            23 => (Statement { name: self.n()?, uparams: self.ns()?, ty: self.e()? }, Other),
            24 => (ProofValue(self.e()?), Other),
            _ => return Err(format!("unknown binary item tag {tag}").into()),
        })
    }
}
