//! Loading content-addressed declarations, and binding a proof to a bounty's statement.
//!
//! A *node* (see `tools/lean/node_format.md` in witness-lean) holds one declaration (an
//! inductive block counts as one) with its own tables of names, levels and expressions, and the
//! hashes of the nodes declaring the constants it mentions: its *imports*. A theorem's node is
//! its statement; its *proof* is a separate blob naming the statement's hash.
//!
//! A [`NodeLoader`] reads nodes into one environment. It must be given each node after its
//! imports, and checks, as it goes, what makes a node mean the same thing wherever it's loaded:
//!
//! - for a node to be checked: every import has been loaded, and every constant the node (or its
//!   proof) mentions is declared by the node itself or by one of its imports. A node's hash covers
//!   its imports' hashes, so it pins everything it mentions, recursively;
//! - for a *trusted* node (one already checked, whose declarations are only used): its imports
//!   needn't be loaded, but any constant it mentions that is loaded must be declared by one of its
//!   imports ([`NodeLoader::finish`] checks that, once everything is loaded). So a trusted node is
//!   never read against another declaration of a name it uses, and leaving its imports out only
//!   leaves the kernel less to look up: a lookup that finds nothing fails the check, it never
//!   passes it. A check then loads only the trusted nodes the kernel touches, not their imports'
//!   closure;
//! - a name is declared once: two nodes declaring the same name can't be loaded together;
//! - the names the kernel treats specially ([`PINNED_NAMES`]: `Nat.add` and the like, which it
//!   computes with natively, and the permitted axioms) are declared only by nodes whose hashes the
//!   caller pins. Otherwise a node could declare its own `Nat.add` (or a `propext : False`), and
//!   the kernel would trust it by name.
//!
//! A theorem statement loaded with its proof becomes a theorem, to be checked. Loaded without one,
//! it becomes an assumption: the caller must only do that for statements already proven (in
//! witness, subjects of attestations).
#[allow(unused_imports)]
use crate::prelude::*;
use crate::env::{Declar, Phase};
use crate::expr::Expr;
use crate::level::Level;
use crate::parser::Parser;
use crate::judgment::{self, Entry};
use crate::tc::{InferFlag, TypeChecker};
use crate::util::{Config, ExportFile, FxHashMap, NamePtr, new_fx_hash_map};
use core::error::Error;
use core::ops::Range;

pub type Hash = [u8; 32];

/// The axioms a proof may rely on.
pub const PERMITTED_AXIOMS: [&str; 3] = ["propext", "Classical.choice", "Quot.sound"];

pub const NODE_MAGIC: &[u8] = b"LEANNOD\x01";
pub const PROOF_MAGIC: &[u8] = b"LEANPRF\x01";

/// Names that only pinned nodes may declare: those the kernel recognizes by name (see
/// `LeanDag::mk_name_cache`), and the permitted axioms.
pub const PINNED_NAMES: [&str; 34] = [
    "eagerReduce", "Quot", "Quot.mk", "Quot.lift", "Quot.ind", "String", "String.ofList", "Nat",
    "Nat.zero", "Nat.succ", "Nat.add", "Nat.sub", "Nat.mul", "Nat.pow", "Nat.mod", "Nat.div",
    "Nat.beq", "Nat.ble", "Nat.gcd", "Nat.xor", "Nat.land", "Nat.lor", "Nat.shiftLeft",
    "Nat.shiftRight", "Bool.true", "Bool.false", "Char", "Char.ofNat", "List", "List.nil",
    "List.cons", "propext", "Classical.choice", "Quot.sound",
];

/// A loaded node.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LoadedNode {
    pub hash: Hash,
    /// Its declarations, as indices into the export file's declarations.
    pub declars: Range<usize>,
    /// A theorem's statement.
    pub theorem: bool,
    /// A theorem statement loaded without its proof.
    pub assumed: bool,
}

pub struct NodeLoader<'p> {
    parser: Parser<'p>,
    pins: Vec<Hash>,
    declared_by: FxHashMap<NamePtr<'p>, Hash>,
    nodes: Vec<LoadedNode>,
    index: FxHashMap<Hash, usize>,
    /// Trusted nodes' names, imports and mentions, to check once everything is loaded.
    deferred: Vec<(Vec<NamePtr<'p>>, Vec<Hash>, Vec<NamePtr<'p>>)>,
}

/// Nodes read into one environment, ready to check.
pub struct Nodes<'p> {
    pub file: ExportFile<'p>,
    pub nodes: Vec<LoadedNode>,
    index: FxHashMap<Hash, usize>,
    /// The node declaring each loaded name.
    declared_by: FxHashMap<NamePtr<'p>, Hash>,
}

struct Header<'b> {
    imports: Vec<Hash>,
    items: &'b [u8],
}

fn uvar(bytes: &mut &[u8]) -> Result<u64, Box<dyn Error>> {
    let mut value = 0u64;
    for shift in (0..64).step_by(7) {
        let (&b, rest) = bytes.split_first().ok_or("node ends early")?;
        *bytes = rest;
        value |= u64::from(b & 0x7f) << shift;
        if b & 0x80 == 0 {
            return Ok(value);
        }
    }
    Err("varint too long".into())
}

fn hash_at(bytes: &mut &[u8]) -> Result<Hash, Box<dyn Error>> {
    let (h, rest) = bytes.split_first_chunk::<32>().ok_or("node ends early")?;
    *bytes = rest;
    Ok(*h)
}

fn header(mut bytes: &[u8]) -> Result<Header<'_>, Box<dyn Error>> {
    let n = uvar(&mut bytes)?;
    let imports = (0..n).map(|_| hash_at(&mut bytes)).collect::<Result<_, _>>()?;
    Ok(Header { imports, items: bytes })
}

impl<'p> NodeLoader<'p> {
    /// A loader trusting only nodes in `pins` to declare [`PINNED_NAMES`]. Only
    /// [`PERMITTED_AXIOMS`] may be declared as axioms.
    pub fn new(pins: &[Hash]) -> Self {
        let mut config = Config::in_memory(PERMITTED_AXIOMS.map(String::from).into());
        config.unpermitted_axiom_hard_error = true;
        NodeLoader {
            parser: Parser::new(config),
            pins: pins.to_vec(),
            declared_by: new_fx_hash_map(),
            nodes: Vec::new(),
            index: new_fx_hash_map(),
            deferred: Vec::new(),
        }
    }

    pub fn is_loaded(&self, hash: &Hash) -> bool {
        self.index.contains_key(hash)
    }

    /// The constants `exprs` mention.
    fn mentions(&self, exprs: &[u32]) -> Vec<NamePtr<'p>> {
        exprs
            .iter()
            .filter_map(|&e| match self.parser.dag.exprs.get_index(e as usize) {
                Some(Expr::Const { name, .. }) => Some(*name),
                Some(Expr::Proj { ty_name, .. }) => Some(*ty_name),
                _ => None,
            })
            .collect()
    }

    /// Check that the constants `exprs` mention are declared by `own` names or by `imports`, all
    /// of which must be loaded.
    fn check_mentions(&self, exprs: &[u32], own: &[NamePtr<'p>], imports: &[Hash]) -> Result<(), Box<dyn Error>> {
        if let Some(missing) = imports.iter().find(|h| !self.is_loaded(h)) {
            return Err(format!("import {missing:02x?} is not loaded (before the node importing it)").into());
        }
        for name in self.mentions(exprs) {
            let imported = self.declared_by.get(&name).is_some_and(|h| imports.contains(h));
            if !own.contains(&name) && !imported {
                return Err(format!("{} is mentioned but not imported", self.parser.name_to_string(name)).into());
            }
        }
        Ok(())
    }

    /// Load node `node` with hash `hash` (the caller has checked it, or computed it), and the
    /// statement's proof if it is a theorem and `proof` is given. A `trusted` node's imports
    /// needn't be loaded (see the module docs). Returns its index.
    pub fn add(&mut self, hash: Hash, node: &[u8], proof: Option<&[u8]>, trusted: bool) -> Result<usize, Box<dyn Error>> {
        if self.is_loaded(&hash) {
            return Err("node loaded twice".into());
        }
        let node = header(node.strip_prefix(NODE_MAGIC).ok_or("not a node")?)?;
        let start = self.parser.declars.len();
        let exprs = self.parser.go_node(node.items)?;
        let statement = self.parser.statement.take();
        if self.parser.proof_value.take().is_some() {
            return Err("a node holds a proof".into());
        }
        if statement.is_some() && self.parser.declars.len() != start {
            return Err("a theorem's node holds more than its statement".into());
        }
        let own: Vec<NamePtr<'p>> = match &statement {
            Some(info) => vec![info.name],
            None => self.parser.declars.keys().skip(start).copied().collect(),
        };
        if own.is_empty() {
            return Err("node declares nothing".into());
        }
        if trusted {
            if proof.is_some() {
                return Err("a proof for a trusted node".into());
            }
            self.deferred.push((own.clone(), node.imports.clone(), self.mentions(&exprs)));
        } else {
            self.check_mentions(&exprs, &own, &node.imports)?;
        }

        let theorem = statement.is_some();
        let assumed = theorem && proof.is_none();
        match (statement, proof) {
            (Some(info), Some(proof)) => {
                let proof = proof.strip_prefix(PROOF_MAGIC).ok_or("not a proof")?;
                let (of, proof) = proof.split_first_chunk::<32>().ok_or("proof ends early")?;
                if *of != hash {
                    return Err("proof of another statement".into());
                }
                let proof = header(proof)?;
                let exprs = self.parser.go_node(proof.items)?;
                if self.parser.statement.take().is_some() {
                    return Err("a proof holds a statement".into());
                }
                if self.parser.declars.len() != start {
                    return Err("a proof declares something".into());
                }
                let val = self.parser.proof_value.take().ok_or("proof without a value")?;
                self.check_mentions(&exprs, &[], &proof.imports)?;
                assert!(self.parser.declars.insert(info.name, Declar::Theorem { info, val }).is_none());
            },
            (Some(info), None) => {
                assert!(self.parser.declars.insert(info.name, Declar::Axiom { info }).is_none());
            },
            (None, Some(_)) => return Err("a proof for a node that isn't a theorem".into()),
            (None, None) => {},
        }

        for name in &own {
            if PINNED_NAMES.contains(&self.parser.name_to_string(*name).as_str()) && !self.pins.contains(&hash) {
                return Err(format!("{} is declared by a node that isn't pinned", self.parser.name_to_string(*name)).into());
            }
            self.declared_by.insert(*name, hash);
        }
        let i = self.nodes.len();
        self.nodes.push(LoadedNode { hash, declars: start..self.parser.declars.len(), theorem, assumed });
        self.index.insert(hash, i);
        Ok(i)
    }

    /// Check that every constant a trusted node mentions, if it is loaded, is declared by one of
    /// its imports, and build the environment.
    pub fn finish(self) -> Result<Nodes<'p>, Box<dyn Error>> {
        for (own, imports, mentions) in &self.deferred {
            for name in mentions {
                let elsewhere = self.declared_by.get(name).is_some_and(|h| !imports.contains(h));
                if !own.contains(name) && elsewhere {
                    return Err(format!("{} is loaded, but not from the node a trusted node imports", self.parser.name_to_string(*name)).into());
                }
            }
        }
        Ok(Nodes { file: crate::parser::finish(self.parser), nodes: self.nodes, index: self.index, declared_by: self.declared_by })
    }
}

impl<'p> Nodes<'p> {
    pub fn find(&self, hash: &Hash) -> Option<usize> {
        self.index.get(hash).copied()
    }

    /// Type-check node `i`'s declarations (panics on an error), each against the environment of
    /// the declarations loaded before it. An assumed statement's type is checked, but nothing
    /// proves it.
    pub fn check(&self, i: usize) {
        self.check_parts(i, |_| vec![Phase::Whole]);
    }

    /// [`Self::check`] the parts of node `i`'s declarations that `parts` picks, by each one's
    /// position within the node: the phases of its check to run (see [`Phase`]), none to skip it.
    /// Panics if it names phases of a declaration that isn't an inductive type.
    pub fn check_parts(&self, i: usize, parts: impl Fn(usize) -> Vec<Phase>) {
        for (k, d) in self.nodes[i].declars.clone().enumerate() {
            let d = self.file.declars.get_index(d).unwrap().1;
            for phase in parts(k) {
                self.file.check_declar_phase(d, phase);
            }
        }
    }

    /// Whether node `i`'s declaration at position `k` is an inductive type (so its check has
    /// phases).
    pub fn is_inductive_type(&self, i: usize, k: usize) -> bool {
        let d = self.nodes[i].declars.start + k;
        k < self.nodes[i].declars.len() && matches!(self.file.declars.get_index(d).unwrap().1, Declar::Inductive(..))
    }

    /// How many declarations node `i` holds.
    pub fn declaration_count(&self, i: usize) -> usize {
        self.nodes[i].declars.len()
    }

    /// Whether node `i` is an inductive block: inductive types, their constructors and recursors.
    /// Only such a node's declarations may be checked apart (each is checked alone the same way
    /// whichever op it's in; a theorem's node can't be split from its proof).
    pub fn is_inductive_block(&self, i: usize) -> bool {
        self.nodes[i].declars.clone().all(|d| {
            matches!(self.file.declars.get_index(d).unwrap().1, Declar::Inductive(..) | Declar::Constructor(..) | Declar::Recursor(..))
        })
    }

    /// The node declaring `name`, if one is loaded.
    pub fn declared_by(&self, name: NamePtr<'_>) -> Option<Hash> {
        self.declared_by.iter().find(|(n, _)| n.get_hash() == name.get_hash()).map(|(_, h)| *h)
    }

    /// Check that the constants `entries` mention mean here what they meant where the entries
    /// were made, or will (see [`crate::judgment`]): each declared, here, by one of `imports`.
    /// Attesting them (`made`), each must be: if one weren't loaded at all, the kernel would read
    /// it as opaque, and could make an entry that's false where it's defined. Citing them, as for
    /// a trusted node, only each that is loaded: one that isn't can't be looked up here, and its
    /// import's hash fixes what it means, as it did where the entries were attested.
    fn check_imports<'t>(&self, tc: &TypeChecker<'_, 't, 'p>, entries: &[Entry<'t>], imports: &[Hash], made: bool) -> Result<(), Box<dyn Error>> {
        Self::check_imports_in(&self.declared_by_ptr(), tc, entries, imports, made)
    }

    /// Which node declares each loaded name, by the name's pointer (the environment's names, from
    /// before any checker's lifetime, compare by pointer).
    fn declared_by_ptr(&self) -> FxHashMap<u64, Hash> {
        self.declared_by.iter().map(|(n, h)| (n.get_hash(), *h)).collect()
    }

    /// [`Self::check_imports`], given [`Self::declared_by_ptr`].
    fn check_imports_in<'t>(declared_by: &FxHashMap<u64, Hash>, tc: &TypeChecker<'_, 't, 'p>, entries: &[Entry<'t>], imports: &[Hash], made: bool) -> Result<(), Box<dyn Error>> {
        for name in judgment::mentions(tc, entries) {
            match declared_by.get(&name.get_hash()) {
                Some(h) if imports.contains(h) => {},
                None if !made => {},
                _ => return Err("a judgment mentions a constant not declared by one of its imports".into()),
            }
        }
        Ok(())
    }

    /// The imports a judgment of `entries` needs here: the nodes declaring what they mention.
    /// `None` if one isn't declared by a loaded node.
    pub fn judgment_imports<'t>(&self, tc: &TypeChecker<'_, 't, 'p>, entries: &[Entry<'t>]) -> Option<Vec<Hash>> {
        let mut out: Vec<Hash> = judgment::mentions(tc, entries).into_iter().map(|n| self.declared_by(n)).collect::<Option<_>>()?;
        out.sort();
        out.dedup();
        Some(out)
    }

    /// Seed `tc`, a checker for node `declaration`, with the entries of `cited`: judgments the
    /// caller vouches were attested. Each must be for `declaration`, and import what it mentions.
    fn seed<'t>(&self, tc: &mut TypeChecker<'_, 't, 'p>, declaration: &Hash, cited: &[&[u8]]) -> Result<(), Box<dyn Error>> {
        for blob in cited {
            let header = judgment::header(blob)?;
            if header.declaration != *declaration {
                return Err("a judgment for another declaration".into());
            }
            let mut l = judgment::Lazy::new(&header)?;
            let entries = (0..l.len()).map(|k| l.entry(tc, k)).collect::<Result<Vec<_>, _>>()?;
            self.check_imports(tc, &entries, &header.imports, false)?;
            judgment::seed(tc, &entries);
        }
        Ok(())
    }

    /// Node `i`'s single declaration.
    fn single(&self, i: usize) -> Result<&Declar<'p>, Box<dyn Error>> {
        let node = &self.nodes[i];
        if node.declars.len() != 1 {
            return Err("judgments for a node of several declarations".into());
        }
        Ok(self.file.declars.get_index(node.declars.start).unwrap().1)
    }

    /// [`Self::check`] node `i`, its checker seeded first with the judgments `cited` (attested,
    /// as the caller vouches; see [`crate::judgment`]). Type errors panic; a judgment that doesn't
    /// belong is an error.
    pub fn check_with(&self, i: usize, cited: &[&[u8]]) -> Result<(), Box<dyn Error>> {
        if cited.is_empty() {
            self.check(i);
            return Ok(());
        }
        let d = self.single(i)?;
        let val = match d {
            Declar::Theorem { val, .. } | Declar::Definition { val, .. } | Declar::Opaque { val, .. } => *val,
            _ => return Err("judgments for a declaration without a value".into()),
        };
        let hash = self.nodes[i].hash;
        self.file.with_tc_and_declar(*d.info(), |tc| {
            self.seed(tc, &hash, cited)?;
            // As `check_declar` does for a declaration with a value.
            tc.check_declar_info(d).unwrap();
            let inferred_type = tc.infer(val, InferFlag::Check);
            tc.assert_def_eq(inferred_type, d.info().ty);
            Ok(())
        })
    }

    /// Attest the judgments `subjects`, for node `declaration`: in a checker for it, seeded with
    /// the judgments `cited`, run the calls in `calls`; then every entry of every subject must be
    /// in its caches. Type errors panic.
    pub fn attest_judgments(&self, declaration: usize, cited: &[&[u8]], calls: &[u8], subjects: &[&[u8]]) -> Result<(), Box<dyn Error>> {
        let d = self.single(declaration)?;
        let hash = self.nodes[declaration].hash;
        let headers = cited.iter().map(|b| judgment::header(b)).collect::<Result<Vec<_>, _>>()?;
        if headers.iter().any(|h| h.declaration != hash) {
            return Err("a judgment for another declaration".into());
        }
        self.file.with_tc_and_declar(*d.info(), |tc| {
            let mut lazy = headers.iter().map(judgment::Lazy::new).collect::<Result<Vec<_>, _>>()?;
            let declared_by = self.declared_by_ptr();
            let mut levels = new_fx_hash_map();
            #[cfg(feature = "trace")]
            let t0 = std::time::Instant::now();
            let calls = judgment::calls(tc, calls)?;
            #[cfg(feature = "trace")]
            let (mut seeding, mut slow) = (core::time::Duration::ZERO, Vec::new());
            #[cfg(feature = "trace")]
            let mut times = Vec::new();
            // Each call runs seeded with what it needs, just before it: no call sees an entry its
            // own check, in the whole declaration's, made only later.
            for (depth, eager, call, seeds) in calls {
                #[cfg(feature = "trace")]
                let ts = std::time::Instant::now();
                let mut by_judgment: FxHashMap<usize, Vec<Entry<'_>>> = new_fx_hash_map();
                for (j, k) in seeds {
                    let entry = lazy.get_mut(j).ok_or("a seed from a judgment not cited")?.entry(tc, k)?;
                    by_judgment.entry(j).or_default().push(entry);
                }
                for (j, entries) in &by_judgment {
                    Self::check_imports_in(&declared_by, tc, entries, &headers[*j].imports, false)?;
                    judgment::seed(tc, entries);
                }
                #[cfg(feature = "trace")]
                let tc0 = std::time::Instant::now();
                judgment::run_memo(tc, depth, eager, call, &mut levels)?;
                #[cfg(feature = "trace")]
                {
                    seeding += tc0 - ts;
                    slow.push(tc0.elapsed().as_micros());
                    times.push(u64::try_from(ts.elapsed().as_nanos()).unwrap_or(u64::MAX));
                }
            }
            #[cfg(feature = "trace")]
            {
                *judgment::CALL_TIMES.lock().unwrap() = times;
            }
            #[cfg(feature = "trace")]
            if std::env::var_os("NANODA_OP_TIMES").is_some() {
                slow.sort_by_key(|&x| core::cmp::Reverse(x));
                std::eprintln!("op: seeding {seeding:?}, all {:?} ({} calls; slowest {:?} µs)", t0.elapsed(), slow.len(), &slow[..slow.len().min(5)]);
            }
            for blob in subjects {
                let header = judgment::header(blob)?;
                if header.declaration != hash {
                    return Err("a judgment for another declaration".into());
                }
                let mut l = judgment::Lazy::new(&header)?;
                let entries = (0..l.len()).map(|k| l.entry(tc, k)).collect::<Result<Vec<_>, _>>()?;
                self.check_imports(tc, &entries, &header.imports, true)?;
                if !entries.iter().all(|e| judgment::holds(tc, e)) {
                    return Err("an entry the calls didn't make".into());
                }
            }
            Ok(())
        })
    }

    /// Plan judgments for node `i`'s declaration (one with a value): record its check, and cut it
    /// into ops that each fit `cfg` (see [`crate::plan`]). Type errors panic.
    #[cfg(feature = "trace")]
    pub fn plan_judgments(&self, i: usize, cfg: &crate::plan::PlanConfig) -> Result<crate::plan::Plan, Box<dyn Error>> {
        let d = self.single(i)?;
        let val = match d {
            Declar::Theorem { val, .. } | Declar::Definition { val, .. } | Declar::Opaque { val, .. } => *val,
            _ => return Err("judgments for a declaration without a value".into()),
        };
        let hash = self.nodes[i].hash;
        self.file.with_tc_and_declar(*d.info(), |tc| {
            tc.rec = Some(Box::new(crate::record::Recorder::new()));
            tc.check_declar_info(d).unwrap();
            let inferred_type = tc.infer(val, InferFlag::Check);
            tc.assert_def_eq(inferred_type, d.info().ty);
            let mut rec = tc.rec.take().unwrap();
            rec.finish();
            crate::plan::plan(tc, &rec, &hash, cfg, |tc, entries| {
                let imports = self.judgment_imports(tc, entries);
                if imports.is_none() {
                    for n in judgment::mentions(tc, entries).into_iter().filter(|&n| self.declared_by(n).is_none()) {
                        std::eprintln!("not declared by a loaded node: {:?}", tc.ctx.debug_print(n));
                    }
                }
                imports
            })
        })
    }

    /// Check that node `theorem` is a theorem with no universe parameters whose type is exactly
    /// the constant node `statement` declares, a definition of type `Prop` with no universe
    /// parameters. Does not type-check anything; see [`Self::check`].
    pub fn check_binding(&self, statement: usize, theorem: usize) -> Result<(), String> {
        let declar = |i: usize| -> Result<&Declar<'p>, String> {
            let node = &self.nodes[i];
            if node.declars.len() != 1 {
                return Err("not a single declaration".into());
            }
            Ok(self.file.declars.get_index(node.declars.start).unwrap().1)
        };
        self.file.with_ctx(|ctx| {
            let Declar::Definition { info: statement_info, .. } = declar(statement)? else {
                return Err("the statement is not a definition".into());
            };
            if !ctx.read_levels(statement_info.uparams).is_empty() {
                return Err("the statement has universe parameters".into());
            }
            match ctx.read_expr(statement_info.ty) {
                Expr::Sort { level, .. } if ctx.read_level(level) == Level::Zero => {},
                _ => return Err("the statement is not a Prop".into()),
            }
            let Declar::Theorem { info, .. } = declar(theorem)? else {
                return Err("not a theorem".into());
            };
            if self.nodes[theorem].assumed {
                return Err("the theorem is assumed, not proven".into());
            }
            if !ctx.read_levels(info.uparams).is_empty() {
                return Err("the theorem has universe parameters".into());
            }
            match ctx.read_expr(info.ty) {
                Expr::Const { name, levels, .. }
                    if name == statement_info.name && ctx.read_levels(levels).is_empty() => Ok(()),
                _ => Err("the theorem does not have the statement as its type".into()),
            }
        })
    }
}

/// Which declarations the kernel looks up, by index into the export file's declarations, for
/// planning what a check needs to trust.
#[cfg(feature = "trace")]
pub mod trace {
    use std::{
        collections::BTreeSet,
        sync::{
            Mutex,
            atomic::{AtomicBool, Ordering},
        },
    };

    static ON: AtomicBool = AtomicBool::new(false);
    static LOOKUPS: Mutex<BTreeSet<usize>> = Mutex::new(BTreeSet::new());

    pub(crate) fn record(declar: usize) {
        if ON.load(Ordering::Relaxed) {
            LOOKUPS.lock().unwrap().insert(declar);
        }
    }

    /// Start recording.
    pub fn start() {
        LOOKUPS.lock().unwrap().clear();
        ON.store(true, Ordering::Relaxed);
    }

    /// Stop recording, and return what was looked up.
    pub fn stop() -> BTreeSet<usize> {
        ON.store(false, Ordering::Relaxed);
        core::mem::take(&mut *LOOKUPS.lock().unwrap())
    }
}
