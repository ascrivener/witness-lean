//! Checking an export in layers, and binding a proof to a bounty's statement.
//!
//! An export can be split into consecutive parts, or layers. Each continues the numbering of
//! names, levels and expressions of the ones before, so a layer only means something after the
//! exact layers it was exported after. [`parse`] reads the layers as one export, and [`Layers`]
//! knows which declarations each one added, so a caller can type-check only some of them (the
//! others having been checked before, in the same context).
//!
//! For a bounty, the poster's statement environment is a prefix of the layers: an export of a
//! `Prop`-valued definition (the statement) and everything it depends on. The solver's delta is
//! the last layer, adding the proof. The proof is accepted when:
//!
//! - all the layers parse as one export. A layer that redeclares any name fails here, because
//!   duplicate declaration names are rejected;
//! - only [`PERMITTED_AXIOMS`] are used (any other axiom is a hard error);
//! - the statement is a definition with no universe parameters and type `Prop`, before the delta;
//! - the theorem is a theorem in the delta with no universe parameters, and its type is exactly
//!   the statement constant;
//! - every declaration not checked before type-checks.
//!
//! Type errors panic, as everywhere in this checker; binding violations are returned as errors.
#[allow(unused_imports)]
use crate::prelude::*;
use crate::env::Declar;
use crate::expr::Expr;
use crate::level::Level;
use crate::name::Name;
use crate::util::{Config, ExportFile, NamePtr, TcCtx};
use core::error::Error;
use core::ops::Range;

/// The axioms a proof may rely on.
pub const PERMITTED_AXIOMS: [&str; 3] = ["propext", "Classical.choice", "Quot.sound"];

/// An export read in layers.
pub struct Layers<'p> {
    pub file: ExportFile<'p>,
    /// The number of declarations after each layer.
    ends: Vec<usize>,
}

/// Parse `parts` as one export, in order, permitting only [`PERMITTED_AXIOMS`]. Each part may be
/// lean4export NDJSON or the binary format.
pub fn parse<'p>(parts: &[&[u8]]) -> Result<Layers<'p>, Box<dyn Error>> {
    let mut config = Config::in_memory(PERMITTED_AXIOMS.map(String::from).into());
    config.unpermitted_axiom_hard_error = true;
    let (file, _skipped, ends) = crate::parser::parse_export_parts(parts, config)?;
    Ok(Layers { file, ends })
}

fn name_string<'t>(ctx: &TcCtx<'t, '_>, n: NamePtr<'t>) -> String {
    let (prefix, last) = match ctx.read_name(n) {
        Name::Anon => return String::new(),
        Name::Str(pfx, sfx, _) => (pfx, ctx.read_string(sfx).to_string()),
        Name::Num(pfx, i, _) => (pfx, i.to_string()),
    };
    let mut s = name_string(ctx, prefix);
    if !s.is_empty() {
        s.push('.');
    }
    s + &last
}

impl<'p> Layers<'p> {
    /// How many layers there are.
    pub fn len(&self) -> usize {
        self.ends.len()
    }

    pub fn is_empty(&self) -> bool {
        self.ends.is_empty()
    }

    /// The declarations layer `i` added, as indices into `file.declars`.
    pub fn layer(&self, i: usize) -> Range<usize> {
        let start = if i == 0 { 0 } else { self.ends[i - 1] };
        start..self.ends[i]
    }

    /// The declarations of layers `layers`.
    pub fn layers(&self, layers: Range<usize>) -> Range<usize> {
        if layers.is_empty() {
            return 0..0;
        }
        self.layer(layers.start).start..self.layer(layers.end - 1).end
    }

    /// Type-check declarations `declars` (panics on an error). Each is checked against the
    /// environment of everything before it.
    pub fn check(&self, declars: Range<usize>) {
        for i in declars {
            self.file.check_declar(self.file.declars.get_index(i).unwrap().1);
        }
    }

    /// Check that `theorem`, declared in `theorem_in`, proves exactly `statement`, declared in
    /// `statement_in`. Does not type-check anything; see [`Self::check`].
    pub fn check_binding(
        &self,
        statement: &str,
        statement_in: Range<usize>,
        theorem: &str,
        theorem_in: Range<usize>,
    ) -> Result<(), String> {
        let declars = &self.file.declars;
        self.file.with_ctx(|ctx| {
            let find = |range: Range<usize>, wanted: &str| {
                range.filter_map(|i| declars.get_index(i)).find(|(n, _)| name_string(ctx, **n) == wanted)
            };

            let (&statement_name, statement_declar) = find(statement_in, statement)
                .ok_or_else(|| format!("statement {statement} is not in the environment"))?;
            let Declar::Definition { info, .. } = statement_declar else {
                return Err(format!("statement {statement} is not a definition"));
            };
            if !ctx.read_levels(info.uparams).is_empty() {
                return Err(format!("statement {statement} has universe parameters"));
            }
            match ctx.read_expr(info.ty) {
                Expr::Sort { level, .. } if ctx.read_level(level) == Level::Zero => {},
                _ => return Err(format!("statement {statement} is not a Prop")),
            }

            let (_, theorem_declar) = find(theorem_in, theorem)
                .ok_or_else(|| format!("theorem {theorem} is not in the submission"))?;
            let Declar::Theorem { info, .. } = theorem_declar else {
                return Err(format!("{theorem} is not a theorem"));
            };
            if !ctx.read_levels(info.uparams).is_empty() {
                return Err(format!("theorem {theorem} has universe parameters"));
            }
            match ctx.read_expr(info.ty) {
                Expr::Const { name, levels, .. }
                    if name == statement_name && ctx.read_levels(levels).is_empty() => Ok(()),
                _ => Err(format!("theorem {theorem} does not have type {statement}")),
            }
        })
    }
}
