//! Planning judgments for a declaration too heavy for one check (witness-lean's
//! `docs/design/heavy-declarations.md`): from a recorded check (`crate::record`), cut the kernel's
//! calls into *units* that each fit a budget, order them into rounds, group each round's units
//! into ops, and write each op's calls and the judgment it attests.
//!
//! A unit is a kernel call, run on its own with the judgments it needs seeded. Its *region* is
//! its call minus the units inside it, whose results it's seeded with instead. The declaration's
//! check itself is the last unit, its attestation as usual, citing what it needs.
//!
//! - A unit needs the entries it hits that were made outside its region: it cites the unit whose
//!   region made each. One made by a unit enclosing it would be circular; the call that made it
//!   becomes a unit of its own instead (or, where that call's result isn't a cache entry, its
//!   nearest enclosing call whose is).
//! - A unit needs its nested units' results, which are cache entries: only a call whose own
//!   result is one can be a unit (not a lazy delta step), or its parent would compute it again.
//! - A unit whose own work is over budget gives up its biggest calls that fit, and then, if it
//!   must, the calls with the most time of their own.
//!
//! Every judgment a unit needs is made in an earlier round, so attesting goes round by round.
use crate::judgment::{self, Call, Entry, Outcome};
use crate::nodes::Hash;
use crate::record::Recorder;
use crate::tc::TypeChecker;
use crate::util::{FxHashMap, FxHashSet, new_fx_hash_map, new_fx_hash_set};
use std::vec;
use std::vec::Vec;

/// Limits for planning.
#[derive(Clone, Debug)]
pub struct PlanConfig {
    /// Most native time a unit's own work may take, in nanoseconds.
    pub budget_ns: u64,
    /// The work a kernel call counts for when cutting units, in nanoseconds.
    pub ns_per_call: u64,
    /// Gas a native nanosecond of the kernel costs in PolkaVM.
    pub gas_per_ns: f64,
    /// Gas loading the declaration's environment costs.
    pub env_gas: f64,
    /// Gas a byte of cited (or attested) judgment costs to rebuild and seed.
    pub gas_per_byte: f64,
    /// Most gas an op may plan for.
    pub op_gas: f64,
    /// Most judgments an op may cite, and their most bytes.
    pub max_cites: usize,
    pub max_cited_bytes: usize,
    /// Each unit's measured replay time (by its call's index in the record), in nanoseconds,
    /// from checking an earlier plan's ops: a unit's replay doesn't depend on its op.
    pub unit_costs: Option<std::collections::HashMap<usize, u64>>,
    /// Most native time an op may plan for, in nanoseconds: its fixed cost, its environment and
    /// blobs at `ns_per_byte`, what it cites at `ns_per_cited_byte`, and its units' replays.
    pub op_ns: u64,
    pub fixed_ns: u64,
    pub env_bytes: usize,
    pub ns_per_byte: f64,
    pub ns_per_cited_byte: f64,
}

impl Default for PlanConfig {
    fn default() -> Self {
        PlanConfig {
            budget_ns: 25_000_000,
            ns_per_call: 1_000,
            gas_per_ns: 94.0,
            env_gas: 6e8,
            gas_per_byte: 300.0,
            op_gas: 4.0e9,
            max_cites: 3000,
            max_cited_bytes: 12_000_000,
            unit_costs: None,
            op_ns: 40_000_000,
            fixed_ns: 4_000_000,
            env_bytes: 600_000,
            ns_per_byte: 13.0,
            ns_per_cited_byte: 4.0,
        }
    }
}

/// One op: some units, run as calls, attesting one judgment.
pub struct Group {
    pub round: usize,
    /// The calls blob (the op's witness, with the declaration's node).
    pub calls: Vec<u8>,
    /// The judgment it attests (its subject).
    pub judgment: Vec<u8>,
    /// The groups whose judgments it cites, by index.
    pub cites: Vec<usize>,
    pub units: usize,
    /// Its estimated gas.
    pub gas: f64,
    /// Each unit's call (its index in the record), its time and its own work, in nanoseconds.
    pub unit_ns: Vec<(usize, u64, u64)>,
}

pub struct Plan {
    pub groups: Vec<Group>,
    /// What the declaration's own attestation cites, and its estimated gas.
    pub final_cites: Vec<usize>,
    pub final_gas: f64,
    pub calls: usize,
    pub units: usize,
    pub rounds: usize,
    /// Hits on entries a unit's enclosing unit made: needs it can't cite, so recomputes.
    pub skipped: usize,
}

/// The cache entry a call's result is, if the call made it.
fn result_entry<'t>(rec: &Recorder<'t>, i: usize) -> Option<Entry<'t>> {
    let c = &rec.calls[i];
    let idx = u32::try_from(i).ok()?;
    let entry = match (c.call?, c.outcome?) {
        (Call::Infer(e, true), Outcome::Expr(t)) => Entry::Infer(e, t),
        (Call::Infer(e, false), Outcome::Expr(t)) => Entry::InferOnly(e, t),
        (Call::Whnf(e), Outcome::Expr(v)) => Entry::Whnf(e, v),
        (Call::DefEq(x, y), Outcome::Bool(true)) => Entry::DefEq(x, y),
        (Call::DefEq(x, y), Outcome::Bool(false)) => {
            [Entry::DefEqFail(x, y, false), Entry::DefEqFail(x, y, true)].into_iter().find(|e| rec.made.get(e) == Some(&idx))?
        },
        _ => return None,
    };
    let entry = entry.normal();
    (rec.made.get(&entry) == Some(&idx)).then_some(entry)
}

/// Plan the recorded check in `tc` (a checker for declaration node `declaration`). `imports`
/// gives a judgment's imports (the nodes declaring what its entries mention).
pub(crate) fn plan<'t, 'p>(
    tc: &TypeChecker<'_, 't, 'p>,
    rec: &Recorder<'t>,
    declaration: &Hash,
    cfg: &PlanConfig,
    imports: impl Fn(&TypeChecker<'_, 't, 'p>, &[Entry<'t>]) -> Option<Vec<Hash>>,
) -> Result<Plan, std::boxed::Box<dyn core::error::Error>> {
    let n = rec.calls.len();
    let parent: Vec<usize> = rec.calls.iter().map(|c| c.parent as usize).collect();
    let end: Vec<usize> = rec.calls.iter().map(|c| c.end as usize).collect();
    // A call's work, for cutting units: the calls made under it, at `ns_per_call` each, rather
    // than its measured time, so the same check is cut into the same units every time (and a
    // unit's measured replay, from an earlier plan, applies to the same unit in the next).
    let ns: Vec<u64> = (0..n).map(|i| (end[i] - i + 1) as u64 * cfg.ns_per_call).collect();
    let mut excl = ns.clone();
    for i in 1..n {
        excl[parent[i]] = excl[parent[i]].saturating_sub(ns[i]);
    }
    let result: Vec<Option<Entry<'t>>> = (0..n).map(|i| if i == 0 { None } else { result_entry(rec, i) }).collect();
    let cacheable = |i: usize| result[i].is_some();
    // Whether call `a` encloses call `b` (or is it).
    let encloses = |a: usize, b: usize| a <= b && b <= end[a];

    let mut is_unit = vec![false; n];
    is_unit[0] = true;
    for i in 1..n {
        if parent[i] == 0 && cacheable(i) {
            is_unit[i] = true;
        }
    }
    let mut unit_of = vec![0usize; n];
    loop {
        for i in 1..n {
            unit_of[i] = if is_unit[i] { i } else { unit_of[parent[i]] };
        }
        let mut promote: FxHashSet<usize> = new_fx_hash_set();
        // An entry a unit needs from outside its region: the call that made it becomes a unit (or,
        // where that call's result isn't an entry, its nearest enclosing call whose is, inside
        // the maker's region), so units stay small and needs shallow, and none is circular.
        for &(at, entry) in &rec.hits {
            let m = rec.made[&entry] as usize;
            let (u, maker) = (unit_of[at as usize], unit_of[m]);
            if u == maker || encloses(m, u) {
                continue;
            }
            let mut c = m;
            while c != maker && !cacheable(c) {
                c = parent[c];
            }
            if c != maker && !encloses(c, u) {
                promote.insert(c);
            }
        }
        // Units over budget give up calls: in each one's region, the biggest calls whose work,
        // less the units inside them, fits the budget, and that no call that fits encloses.
        let mut own = ns.clone();
        let mut left = ns.clone();
        for i in 1..n {
            if is_unit[i] {
                let r = unit_of[parent[i]];
                own[r] = own[r].saturating_sub(ns[i]);
                let mut a = parent[i];
                while a != r {
                    left[a] = left[a].saturating_sub(ns[i]);
                    a = parent[a];
                }
            }
        }
        let over: FxHashSet<usize> = (0..n).filter(|&r| is_unit[r] && own[r] > cfg.budget_ns).collect();
        if !over.is_empty() {
            let fits = |i: usize| cacheable(i) && left[i] <= cfg.budget_ns;
            let mut covered = vec![false; n];
            let mut candidates: FxHashMap<usize, Vec<usize>> = new_fx_hash_map();
            for i in 1..n {
                if is_unit[i] {
                    continue;
                }
                let p = parent[i];
                covered[i] = !is_unit[p] && (covered[p] || fits(p));
                let r = unit_of[i];
                if over.contains(&r) && fits(i) && !covered[i] {
                    candidates.entry(r).or_default().push(i);
                }
            }
            for (r, mut ks) in candidates {
                ks.sort_by_key(|&k| core::cmp::Reverse(left[k]));
                let mut rest = own[r];
                for k in ks {
                    if rest <= cfg.budget_ns {
                        break;
                    }
                    promote.insert(k);
                    rest = rest.saturating_sub(left[k]);
                }
            }
        }
        promote.retain(|&p| !is_unit[p]);
        if promote.is_empty() {
            break;
        }
        for p in promote {
            is_unit[p] = true;
        }
    }

    // Each unit's needs (the units whose judgments it cites) and what it publishes.
    let units: Vec<usize> = (0..n).filter(|&i| is_unit[i]).collect();
    let mut needs: FxHashMap<usize, FxHashSet<usize>> = units.iter().map(|&u| (u, new_fx_hash_set())).collect();
    let mut publish: FxHashMap<usize, FxHashSet<Entry<'t>>> = units.iter().map(|&u| (u, new_fx_hash_set())).collect();
    // The entries each unit needs from other units, in the order it first hit them.
    let mut need_entries: FxHashMap<usize, Vec<Entry<'t>>> = units.iter().map(|&u| (u, Vec::new())).collect();
    let mut needed_seen: FxHashSet<(usize, Entry<'t>)> = new_fx_hash_set();
    let mut skipped = 0usize;
    for &(at, entry) in &rec.hits {
        let m = rec.made[&entry] as usize;
        let (u, maker) = (unit_of[at as usize], unit_of[m]);
        if u == maker {
            continue;
        }
        if encloses(maker, u) {
            skipped += 1;
            continue;
        }
        needs.get_mut(&u).unwrap().insert(maker);
        publish.get_mut(&maker).unwrap().insert(entry);
        if needed_seen.insert((u, entry)) {
            need_entries.get_mut(&u).unwrap().push(entry);
        }
    }
    for &u in &units[1..] {
        let p = unit_of[parent[u]];
        needs.get_mut(&p).unwrap().insert(u);
        let r = result[u].unwrap();
        publish.get_mut(&u).unwrap().insert(r);
        if needed_seen.insert((p, r)) {
            need_entries.get_mut(&p).unwrap().push(r);
        }
    }
    // Which unit made each entry a unit needs.
    let maker_unit = |e: &Entry<'t>| unit_of[rec.made[e] as usize];
    let mut own = ns.clone();
    for &u in &units[1..] {
        let p = unit_of[parent[u]];
        own[p] = own[p].saturating_sub(ns[u]);
    }
    // Rounds: a unit after everything it needs, which all finish before it ends.
    let mut order = units.clone();
    order.sort_by_key(|&u| (end[u], core::cmp::Reverse(u)));
    let mut round: FxHashMap<usize, usize> = new_fx_hash_map();
    for &u in &order {
        let r = needs[&u].iter().map(|v| round.get(v).copied().ok_or("a unit needs one after it")).collect::<Result<Vec<_>, _>>()?;
        round.insert(u, 1 + r.into_iter().max().unwrap_or(0));
    }
    let rounds = round[&0];
    // A unit's cost in its op, in native nanoseconds: its measured replay, or its own work and a
    // little per call; and the bytes its call and what it publishes add to its op.
    let cost = |u: usize| -> u64 {
        cfg.unit_costs.as_ref().and_then(|c| c.get(&u).copied()).unwrap_or(own[u] + 3_000)
    };
    let unit_bytes = |u: usize| publish[&u].len() * 64 + 32;

    // Group each round's units (the declaration's own, last, apart) in call order.
    let mut group_of: FxHashMap<usize, usize> = new_fx_hash_map();
    let mut groups: Vec<Group> = Vec::new();
    let mut blob_bytes: Vec<usize> = Vec::new();
    // Each group's entries, by their position in its judgment.
    let mut entry_index: Vec<FxHashMap<Entry<'t>, usize>> = Vec::new();
    for r in 1..rounds {
        let mut members: Vec<usize> = units.iter().copied().filter(|&u| u != 0 && round[&u] == r).collect();
        members.sort_unstable();
        let mut cur: Vec<usize> = Vec::new();
        let mut cites: FxHashSet<usize> = new_fx_hash_set();
        let (mut work, mut cited, mut bytes) = (0u64, 0usize, 0usize);
        #[allow(clippy::too_many_arguments)]
        let close = |cur: &mut Vec<usize>,
                     cites: &mut FxHashSet<usize>,
                     work: &mut u64,
                     cited: &mut usize,
                     groups: &mut Vec<Group>,
                     group_of: &mut FxHashMap<usize, usize>,
                     blob_bytes: &mut Vec<usize>,
                     entry_index: &mut Vec<FxHashMap<Entry<'t>, usize>>|
         -> Result<(), std::boxed::Box<dyn core::error::Error>> {
            if cur.is_empty() {
                return Ok(());
            }
            let mut cites: Vec<usize> = cites.drain().collect();
            cites.sort_unstable();
            let position: FxHashMap<usize, usize> = cites.iter().enumerate().map(|(j, &g)| (g, j)).collect();
            // Each unit's call, seeded just before it with what it needs (once in the op).
            let mut seeded: FxHashSet<Entry<'t>> = new_fx_hash_set();
            let mut calls: Vec<judgment::CallItem<'t>> = Vec::new();
            for &u in cur.iter() {
                let mut seeds = Vec::new();
                for e in &need_entries[&u] {
                    if seeded.insert(*e) {
                        let g = group_of[&maker_unit(e)];
                        seeds.push((position[&g], entry_index[g][e]));
                    }
                }
                calls.push((rec.calls[u].depth, rec.calls[u].eager, rec.calls[u].call.unwrap(), seeds));
            }
            let mut entries: Vec<Entry<'t>> = cur.iter().flat_map(|u| publish[u].iter().copied()).collect();
            entries.sort_by_key(|e| match e {
                Entry::Infer(a, _) | Entry::InferOnly(a, _) | Entry::Whnf(a, _) | Entry::WhnfCore(a, _) => a.get_hash(),
                Entry::DefEqFail(a, _, _) | Entry::DefEq(a, _) | Entry::CongrFail(a, _) => a.get_hash(),
            });
            let imp = imports(tc, &entries).ok_or("a judgment mentions a constant not declared by a loaded node")?;
            let judgment = judgment::write_judgment(tc, declaration, &imp, &entries);
            let calls = judgment::write_calls(tc, &calls);
            let g = groups.len();
            entry_index.push(entries.iter().enumerate().map(|(k, e)| (*e, k)).collect());
            for &u in cur.iter() {
                group_of.insert(u, g);
            }
            let est_ns = cfg.fixed_ns as f64
                + (cfg.env_bytes + judgment.len() + calls.len()) as f64 * cfg.ns_per_byte
                + *cited as f64 * cfg.ns_per_cited_byte
                + *work as f64;
            let gas = est_ns * cfg.gas_per_ns;
            blob_bytes.push(judgment.len());
            let unit_ns = cur.iter().map(|&u| (u, ns[u], own[u])).collect();
            groups.push(Group { round: r, calls, judgment, cites, units: cur.len(), gas, unit_ns });
            cur.clear();
            *work = 0;
            *cited = 0;
            Ok(())
        };
        for u in members {
            let mine: FxHashSet<usize> = needs[&u].iter().map(|v| group_of[v]).collect();
            let add: Vec<usize> = mine.iter().copied().filter(|g| !cites.contains(g)).collect();
            let add_bytes: usize = add.iter().map(|&g| blob_bytes[g]).sum();
            let est_ns = cfg.fixed_ns as f64
                + (cfg.env_bytes + bytes + unit_bytes(u)) as f64 * cfg.ns_per_byte
                + (cited + add_bytes) as f64 * cfg.ns_per_cited_byte
                + (work + cost(u)) as f64;
            let over = est_ns > cfg.op_ns as f64 || cites.len() + add.len() > cfg.max_cites || cited + add_bytes > cfg.max_cited_bytes;
            if over && !cur.is_empty() {
                close(&mut cur, &mut cites, &mut work, &mut cited, &mut groups, &mut group_of, &mut blob_bytes, &mut entry_index)?;
                bytes = 0;
            }
            for g in mine {
                if cites.insert(g) {
                    cited += blob_bytes[g];
                }
            }
            cur.push(u);
            work += cost(u);
            bytes += unit_bytes(u);
        }
        close(&mut cur, &mut cites, &mut work, &mut cited, &mut groups, &mut group_of, &mut blob_bytes, &mut entry_index)?;
    }
    let mut final_cites: Vec<usize> = needs[&0].iter().map(|v| group_of[v]).collect::<FxHashSet<_>>().into_iter().collect();
    final_cites.sort_unstable();
    let final_gas = (cfg.fixed_ns as f64
        + cfg.env_bytes as f64 * cfg.ns_per_byte
        + final_cites.iter().map(|&g| blob_bytes[g]).sum::<usize>() as f64 * cfg.ns_per_byte
        + cost(0) as f64)
        * cfg.gas_per_ns;
    Ok(Plan { groups, final_cites, final_gas, calls: n - 1, units: units.len(), rounds, skipped })
}

