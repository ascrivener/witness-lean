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
    /// An op's gas, estimated (fit to ops measured in PolkaVM, `tools/lean/heavy_bench.py`): per
    /// native nanosecond of its units' replays (as measured, seeding included), and besides them a
    /// fixed amount, and per byte of its environment, of what it attests and its calls, and of
    /// what it cites. `env_bytes` is a typical op's environment: which nodes an op looks up isn't
    /// known when planning.
    pub gas_per_ns: f64,
    pub fixed_gas: f64,
    pub env_bytes: usize,
    pub gas_per_env_byte: f64,
    pub gas_per_own_byte: f64,
    pub gas_per_cited_byte: f64,
    /// Most gas an op may plan for: below witness's 5×10⁹ by the estimate's error.
    pub op_gas: f64,
    /// A unit not yet measured replays in about this times its calls at `ns_per_call`.
    pub unmeasured_scale: f64,
    /// Most judgments an op may cite, and their most bytes.
    pub max_cites: usize,
    pub max_cited_bytes: usize,
    /// Most bytes an op's calls blob may have: it's the op's witness, with the declaration's
    /// node, and an attest op's witness is at most witness's `MAX_WITNESS_LEN` (64 KiB).
    pub max_calls_bytes: usize,
    /// An op citing more judgment bytes than this cites relays instead (see `plan`).
    pub relay_bytes: usize,
    /// Each unit's measured replay time (by its call's index in the record), in nanoseconds,
    /// from checking an earlier plan's ops: a unit's replay doesn't depend on its op.
    pub unit_costs: Option<std::collections::HashMap<usize, u64>>,
    /// Write each op's entries as several judgments, split by which ops seed them, so that an op
    /// cites only blobs holding what it needs, rather than whole ops' judgments (see `split`).
    /// Relays are then not needed.
    pub fine: bool,
    /// What a judgment blob costs beyond its entries, in bytes: its header's imports, and the
    /// subterms it repeats from its op's other blobs. Splitting must save more than this.
    pub blob_overhead: f64,
    /// A byte of an op's own judgment costs this many bytes cited.
    pub own_per_cited: f64,
    /// Most judgments an op may attest.
    pub max_blobs: usize,
    /// Planning in fine mode, an op's cited bytes are its needed entries' share of their ops'
    /// judgments times this.
    pub cite_factor: f64,
}

impl Default for PlanConfig {
    fn default() -> Self {
        PlanConfig {
            budget_ns: 25_000_000,
            ns_per_call: 1_000,
            gas_per_ns: 23.5,
            fixed_gas: 0.0,
            env_bytes: 250_000,
            gas_per_env_byte: 1100.0,
            gas_per_own_byte: 350.0,
            gas_per_cited_byte: 30.0,
            op_gas: 3.0e9,
            unmeasured_scale: 2.6,
            max_cites: 3000,
            max_cited_bytes: 11_000_000,
            max_calls_bytes: 55_000,
            relay_bytes: 3_000_000,
            unit_costs: None,
            fine: true,
            blob_overhead: 2000.0,
            own_per_cited: 12.0,
            max_blobs: 512,
            cite_factor: 2.0,
        }
    }
}

/// One op: some units, run as calls, attesting one judgment, or several (`PlanConfig::fine`).
pub struct Group {
    pub round: usize,
    /// The calls blob (the op's witness, with the declaration's node).
    pub calls: Vec<u8>,
    /// The judgments it attests (its subjects).
    pub judgments: Vec<Vec<u8>>,
    /// Their indices among every op's judgments, in order (see `Plan::blob_group`).
    pub blobs: Vec<usize>,
    /// The judgments it cites, by index.
    pub cites: Vec<usize>,
    pub units: usize,
    /// Its estimated gas.
    pub gas: f64,
    /// Each unit's call (its index in the record), its time and its own work, in nanoseconds.
    pub unit_ns: Vec<(usize, u64, u64)>,
}

pub struct Plan {
    pub groups: Vec<Group>,
    /// The group attesting each judgment.
    pub blob_group: Vec<usize>,
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
        cfg.unit_costs.as_ref().and_then(|c| c.get(&u).copied()).unwrap_or_else(|| estimate((own[u] + 3_000) as f64 * cfg.unmeasured_scale) as u64)
    };
    // An op's estimated gas, from what it attests and its calls (bytes), what it cites (bytes) and
    // its units' replays (native nanoseconds).
    let op_gas = |own: usize, cited: usize, work: u64| {
        cfg.fixed_gas
            + cfg.env_bytes as f64 * cfg.gas_per_env_byte
            + own as f64 * cfg.gas_per_own_byte
            + cited as f64 * cfg.gas_per_cited_byte
            + work as f64 * cfg.gas_per_ns
    };
    let unit_bytes = |u: usize| publish[&u].len() * 64 + 32;

    // Group each round's units (the declaration's own, last, apart) in call order.
    let mut group_of: FxHashMap<usize, usize> = new_fx_hash_map();
    let mut groups: Vec<Group> = Vec::new();
    let mut blob_bytes: Vec<usize> = Vec::new();
    // Each group's entries, by their position in its judgment.
    let mut entry_index: Vec<FxHashMap<Entry<'t>, usize>> = Vec::new();
    // Each group's entries, in order, and its calls with the entries each seeds (for `split`).
    let mut group_entries: Vec<Vec<Entry<'t>>> = Vec::new();
    let mut group_calls: Vec<Vec<SeededCall<'t>>> = Vec::new();
    for r in 1..rounds {
        let mut members: Vec<usize> = units.iter().copied().filter(|&u| u != 0 && round[&u] == r).collect();
        members.sort_unstable();
        let mut cur: Vec<usize> = Vec::new();
        let mut cites: FxHashSet<usize> = new_fx_hash_set();
        let (mut work, mut cited, mut bytes) = (0u64, 0usize, 0usize);
        // In fine mode, the entries the op being built seeds.
        let mut op_entries: FxHashSet<Entry<'t>> = new_fx_hash_set();
        #[allow(clippy::too_many_arguments)]
        let close = |cur: &mut Vec<usize>,
                     cites: &mut FxHashSet<usize>,
                     work: &mut u64,
                     cited: &mut usize,
                     groups: &mut Vec<Group>,
                     group_of: &mut FxHashMap<usize, usize>,
                     blob_bytes: &mut Vec<usize>,
                     entry_index: &mut Vec<FxHashMap<Entry<'t>, usize>>,
                     group_entries: &mut Vec<Vec<Entry<'t>>>,
                     group_calls: &mut Vec<Vec<SeededCall<'t>>>|
         -> Result<(), std::boxed::Box<dyn core::error::Error>> {
            // Write `cur` as one op, or, where its calls would be more than an op's witness may
            // hold, as two or more, splitting it in halves.
            let first = core::mem::take(cur);
            let mut queue: std::collections::VecDeque<Vec<usize>> = Default::default();
            if !first.is_empty() {
                queue.push_back(first);
            }
            while let Some(units) = queue.pop_front() {
                // The entries each unit seeds, each once in the op, and the group that made each.
                let mut seeded: FxHashSet<Entry<'t>> = new_fx_hash_set();
                let unit_seeds: Vec<Vec<Entry<'t>>> = units
                    .iter()
                    .map(|u| need_entries[u].iter().copied().filter(|e| seeded.insert(*e)).collect())
                    .collect();
                let mut source: FxHashMap<Entry<'t>, (usize, usize)> = seeded
                    .iter()
                    .map(|e| {
                        let g = group_of[&maker_unit(e)];
                        (*e, (g, entry_index[g][e]))
                    })
                    .collect();
                let write = |cs: &[usize], source: &FxHashMap<Entry<'t>, (usize, usize)>| {
                    let position: FxHashMap<usize, usize> = cs.iter().enumerate().map(|(j, &g)| (g, j)).collect();
                    let calls: Vec<judgment::CallItem<'t>> = units
                        .iter()
                        .zip(&unit_seeds)
                        .map(|(&u, es)| {
                            let seeds = es.iter().map(|e| (position[&source[e].0], source[e].1)).collect();
                            (rec.calls[u].depth, rec.calls[u].eager, rec.calls[u].call.unwrap(), seeds)
                        })
                        .collect();
                    judgment::write_calls(tc, &calls)
                };
                let mut cs: Vec<usize> = source.values().map(|&(g, _)| g).collect::<FxHashSet<_>>().into_iter().collect();
                cs.sort_unstable();
                if write(&cs, &source).len() > cfg.max_calls_bytes && units.len() > 1 {
                    let (a, b) = units.split_at(units.len() / 2);
                    queue.push_front(b.to_vec());
                    queue.push_front(a.to_vec());
                    continue;
                }
                // Citing a lot for a few entries: relays, each citing some of those groups and
                // re-attesting just the entries this op needs from them, are cited instead.
                if !cfg.fine && cs.iter().map(|&g| blob_bytes[g]).sum::<usize>() > cfg.relay_bytes && cs.len() > 1 {
                    let mut chunks: Vec<Vec<usize>> = vec![Vec::new()];
                    let mut size = 0;
                    for &g in &cs {
                        if size + blob_bytes[g] > cfg.relay_bytes && !chunks.last().unwrap().is_empty() {
                            chunks.push(Vec::new());
                            size = 0;
                        }
                        chunks.last_mut().unwrap().push(g);
                        size += blob_bytes[g];
                    }
                    let mut direct = Vec::new();
                    for chunk in chunks {
                        if chunk.len() == 1 {
                            direct.push(chunk[0]);
                            continue;
                        }
                        let mut ents: Vec<Entry<'t>> = source.iter().filter(|(_, (g, _))| chunk.contains(g)).map(|(e, _)| *e).collect();
                        ents.sort_by_key(|e| (source[e].0, source[e].1));
                        let position: FxHashMap<usize, usize> = chunk.iter().enumerate().map(|(j, &g)| (g, j)).collect();
                        let seeds = ents.iter().map(|e| (position[&source[e].0], source[e].1)).collect();
                        let calls = judgment::write_calls(tc, &[(0, false, Call::Seed, seeds)]);
                        let imp = imports(tc, &ents).ok_or("a judgment mentions a constant not declared by a loaded node")?;
                        let relay = judgment::write_judgment(tc, declaration, &imp, &ents);
                        let rg = groups.len();
                        entry_index.push(ents.iter().enumerate().map(|(k, e)| (*e, k)).collect());
                        let cited_bytes: usize = chunk.iter().map(|&c| blob_bytes[c]).sum();
                        blob_bytes.push(relay.len());
                        let gas = op_gas(relay.len() + calls.len(), cited_bytes, 0);
                        groups.push(Group { round: r, calls, judgments: vec![relay], blobs: vec![rg], cites: chunk, units: 0, gas, unit_ns: Vec::new() });
                        group_calls.push(vec![(0, false, Call::Seed, ents.clone())]);
                        group_entries.push(ents.clone());
                        for (k, e) in ents.iter().enumerate() {
                            source.insert(*e, (rg, k));
                        }
                    }
                    cs = source.values().map(|&(g, _)| g).collect::<FxHashSet<_>>().into_iter().collect();
                    cs.sort_unstable();
                    let _ = direct;
                }
                let calls = write(&cs, &source);
                let mut entries: Vec<Entry<'t>> = units.iter().flat_map(|u| publish[u].iter().copied()).collect();
                entries.sort_by_key(|e| match e {
                    Entry::Infer(a, _) | Entry::InferOnly(a, _) | Entry::Whnf(a, _) | Entry::WhnfCore(a, _) => a.get_hash(),
                    Entry::DefEqFail(a, _, _) | Entry::DefEq(a, _) | Entry::CongrFail(a, _) => a.get_hash(),
                });
                let imp = imports(tc, &entries).ok_or("a judgment mentions a constant not declared by a loaded node")?;
                let judgment = judgment::write_judgment(tc, declaration, &imp, &entries);
                let g = groups.len();
                entry_index.push(entries.iter().enumerate().map(|(k, e)| (*e, k)).collect());
                for &u in &units {
                    group_of.insert(u, g);
                }
                let cited_bytes: usize = cs.iter().map(|&c| blob_bytes[c]).sum();
                let gas = op_gas(judgment.len() + calls.len(), cited_bytes, units.iter().map(|&u| cost(u)).sum());
                blob_bytes.push(judgment.len());
                let unit_ns = units.iter().map(|&u| (u, ns[u], own[u])).collect();
                groups.push(Group { round: r, calls, judgments: vec![judgment], blobs: vec![g], cites: cs, units: units.len(), gas, unit_ns });
                group_calls.push(units.iter().zip(&unit_seeds).map(|(&u, es)| (rec.calls[u].depth, rec.calls[u].eager, rec.calls[u].call.unwrap(), es.clone())).collect());
                group_entries.push(entries);
            }
            cites.clear();
            *work = 0;
            *cited = 0;
            Ok(())
        };
        // In fine mode, what unit `u`'s needs add to the cited bytes of an op seeding `op_entries`,
        // estimated as each entry's share of its group's judgment.
        let fine_add = |u: usize, op_entries: &FxHashSet<Entry<'t>>, group_of: &FxHashMap<usize, usize>, blob_bytes: &[usize], group_entries: &[Vec<Entry<'t>>]| {
            let bytes: f64 = need_entries[&u]
                .iter()
                .filter(|e| !op_entries.contains(*e))
                .map(|e| {
                    let g = group_of[&maker_unit(e)];
                    blob_bytes[g] as f64 / group_entries[g].len().max(1) as f64
                })
                .sum();
            estimate(bytes * cfg.cite_factor)
        };
        for u in members {
            let mine: FxHashSet<usize> = needs[&u].iter().map(|v| group_of[v]).collect();
            let add: Vec<usize> = mine.iter().copied().filter(|g| !cites.contains(g)).collect();
            let add_bytes: usize = if cfg.fine {
                fine_add(u, &op_entries, &group_of, &blob_bytes, &group_entries)
            } else {
                add.iter().map(|&g| blob_bytes[g]).sum()
            };
            let over = op_gas(bytes + unit_bytes(u), cited + add_bytes, work + cost(u)) > cfg.op_gas || cites.len() + add.len() > cfg.max_cites || cited + add_bytes > cfg.max_cited_bytes;
            if over && !cur.is_empty() {
                close(&mut cur, &mut cites, &mut work, &mut cited, &mut groups, &mut group_of, &mut blob_bytes, &mut entry_index, &mut group_entries, &mut group_calls)?;
                bytes = 0;
                op_entries.clear();
            }
            if cfg.fine {
                cited += fine_add(u, &op_entries, &group_of, &blob_bytes, &group_entries);
                op_entries.extend(need_entries[&u].iter().copied());
                cites.extend(mine);
            } else {
                for g in mine {
                    if cites.insert(g) {
                        cited += blob_bytes[g];
                    }
                }
            }
            cur.push(u);
            work += cost(u);
            bytes += unit_bytes(u);
        }
        close(&mut cur, &mut cites, &mut work, &mut cited, &mut groups, &mut group_of, &mut blob_bytes, &mut entry_index, &mut group_entries, &mut group_calls)?;
    }
    let mut final_cites: Vec<usize> = needs[&0].iter().map(|v| group_of[v]).collect::<FxHashSet<_>>().into_iter().collect();
    final_cites.sort_unstable();
    let mut blob_group: Vec<usize> = (0..groups.len()).collect();
    if cfg.fine {
        (blob_group, final_cites) = split(tc, declaration, cfg, &imports, &mut groups, &group_entries, &group_calls, &need_entries[&0])?;
    }
    let blob_len: Vec<usize> = groups.iter().flat_map(|g| g.judgments.iter().map(Vec::len)).collect();
    let final_gas = op_gas(0, final_cites.iter().map(|&b| blob_len[b]).sum(), cost(0));
    Ok(Plan { groups, blob_group, final_cites, final_gas, calls: n - 1, units: units.len(), rounds, skipped })
}

/// A byte count estimated as a float, as a whole number (rounded down, at least 0).
#[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
fn estimate(x: f64) -> usize {
    x.max(0.0) as usize
}

/// Entries seeded by the same ops (by index): the ops, the entries, and their judgment's size.
type Bucket<'t> = (Vec<usize>, Vec<Entry<'t>>, f64);

/// A merge of two buckets (by position), and what it gains.
type Merge = (f64, usize, usize);

/// A call to write, with the entries to seed before it.
type SeededCall<'t> = (u16, bool, Call<'t>, Vec<Entry<'t>>);

/// For `PlanConfig::fine`: split each group's judgment into blobs of the entries the same ops (or
/// the declaration's own check, `final_needs`) seed, merging blobs where a blob's overhead costs
/// more than the citing it saves, then rewrite every group's calls to cite just the blobs it seeds
/// from. Returns the group of each blob, and the blobs the declaration's own check cites.
#[allow(clippy::too_many_arguments)]
fn split<'t, 'p>(
    tc: &TypeChecker<'_, 't, 'p>,
    declaration: &Hash,
    cfg: &PlanConfig,
    imports: &impl Fn(&TypeChecker<'_, 't, 'p>, &[Entry<'t>]) -> Option<Vec<Hash>>,
    groups: &mut [Group],
    group_entries: &[Vec<Entry<'t>>],
    group_calls: &[Vec<SeededCall<'t>>],
    final_needs: &[Entry<'t>],
) -> Result<(Vec<usize>, Vec<usize>), std::boxed::Box<dyn core::error::Error>> {
    // The ops seeding each entry, the declaration's own check as `groups.len()`.
    let mut consumers: FxHashMap<Entry<'t>, Vec<usize>> = new_fx_hash_map();
    for (h, calls) in group_calls.iter().enumerate() {
        for e in calls.iter().flat_map(|c| &c.3) {
            consumers.entry(*e).or_default().push(h);
        }
    }
    for e in final_needs {
        consumers.entry(*e).or_default().push(groups.len());
    }
    for v in consumers.values_mut() {
        v.sort_unstable();
        v.dedup();
    }
    let old_cited: Vec<usize> = groups.iter().map(|g| g.cites.iter().map(|&c| groups[c].judgments[0].len()).sum()).collect();
    let mut blob_group = Vec::new();
    let mut place: FxHashMap<Entry<'t>, (usize, usize)> = new_fx_hash_map();
    // What each op (and the declaration's own check) cites so far, in bytes: a merge mustn't take
    // one past `max_cited_bytes`, or its arguments past what a work package holds.
    let mut cited_so_far = vec![0usize; groups.len() + 1];
    // Each group's entries, bucketed by the ops seeding them, with each bucket's size written
    // alone (a merged blob is at most its parts' sum); and what each op must still cite of the
    // groups not yet split, at least: the buckets it seeds from.
    let write = |es: &mut Vec<Entry<'t>>| -> Result<Vec<u8>, std::boxed::Box<dyn core::error::Error>> {
        es.sort_by_key(|e| e.terms()[0].get_hash());
        let imp = imports(tc, es).ok_or("a judgment mentions a constant not declared by a loaded node")?;
        Ok(judgment::write_judgment(tc, declaration, &imp, es))
    };
    let mut all_buckets: Vec<Vec<Bucket<'t>>> = Vec::new();
    let mut rest = vec![0f64; groups.len() + 1];
    for entries in group_entries {
        let mut by: std::collections::BTreeMap<&[usize], Vec<Entry<'t>>> = Default::default();
        for e in entries {
            by.entry(consumers.get(e).map_or(&[][..], Vec::as_slice)).or_default().push(*e);
        }
        let mut buckets = Vec::new();
        for (cs, mut es) in by {
            let size = write(&mut es)?.len() as f64;
            for &h in cs {
                rest[h] += size;
            }
            buckets.push((cs.to_vec(), es, size));
        }
        all_buckets.push(buckets);
    }
    for (g, mut buckets) in all_buckets.into_iter().enumerate() {
        let old_own = groups[g].judgments[0].len();
        // For weighing a merge, an entry's share of the group's whole judgment: blobs share
        // subterms, which their sizes written alone don't show.
        let per = old_own as f64 / group_entries[g].len().max(1) as f64;
        for (cs, _, size) in &buckets {
            for &h in cs {
                rest[h] -= size;
            }
        }
        // Merge the pair gaining most (a blob's overhead, made and cited, saved; less what each
        // side's consumers now cite of the other) while one gains, and while there are too many.
        let common = |a: &[usize], b: &[usize]| {
            let (mut i, mut j, mut n) = (0, 0, 0);
            while i < a.len() && j < b.len() {
                match a[i].cmp(&b[j]) {
                    core::cmp::Ordering::Less => i += 1,
                    core::cmp::Ordering::Greater => j += 1,
                    core::cmp::Ordering::Equal => (i, j, n) = (i + 1, j + 1, n + 1),
                }
            }
            n
        };
        // What each consumer will cite, with this group's blobs as they stand.
        let mut will: FxHashMap<usize, f64> = new_fx_hash_map();
        for (cs, _, size) in &buckets {
            for &h in cs {
                *will.entry(h).or_insert(cited_so_far[h] as f64) += size;
            }
        }
        let fits = |will: &FxHashMap<usize, f64>, gaining: &[usize], add: f64, other: &[usize]| {
            gaining.iter().filter(|h| other.binary_search(h).is_err()).all(|&h| will[&h] + add + rest[h] <= cfg.max_cited_bytes as f64)
        };
        while buckets.len() > 1 {
            // The best merge that fits, and, if there are too many blobs, the best of any.
            let (mut best, mut best_any): (Option<Merge>, Option<Merge>) = (None, None);
            let must = buckets.len() > cfg.max_blobs;
            for i in 0..buckets.len() {
                for j in i + 1..buckets.len() {
                    let ((sa, ea, na), (sb, eb, nb)) = (&buckets[i], &buckets[j]);
                    let fit = fits(&will, sb, *na, sa) && fits(&will, sa, *nb, sb);
                    let (na, nb) = (ea.len() as f64 * per, eb.len() as f64 * per);
                    if !fit && !must {
                        continue;
                    }
                    let c = common(sa, sb);
                    let union = (sa.len() + sb.len() - c) as f64;
                    let added = na * (sb.len() - c) as f64 + nb * (sa.len() - c) as f64;
                    let gain = cfg.blob_overhead * (cfg.own_per_cited + union) - added;
                    if fit && best.is_none_or(|(b, _, _)| gain > b) {
                        best = Some((gain, i, j));
                    }
                    if best_any.is_none_or(|(b, _, _)| gain > b) {
                        best_any = Some((gain, i, j));
                    }
                }
            }
            let Some((gain, i, j)) = (if must { best.or(best_any) } else { best }) else { break };
            if gain <= 0.0 && !must {
                break;
            }
            for (gaining, add, other) in [(&buckets[j].0, buckets[i].2, &buckets[i].0), (&buckets[i].0, buckets[j].2, &buckets[j].0)] {
                for h in gaining.iter().filter(|h| other.binary_search(h).is_err()) {
                    *will.get_mut(h).unwrap() += add;
                }
            }
            let (sb, eb, nb) = buckets.swap_remove(j);
            let a = &mut buckets[i];
            a.0.extend(sb);
            a.0.sort_unstable();
            a.0.dedup();
            a.1.extend(eb);
            a.2 += nb;
        }
        let mut judgments = Vec::new();
        let mut blobs = Vec::new();
        for (cs, mut es, _) in buckets {
            let j = write(&mut es)?;
            let b = blob_group.len();
            for (k, e) in es.iter().enumerate() {
                place.insert(*e, (b, k));
            }
            for h in cs {
                cited_so_far[h] += j.len();
            }
            judgments.push(j);
            blobs.push(b);
            blob_group.push(g);
        }
        let own: usize = judgments.iter().map(Vec::len).sum();
        groups[g].gas += (own as f64 - old_own as f64) * cfg.gas_per_own_byte;
        groups[g].judgments = judgments;
        groups[g].blobs = blobs;
    }
    let blob_len: Vec<usize> = groups.iter().flat_map(|g| g.judgments.iter().map(Vec::len)).collect();
    let cites_of = |es: &mut dyn Iterator<Item = &Entry<'t>>| {
        let mut cs: Vec<usize> = es.map(|e| place[e].0).collect::<FxHashSet<_>>().into_iter().collect();
        cs.sort_unstable();
        cs
    };
    for (h, calls) in group_calls.iter().enumerate() {
        let cs = cites_of(&mut calls.iter().flat_map(|c| &c.3));
        let position: FxHashMap<usize, usize> = cs.iter().enumerate().map(|(j, &b)| (b, j)).collect();
        let items: Vec<judgment::CallItem<'t>> = calls
            .iter()
            .map(|(depth, eager, call, es)| (*depth, *eager, *call, es.iter().map(|e| (position[&place[e].0], place[e].1)).collect()))
            .collect();
        let cited: usize = cs.iter().map(|&b| blob_len[b]).sum();
        let g = &mut groups[h];
        g.gas += (cited as f64 - old_cited[h] as f64) * cfg.gas_per_cited_byte;
        g.calls = judgment::write_calls(tc, &items);
        g.cites = cs;
    }
    let final_cites = cites_of(&mut final_needs.iter());
    Ok((blob_group, final_cites))
}

