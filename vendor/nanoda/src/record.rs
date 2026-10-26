//! Recording the kernel's calls and cache traffic while it checks a declaration, for planning
//! judgments (see [`crate::plan`]). Only with the `trace` feature; the kernel's hooks are no-ops
//! otherwise.
use crate::judgment::{Call, Entry, Outcome};
use crate::util::{FxHashMap, new_fx_hash_map};
use std::time::Instant;
use std::vec;
use std::vec::Vec;

/// One kernel call (an inference, a reduction, a definitional equality or a lazy delta step).
pub(crate) struct CallRec<'t> {
    pub(crate) call: Option<Call<'t>>,
    /// The de Bruijn level counter at its start, and whether it ran in eager mode.
    pub(crate) depth: u16,
    pub(crate) eager: bool,
    /// The call it was made from (0, the declaration's check itself, for a top-level call).
    pub(crate) parent: u32,
    /// The last call made inside it.
    pub(crate) end: u32,
    /// Its time, including the calls made inside it, in nanoseconds.
    pub(crate) ns: u64,
    pub(crate) outcome: Option<Outcome<'t>>,
}

pub(crate) struct Recorder<'t> {
    /// Every call, in the order made; index 0 stands for the declaration's check itself.
    pub(crate) calls: Vec<CallRec<'t>>,
    stack: Vec<(u32, Instant)>,
    start: Instant,
    /// The call each cache entry was first made in.
    pub(crate) made: FxHashMap<Entry<'t>, u32>,
    /// Every cache hit on an entry made here: the call it happened in, and the entry.
    pub(crate) hits: Vec<(u32, Entry<'t>)>,
}

impl<'t> Recorder<'t> {
    pub(crate) fn new() -> Self {
        let root = CallRec { call: None, depth: 0, eager: false, parent: 0, end: 0, ns: 0, outcome: None };
        Recorder { calls: vec![root], stack: Vec::new(), start: Instant::now(), made: new_fx_hash_map(), hits: Vec::new() }
    }

    fn current(&self) -> u32 {
        self.stack.last().map_or(0, |&(i, _)| i)
    }

    pub(crate) fn enter(&mut self, call: Call<'t>, depth: u16, eager: bool) -> u32 {
        let idx = u32::try_from(self.calls.len()).unwrap();
        let parent = self.current();
        self.calls.push(CallRec { call: Some(call), depth, eager, parent, end: idx, ns: 0, outcome: None });
        self.stack.push((idx, Instant::now()));
        crate::nodes::trace::set_call(idx);
        idx
    }

    pub(crate) fn exit(&mut self, idx: u32, outcome: Outcome<'t>) {
        let (top, t0) = self.stack.pop().unwrap();
        debug_assert_eq!(top, idx);
        crate::nodes::trace::set_call(self.current());
        let end = u32::try_from(self.calls.len() - 1).unwrap();
        let c = &mut self.calls[idx as usize];
        c.end = end;
        c.ns = u64::try_from(t0.elapsed().as_nanos()).unwrap_or(u64::MAX);
        c.outcome = Some(outcome);
    }

    pub(crate) fn hit(&mut self, entry: Entry<'t>) {
        let entry = entry.normal();
        if self.made.contains_key(&entry) {
            let at = self.current();
            self.hits.push((at, entry));
        }
    }

    pub(crate) fn made(&mut self, entry: Entry<'t>) {
        let entry = entry.normal();
        let at = self.current();
        self.made.entry(entry).or_insert(at);
    }

    /// Close the record: the declaration's check (index 0) spans every call.
    pub(crate) fn finish(&mut self) {
        let end = u32::try_from(self.calls.len() - 1).unwrap();
        let root = &mut self.calls[0];
        root.end = end;
        root.ns = u64::try_from(self.start.elapsed().as_nanos()).unwrap_or(u64::MAX);
    }
}
