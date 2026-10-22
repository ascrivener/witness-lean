# Design: content-addressed Lean, attested as a DAG

Status: proposal. Measurements below are on the infinite-primes and FLT-for-n = 4 closures;
nothing is built yet.

## Why

Today every blob is a layer of one positional export: each layer numbers its names, levels and
expressions on from the layers before. So a layer only means something after its exact prefix,
and every refine must parse that whole prefix. A refine of at most 4.5×10⁹ gas can parse about
4 MB, roughly 8,000 declarations. Infinite primes (2,945) fits; Mathlib (perhaps 50 times bigger)
never will, however it's cut.

The fix is to stop numbering things by position. If a declaration names what it uses by hash,
it means the same thing wherever it appears, and checking it needs only the declarations it
actually uses.

## Measurements (infinite primes, 3,321 declarations)

- **What checking a declaration needs.** Its *load set*: the constants it mentions, closed over
  the types of everything loaded and the values of definitions (which checking may unfold), but
  not theorem proofs. Median 41 declarations, 31 KB of NDJSON; 90th percentile 167 (203 KB);
  maximum 684 (1.1 MB). Today, the last layers parse 1.5 MB of binary, about 11 MB of NDJSON.
- **Depth.** The longest dependency path is 75 declarations, so attesting the whole closure
  takes at least 75 rounds, each in parallel across independent lemmas.
- **Proofs are never unfolded.** With the proofs of the first 33%, 66% or 90% of theorems
  replaced by axioms of the same statement, all 3,321 declarations still type-check (0
  failures). Checking a declaration needs other theorems' statements, never their proofs. The
  kernel can unfold a theorem's proof in principle, so this is measured, not guaranteed, and
  [the design keeps a way out](#if-a-proof-is-needed).
- **Proofs are two thirds of the bytes.** Of the closure's expression data, 64% is reachable only
  from theorem proofs.

### A bigger closure: FLT for n = 4

Mathlib's `fermatLastTheoremFour` (x⁴ + y⁴ ≠ z⁴) is a closure 2.5 times bigger. The positional
format can't take it at all: its last layers would parse 4.6 MB, about 4.6×10⁹ gas, more than a
refine allows. What a declaration needs grows far more slowly than the closure:

| | Infinite primes | FLT, n = 4 | Growth |
|---|---|---|---|
| Declarations | 3,321 | 8,328 | 2.5× |
| Closure, binary format | 1.5 MB | 4.6 MB | 3.0× |
| Native check of the whole closure | 0.98 s (≈ 28×10⁹ gas) | 2.4 s (≈ 70×10⁹ gas) | 2.5× |
| Load set, median | 41 (31 KB) | 51 (40 KB) | 1.3× |
| Load set, 90th percentile | 167 (203 KB) | 263 (295 KB) | 1.5× |
| Load set, largest | 684 (1.1 MB) | 1,395 (2.4 MB) | 2.2× |
| DAG depth | 75 | 92 | 1.2× |

Load sets are in declarations and NDJSON bytes; the binary format is about a seventh of NDJSON.
So total work grows with the library, as it must, but the work of any one check grows with what
it uses: the worst FLT check loads about 330 KB of binary statements, around 3.5×10⁸ gas to
parse.

## The format

A **declaration node** encodes one declaration (an inductive block, with its constructors and
recursors, is one node) on its own:

- local tables of names, levels and expressions, numbered from zero within the node;
- an **import table**: the hashes of the nodes it mentions, which its `const` expressions point
  into, and the names those nodes declare;
- its kind, name, universe parameters and type; for a definition, its value; for an inductive
  block, everything.

A theorem's node is its **statement**: everything but the proof. Its **proof** is separate: an
expression over the statement node's tables plus its own, with its own import table.

A node's **hash** is Blake2b-256 of its encoding. It covers the hashes it imports, so it commits
to everything the declaration means, recursively; two nodes with the same hash mean the same
thing anywhere. A theorem's hash doesn't cover its proof: anyone may prove it, any way.

A **batch** is a blob of nodes, in dependency order, so related declarations (a module's, say)
share one blob and one attestation.

`tools/lean` gets a converter from lean4export's NDJSON (no change to Lean or lean4export).

## Attestations

An attestation of batch B by the Lean check says: every node in B is valid, given that the nodes
it imports are. Concretely, in attest mode:

- **Trusted blobs** are attested batches holding every node B's load set needs.
- **The subject** is B, statements only.
- **The witness** is B's proofs. witness passes attest-mode witnesses today but leaves them
  empty; it would carry the proofs, which are checked once and never stored or loaded again.

The check resolves every import of every node in B to a node in B (earlier) or in a trusted
blob, by hash. Anything unresolved is false. It builds a nanoda environment from just those
nodes, checks each node of B (with its proof, for a theorem), and returns true.

Soundness by induction: a trusted node was in an attested batch, so it was checked given the
nodes it imports, which were themselves attested before; and since hashes cover imports, a
trusted node always means what it meant when it was checked.

**Reveal** works the same way. The bounty's params name the statement by *hash* (with the
theorem's name), so binding is "the theorem's type is `const` of that hash". The witness is the
solver's batch, with proofs; the trusted blobs are attested batches holding its load set. The
library the solver uses is attested once, by anyone, and reused by every later bounty.

## What witness needs (generic)

1. **Attestations form a DAG, and cover sets.** A claim names a set of parents and a subject list
   (a preimage listing a batch's statement nodes), any of which a check may receive as trusted
   alone. Ops cite a claim once and its entries by index, and `MAX_BLOBS` rises into the thousands. In attest and reveal mode the
   check receives the parents' subjects, and witness makes sure every trusted subject arrives
   with its own parents (the closure), so trust never skips a step. Linear chains are the case
   of one parent each; their closure is the chain.
2. **No positional context rule.** Today a subject is trusted only right after its own chain,
   because positional layers depend on their prefix. Content-addressed blobs don't, so witness
   can drop that rule. A check over a positional format can still enforce it itself: it sees each
   blob's hash, so a layer can name the hash of the layer it follows.
3. **Attest-mode witnesses.** Pass the attester's witness (here, the proofs) to the check. It
   isn't part of the claim's id: the attestation is about the subject, whatever the evidence.
4. **Bounties and reveals cite sets** of attested blobs, rather than one chain plus extras.

These are a revision of the chain model witness#7 merged. Nothing is deployed, so it's a clean
change of the types, rules and CLI.

## If a proof is needed

If a declaration somewhere needs another theorem's proof to type-check (none in infinite primes
does), the attester can include that theorem's proof node in the trusted set: proof nodes are
content-addressed too, keyed by the theorem's hash. The check loads it when present; checking
stays the same. Nothing about the format has to change.

## Plan

1. **Measure batching.** Done (above), for infinite primes and FLT for n = 4.
2. **The format.** A converter from NDJSON to nodes and batches, and a nanoda loader that builds
   an environment from nodes by hash.
3. **witness.** DAG attestations, attest-mode witnesses, sets of cited blobs.
4. **The check, v2.** Attest and reveal over content-addressed batches.
5. **End to end.** Infinite primes on the testnet, compared with today's 66-layer chain: total gas,
   gas of the heaviest step, and rounds. Then a bigger theorem.

## Batching: attest in batches, load single statements

Measured on the infinite-primes closure (`tools/lean/measure_batches.py`), with each batch's
trusted set being the batches that hold any statement its declarations need:

| Batches | Count | Rounds | Trusted batches per batch (median / max) | Trusted statements, NDJSON (median / max) |
|---|---|---|---|---|
| ~50 KB, export order | 293 | 208 | 28 / 89 | 1.1 MB / 3.2 MB |
| ~150 KB, export order | 113 | 101 | 24 / 61 | 2.3 MB / 4.8 MB |
| ~50 KB, by depth | 337 | 75 | 44 / 169 | 1.7 MB / 4.8 MB |
| ~400 KB, by depth | 94 | 75 | 29 / 69 | 5.3 MB / 7.2 MB |

Two things go wrong when the unit of loading is the batch:

- **A batch loads far more than it needs.** One declaration needs a median of 31 KB of statements
  and at most 1.1 MB; a batch pulls in every batch that holds any of them, 1 to 7 MB.
- **Export order chains the batches.** Consecutive batches depend on each other, so attesting
  takes as many rounds as there are batches. Batching by dependency depth gets the minimum, 75,
  at the cost of loading even more.

So the unit of attestation and the unit of loading should differ. **Attest in batches**, to keep
the number of refines and records down, but **publish each declaration's statement as its own
node blob**, which the batch's attestation vouches for. A later check then loads exactly the
statement nodes it needs. For witness that means an attestation can cover a *set* of subject
blobs (a batch's statement nodes), any of which a check may receive as trusted on its own, and a
check may receive many more blobs than `MAX_BLOBS` (128) allows today: up to about 700 here, so
blobs need a cheaper path than one lookup each, or a much higher limit.

Loading single statements, a batch loads the union of its declarations' load sets:

| Batches, by depth | Infinite primes: statements per batch (median / max) | FLT, n = 4 |
|---|---|---|
| ~50 KB | 188, 230 KB / 684, 1.1 MB | 242, 299 KB / 1,395, 2.4 MB |
| ~150 KB | 322, 419 KB / 697, 1.1 MB | 434, 579 KB / 1,526, 2.8 MB |
| ~400 KB | 438, 629 KB / 699, 1.1 MB | 683, 1.0 MB / 1,754, 3.3 MB |

(NDJSON bytes; about a seventh of that in the binary format.) Compare 1 to 7 MB per batch when
loading whole batches, for the smaller closure.

### Many blobs, cheaply

A check may draw on hundreds to about 1,700 statement blobs. In gas that's cheap: a `lookup` costs
600 gas plus 248 per KiB, so 1,700 lookups of 3 MB in all cost about 2×10⁶ gas, a tiny fraction
of a refine. What doesn't scale is the op: a claim per trusted blob is about 140 bytes, so 1,700
of them would be about 240 KB, far over a work item's payload. So:

- An attestation names its batch's statement nodes through **one subject list**: a preimage
  listing their hashes. The claim covers the list's hash.
- An op carries each attestation's claim once, plus, per statement used, which claim and which
  entry of its list (a few bytes). Refine looks up the list and the node, and checks the node's
  hash against the list.

For the worst FLT batch, that's around 200 claims and 1,526 entries: under 40 KB. witness's
`MAX_BLOBS` (128) has to rise into the thousands for this.

## Open questions

- **Batch shape.** Batching by depth minimizes rounds; batching by Mathlib module probably
  minimizes how many batches a check draws statements from. With statements loaded one by one,
  only the rounds matter, so batch by depth.
- **Holding many small preimages.** Each statement node is a preimage the service holds, with a
  storage deposit per item. Mathlib's hundreds of thousands of declarations would be as many
  items. If that's too costly, a batch's nodes can share one blob, with a check given byte ranges
  of it; the subject list then lists (offset, length, hash).
- **Names.** Lean environments need unique names. Two different nodes with the same name (two
  versions of a lemma) can't both be loaded into one check; the check rejects it. Different
  Mathlib versions can still share every node that didn't change, since unchanged declarations
  hash the same.
- **Storage.** Statement batches stay held while anything cites them. Mathlib's statements are
  about a third of its export.
