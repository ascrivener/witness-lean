# Design: content-addressed Lean, attested as a DAG

Status: proposal. Measurements below are on the infinite-primes closure; nothing is built yet.

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

1. **Attestations form a DAG.** A claim names a set of parents. In attest and reveal mode the
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

1. **Measure batching.** Cut the closure into batches (by module, then by size), compute each
   batch's trusted set and its native check time with `tools/lean-host`, and the number of
   rounds. Then do the same for one larger Mathlib target, to check the estimates.
2. **The format.** A converter from NDJSON to nodes and batches, and a nanoda loader that builds
   an environment from nodes by hash.
3. **witness.** DAG attestations, attest-mode witnesses, sets of cited blobs.
4. **The check, v2.** Attest and reveal over content-addressed batches.
5. **End to end.** Infinite primes on the testnet, compared with today's 66-layer chain: total gas,
   gas of the heaviest step, and rounds. Then a bigger theorem.

## Open questions

- **Batching.** A batch's trusted set is every attested batch holding a node its load set needs.
  Batches that follow Mathlib's modules should keep that set small, since a module mostly uses its
  own imports. Step 1 measures it.
- **Names.** Lean environments need unique names. Two different nodes with the same name (two
  versions of a lemma) can't both be loaded into one check; the check rejects it. Different
  Mathlib versions can still share every node that didn't change, since unchanged declarations
  hash the same.
- **Storage.** Statement batches stay held while anything cites them. Mathlib's statements are
  about a third of its export.
