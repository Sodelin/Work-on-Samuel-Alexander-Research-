# NANUQ at every finite level: circularity and exact displayed-split support

Research checkpoint: 29 September 2026. Read [the proof](ALL-LEVEL-PROOF.md)
for the hypotheses and [the source-to-result ledger](SOURCE-RESULT-LEDGER.md)
for the precise externally posed questions answered.

For every finite binary semi-directed LSA, outer-labeled planar, galled
phylogenetic network on at least four taxa, the **original NANUQ distance is
circular decomposable and its positive split support is exactly the union of
splits displayed by the network**. The theorem allows arbitrarily many blobs
and arbitrarily high finite reticulation level.

The proof replaces a level-by-level core classification with a uniform
six-label reduction. Opening the pendant hybrids of a capped blob produces a
plane tree with adjacent paired tip occurrences. A circular coefficient uses
two anchors and at most four boundary taxa; retaining those occurrences
preserves the coefficient. An exhaustive finite certificate therefore controls
networks of unbounded size and level. An exact composition identity joins
the local distances into the full network distance.

A second theorem gives the exact universal **anchor-positivity** domain for
the displayed-quartet extension of the NANUQ+ four-score family:

```math
 s=o=1,\qquad \tfrac12\le a\le1,\qquad 0\le c\le a.
```

It implies circularity for all-level bloblets, including original and Modified
NANUQ. Necessity for the aggregated unweighted distance, general parameter
composition across blobs, and identifiability across the region are separate
questions. At the all-one score vector the distance loses all network information.

## Evidence and formalization boundary

The main result is a **computer-assisted mathematical proof with internal
agent audits**, not an externally reviewed or fully Lean-formalized theorem.

- [Structural reduction](ALL-LEVEL-STRUCTURAL-AUDIT.md): embedding, adjacency,
  switching support, restriction and original circular order.
- [Independent finite check](ALL-LEVEL-FINITE-AUDIT.md): 84,076 ordered
  tree/duplication instances; 11,848,859 physical-copy quartet checks;
  122 distinct systems and 24,667 anchor coefficients. These are representation
  instances, not 84,076 distinct phylogenetic-network isomorphism classes.
- [Composition](ALL-LEVEL-COMPOSITION-AUDIT.md): arbitrary level and multiple
  blobs, preserving the source's uniform **distinct-topology** definition.
- [Support computation](ALL-LEVEL-SUPPORT-FINITE-AUDIT.md) and
  [support transfer](ALL-LEVEL-SUPPORT-STRUCTURAL-AUDIT.md): no loss of displayed
  splits, no additional metric splits, including bridges and two-port chains.
- [Parameter audit](PARAMETER-DOMAIN-AUDIT.md): independent exact symbolic
  classification, with witnesses for all sixteen inequality types.
- [Independent selected-tree support verifier](SIDECHAT-SUPPORT-AUDIT.md):
  2,525,210 globally consistent occurrence selections, with no support mismatch.
- [Second lane](source-development/README.md): preserved level-two development,
  canonical-theta Lean proofs, raw-graph foundations, logs and dated checkpoints.
  Its older README and manifests are historical snapshots. See the newer
  [quality assessment](source-development/formal-full/ALL-LEVEL-QUALITY.md)
  and [remaining formal obligations](source-development/formal-full/OBLIGATIONS.md).

The second lane's Lean algebra proves equivalence of the recorded parameter
inequalities to the displayed domain. That does not itself formalize the
all-level graph representation or enumerate its source models in Lean.
The canonical-theta theorem has a different, narrower scope. No count of
files, lemmas, or tested cases is a count of discoveries.

## Sharpenings and the abstract extension

- [Five is the sharp parameter-test cutoff](FIVE-TAXON-THRESHOLD.md). The
  proof uses the six-label structural reduction and exact equality of the
  five- and six-label inequality catalogs. An explicit five-label example
  defeats four-only tests. This does not assert pointwise five-label compression.
- [Contiguous multicopy trees](CONTIGUOUS-MULTICOPY-EXTENSION.md). For a plane
  binary tree in which each taxon's occurrences form one contiguous block,
  retaining only the first and last copy preserves every distinct quartet
  set and the union of displayed splits. Block sizes may be arbitrarily large.
  Thus the distance/support and parameter results apply to this abstract
  class as well. Full displayed-tree families and copy-weighted probabilities
  need not be preserved.
- [Margins, residual pseudometric and scope boundary](ADDITIONAL-COROLLARIES.md).
  Positive original-NANUQ split weights are at least 1 in the original scale;
  integer rounding recovers the complete raw matrix from entrywise error
  strictly below 1/2, and the supplied correct order then gives exact support.
  A four-taxon ambiguity proves that radius is optimal uniformly over the
  source class; see the [fresh replay and sharpness proof](EXTREMALITY-REPLAY.md).
  A verified level-two counterexample shows why outer-labeled planarity
  cannot simply be omitted from exact support.
- [Beyond NANUQ](BEYOND-NANUQ-TARGETS.md). The natural neighboring framework is
  multi-labeled trees. The bounded source audit finds no additional externally
  posed conjecture already closed by these extensions. General ARGs and shared
  pruning choices require additional structure that the quartet summary loses.

The literature notes preserve their status at the time of their bounded pass;
the completed multicopy proof above supersedes their pending-proof wording.
For the formal lane's newest stable inventory and portable runner, use
[PUBLICATION-HANDOFF.md](source-development/formal-full/PUBLICATION-HANDOFF.md).
Its separate fresh 94-module rebuild was still in progress at capture; this
package does not represent that pending rebuild as a successful fresh run.

The [extremality register](source-development/extremality-sidechat/THEOREM-EXTREMALITY-REGISTER.md)
preserves 96 audit items, with stable IDs and proposed Lean contracts, from
the authorized side chat. This is a reference inventory: it is neither a
list of 96 externally stated open problems nor a claim of 96 discoveries,
and it does not authorize 96 new investigations. The fresh standalone Node
replay exactly matches its saved JSON; the integration audit independently
checks the new sharp-noise claim. Other status labels retain the side chat's
scope and do not constitute a fresh register-wide review.

## Reproduce or continue

The finite Python programs use the standard library. In a disposable copy of
this directory, run:

```text
python -B all_level_screen.py
python -B independent_all_level_check.py
python -B parameter_domain.py
python -B independent_support_check.py
node sidechat_support_check.cjs
python -B nonplanar_support_counterexample.py
```

The first two use different enumeration and quartet-evaluation methods. The
support checker reuses the independently saved systems. The JavaScript check
independently tracks actual selected-tree edges. These commands overwrite
their generated receipts where applicable; retain the committed receipts for
comparison. Never use Python's `-O` option: assertions are verification checks.

`PARAMETER-DOMAIN-AUDIT.md` includes the independent symbolic checker verbatim;
its historical local folder setting must be changed to this directory when
reproducing it elsewhere. Older exploratory scripts with machine-specific
paths are retained as history, not as the portable primary entry point.
`SOURCE-INVENTORY.json` pins every captured source and documentary file from
the two main lanes and the supplemental extremality handoff. Generated
compiled objects and dependency caches are excluded; documentary compiler
logs are included explicitly despite the repository-wide log ignore rule.

`python -B verify_publication.py` verifies the captured inventory. Add
`--recompute` to run the portable finite programs in a temporary copy and
check their key results without overwriting the committed receipts. Before
publishing from a Git checkout, add `--require-git-tracked` to verify that
every inventory item is in the Git index, including the compiler logs.
The supplemental side verifier can be replayed separately with
`node source-development/extremality-sidechat/verify_nanuq.js`.

For a fresh chat, begin with [CONTINUE-RESEARCH.md](../../CONTINUE-RESEARCH.md).
It names the live packet and the exact return format. For next mathematical
targets, read [the bounded extension map](EXPLICIT-EXTENSION-TARGETS.md).
Those literature targets are not claimed solved by analogy.

## Publication status

The GitHub checkpoint and the VibeMathed submission are separate events.
The entry **All-level NANUQ circularity and exact displayed-split support**
was submitted and its exact title read back in the review queue on
30 September 2026 UTC (29 September locally). The submitted proof is
commit `cba23504ec7c63936ab60e5c3beb65d296c2e9c5`; both hosted checks
passed there. See [the delivery receipt](DELIVERY-RECEIPT.json),
[submitted public fields](SUBMISSION-PAYLOAD.json) and
[current delivery state](SUBMISSION-STATUS.json). Curator acceptance is pending.
No curator acceptance, external expert endorsement, historical priority, or
author email is inferred from publishing these files.
