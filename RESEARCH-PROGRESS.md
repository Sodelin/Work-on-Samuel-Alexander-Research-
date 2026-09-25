# Research progress — 25 September 2026

**Snapshot: 16:21 UTC / 09:21 Pacific.** Start with the readable results below; each links to its exact code and evidence. This is a navigation snapshot. The owning source ledgers retain the full mathematical scope.

## What changed today

- **The default GitHub page now shows current work.** The README links here and to [draft PR #6](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/pull/6). Earlier progress was on the research branch while the front page remained stale.
- **The finite-model comparison is published and passed GitHub verification:** [read the result](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/4fd6f7cc89fda47f245e9ae28fca140fd04de783/research/feedback-speciation/finite-epigenetic/README.md), [successful run](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/actions/runs/36156872958).
- **The Wong deterministic integration is published:** [current result and coverage](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/c169e5f19a4233182f29d54c3e2e0e3d65abe897/research/wong/completion/CURRENT.md). Its combined local Lean audit and [full hosted run](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/actions/runs/36158710859) passed. The earlier failure in two archived README math delimiters was fixed in [46aac52e](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/commit/46aac52e214311fb2c2230b1b4fe37c42ef9e1a9); the proof bytes were unchanged.
- **Two further bounded proofs passed locally:** the 19-declaration embedded count-process package and a four-declaration finite parent-choice connection. They remain outside the new public integration pending their separate reviews.
- **The requested team is configured:** one Astra auditor, three Astra Max leads, two shared Sol workers and one shared Luna assistant. [Roles and publication rules](RESEARCH-ARCHITECTURE.md) state the work limits and review process.

## 1. Simplifying ancestry while retaining the relationships we care about

An ancestral recombination graph records which genome regions came through which ancestors. A useful simplification removes unnecessary detail while preserving specified ancestry questions.

The new deterministic work separates removing ancestry above a local most recent common ancestor, contracting supported paths through nonsample unary nodes, and combining interval annotations into a canonical representation. This gives explicit preservation guarantees and reveals the assumptions each operation needs.

**Published contribution:** 24 MRCA, 31 interval and 10 normal-form declarations, integrated into a fresh audit of **274 selected real-library declarations across 61 imported local modules**. All selected declarations report only the standard axioms allowed by the repository. The combined local check exited successfully, followed by a successful hosted check of all repository gates at commit 46aac52e. [Exact receipt](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/c169e5f19a4233182f29d54c3e2e0e3d65abe897/verification/real-audit.json) · [source correspondence](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/c169e5f19a4233182f29d54c3e2e0e3d65abe897/research/wong/completion/verification/deterministic65/SOURCE-CORRESPONDENCE.md) · [independent review](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/c169e5f19a4233182f29d54c3e2e0e3d65abe897/research/wong/completion/verification/deterministic65/SOL2-REVIEW.md).

**Limits:** the guarantees require the stated sample support and ancestry hypotheses. Idempotence of canonical interval storage does not establish idempotence of the whole simplification pipeline. Whole-paper formalization, continuous-time and spatial process connections, Little ARG results and the remaining exporter obligations are still open in the [coverage ledger](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/c169e5f19a4233182f29d54c3e2e0e3d65abe897/research/wong/completion/COVERAGE.md).

### A new local step: absorption of the count process

The separate probability package now constructs an actual path law for the stopped embedded count chain and proves that it reaches one lineage after finitely many jumps with probability one, under the specified split and merger rates. The final theorem derives the required drift from its explicit potential.

**Status:** 19 selected declarations passed local Lean checks: two scalar, ten count-chain and seven absorption declarations. Independent statement review passed with explicit scope limits; the lead is finishing source correspondence and the publication packet. Finite jump count, continuous physical time and projection from a spatial ARG are separate proof obligations. This package is not included in the public 274-declaration audit above.

## 2. A comparison can change when the model changes

The finite feedback packet compares genetic and epigenetic regimes in two specified population models. In the finite model, the genetic reproductive-isolation score is approximately **0.420005**, below the epigenetic value **3/7**, approximately **0.428571**. In the deterministic comparison, the genetic score is above **3/7** from the stated fourth generation onward.

The practical lesson is precise: transferring a ranking from a deterministic population model to a small finite population can reverse the answer. The model assumptions and initialization are part of the result.

**Status:** all **34 selected declarations** are published, and their integration passed a fresh GitHub run. The standalone research audit now checks **163 declarations in 23 files**. [Worked result and replay instructions](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/4fd6f7cc89fda47f245e9ae28fca140fd04de783/research/feedback-speciation/finite-epigenetic/README.md) · [publication manifest](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/4fd6f7cc89fda47f245e9ae28fca140fd04de783/research/feedback-speciation/finite-epigenetic/PUBLICATION-MANIFEST.json) · [successful hosted check](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/actions/runs/36156872958).

**Limits:** this is a comparison inside the stated models. It establishes neither universal DNA-based species identification nor an automatic transfer to Alexander's infinite ancestry definitions. The formal limiting statement retains its convergence premise; the finite-generation reversal does not require that premise.

### Making the Alexander connection real

The next question is whether the parent choices generating those allele counts also satisfy Alexander's ancestry hypotheses. The auditor challenged a proposed probability argument: a one-offspring probability alone does not determine the probability of the complete parent-and-allele event. The owner supplied the complete joint construction.

A first **four-declaration local Lean checkpoint** now checks normalization of the finite weighted records, a designated parent-table probability, one ordinary transition and the separate initialization pulse against the existing count model.

**Remaining:** the full raw-noise-to-record correspondence, all transition marginals and the infinite-time ancestry conclusion. Finite-prefix examples, possible infinite paths and probability-one assertions are kept distinct.

## 3. Information lost through simplification

The already published Q04 exact-abstraction result specifies when the retained observation is sufficient to predict the next observed state. Q09 supplies a merge-history obstruction: two states with the same current membership can need different future answers when the operation depends on past parentage.

This gives the user's “abstraction fee” a concrete mathematical question: which distinctions did the observation erase, and do those distinctions matter for the prediction or decision we want to preserve?

**Next bounded connection:** one preservation statement applied to two explicitly defined models, with a counterexample and the assumptions needed for a biological interpretation. The replacement Astra Max lead has acknowledged the assignment. The earlier task is preserved after returning empty continuations.

[Proof structure and examples](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/138dd529643ae5706a9df6a750bd6344ab967a8a/research/open-problems/time-self-reference/PROOF-STRUCTURE.md) · [source-question ledger](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/138dd529643ae5706a9df6a750bd6344ab967a8a/research/open-problems/time-self-reference/problem-ledger.json).

**None of the twelve broad source questions is declared completely solved.** These are restricted, reusable mathematical results and proposed interpretations.

## Verification and next deliverables

| Work | Evidence now | Next concrete finish |
|---|---|---|
| Latest fully successful hosted research commit | 46aac52e: 405 core, 274 real, 163 standalone selected declarations | Preserve exact receipts as later packets are integrated |
| Wong deterministic additions | 65 added declarations; combined local and hosted checks passed; source packet public | Continue with the remaining paper obligations |
| Wong count-process absorption | 19-declaration local package and independent statement review passed | Finish source correspondence and integrate the scoped result |
| Finite feedback ranking | 34 added declarations; included in successful hosted run | Preserve the immutable release |
| Alexander parent-choice connection | Four selected finite statements passed locally | Prove the remaining law correspondence before the infinite-time transfer |
| Same-prefix/noisy finite observations | Completed 23-declaration local packet and interpretation review | Publish its exact scope and dependencies |
| Q10 order-convex Nash obstruction | Written construction, finite checks and Sol review | Astra adjudication of the bounded claim, then publication |
| General connections | New owner acknowledged one bridge and two-model scope | Deliver the statement-only brief |

Counts describe selected audited declarations, not independent discoveries. Formal verification, novelty, usefulness and empirical applicability have separate evidence requirements.

The auditor is the only public integrator. Workers receive one bounded assignment at a time, there is one local compiler owner, and side ideas receive their own brief. Completed tasks remain visible and unarchived.

GitHub publication, author email and VibeMathed submission are separate events. This snapshot records GitHub progress; it does not record a new email or site submission.
