# What belongs in each research deliverable

This is the scope and delivery map for the coordinated research pass. Its purpose
is to keep the original connections visible while distinguishing attributed
results, new quantitative answers, project extensions and exploratory ideas.
The intended cross-paper connection is **Wong et al. (2024) genome ARGs to Alexander's organism/population and specieslike framework**. Its exact current boundary is recorded in the [Wong bridge audit](notes/WONG-ALEXANDER-BRIDGE-STATUS.md).
The ten entries in [TEN-SOLUTIONS](TEN-SOLUTIONS.md) answer our ten extension
proposals. They are not ten previously open problems posed by Alexander.

## The bridges, stated precisely

| Connection | What is formally established | Boundary |
|---|---|---|
| **Wong 2024 genome ARGs to Alexander ancestry** | A finite interval-annotated DAG model, local ancestry/parent representation, sample-restriction laws and exact recovery conditions, and contrasting infinite completions of any finite ordered history have passed individual Lean checks. The owner-to-pedigree path projection has explicit compatibility premises. | These prove a representation framework and a finite-data limitation. They do not infer biological owners, identify an actual future population, establish diploid role-label coverage, certify a full simplification algorithm, or prove that every projected population is specieslike. The original Wong packet passed hosted verification at bcef6da64672310b314f2bc17c96f9535fcaaf5b; subsequent modules have their own source receipts and publication gate. |
| The separate avoiding construction to Alexander's specieslike/inspecies definitions | The actual unlabelled $`P_s`$ with natural birthdates satisfies the biosphere and specieslike conditions; its whole graph is an inspecies. Binary unavoidability within the specieslike class is still exactly eventual periodicity. | This is a mathematical connection between the stated graph models. The construction belongs to the separate September manuscript; Alexander supplied the framework and positive theorem. |
| Whole populations to their specieslike subsets | The source graph's two maximal IAP/CONV/CA/REF cones are classified. Lost parent labels are checked, and a fixed infinite subset has an eligible deletion-only repair exactly when its deficient vertices are finite. Productive pruning has exact language-preservation and cluster results. | Whole-graph common ancestry fails in the eligible binary model. A specieslike subset does not automatically inherit all population axioms. These theorems do not solve general maximal-cluster existence. |
| Thue-Morse scale structure to quantitative graph behavior | Dyadic bit identities feed actual boundary/path recursions, a sharp $`8/3`$ bound, exact maxima at every start and a certified integer digit evaluator. | This is a proved recursive description of labels and matching lengths. It is not a theorem that all of Alexander's graphs are self-similar or that a dilation is a graph isomorphism. |
| Exact observation and deterministic prediction | Recovery by an observation is equivalent to constancy on its fibres; deterministic prediction has an exact compatibility condition. | These abstract facts support concrete information-loss arguments. No genomic estimator, coalescent process, or biological/psychological dynamics has been instantiated. |

The Wong connection is documented first in [WONG-ALEXANDER-BRIDGE-STATUS](notes/WONG-ALEXANDER-BRIDGE-STATUS.md), with exact published pages and Lean coverage. The separate avoidance-to-species connection is documented in [SPECIESLIKE-BRIDGE](notes/SPECIESLIKE-BRIDGE.md).
Its principal endpoints include `SpeciesBridge.psWhole_bridge`,
`SpeciesGlobalIAP.psWhole_inspecies`, and
`PositiveUnavoidability.specieslike_classification`. The subset boundary is
handled by `SpeciesCones`, `ProductiveCore`, and `BoundaryRepair`.
The [ancestry/observation interface](notes/ANCESTRY-OBSERVATION-INTERFACE.md)
and [exploratory complex-systems appendix](explorations/COMPLEX-SYSTEMS-INTERFACE.md)
make the broader connection's remaining assumptions explicit.

The source is now identified as Wong 2024. Neither its persistence of node
identities across local trees nor its simplification procedures establish
literal graph self-similarity. The existing Thue-Morse scale identities concern
one specific word and matching-height function. A self-similarity claim needs
its own explicit map and invariant; specieslike status has different axioms.
The new Wong audit supersedes the older scope note's unresolved-source wording.

## Four destinations

| Destination | Include | Lead with | Keep out of the central claim |
|---|---|---|---|
| **Verified Lean release** | The complete checked dependency chain, source/model adapters, new results, counterexamples, pinned versions, axiom receipts, reproduction commands and exact-commit CI. | Actual graph statements and their hypotheses, with source attribution. Include the Wong adapter and its explicit coverage limits, alongside the separate specieslike and quantitative results. | Uncompiled exploratory proofs; empirical or conceptual implications for which no concrete model was supplied. A passing build alone does not establish originality or statement fidelity. |
| **Email to Alexander** | A short readable introduction, explicit AI-role disclosure, one stable public link, two or three examples, and a request for mathematical feedback or prior references. | **The Wong genome-history / organism-ancestry connection, what sample restriction retains, and the proved finite-history/infinite-future limitation**; then the sharp Thue-Morse result as a distinct quantitative contribution. | A ten-result dump, claims to solve all his open questions, invented authorship, claims that his graphs generally are self-similar, or speculative psychology conclusions. The coordinating task owns the draft and outreach. |
| **VibeMathed submission candidate** | One sharply stated source-linked problem, its proved answer, the question's earlier public location, the exact proof endpoint and commit, AI contribution, verification evidence and priority caveats. | **Sharp quantitative Thue-Morse matching heights**, strengthened by the all-start formula and certified evaluator. This answers the separate September manuscript's explicit request for useful bounds. | Bundling every project extension as a separate historic breakthrough, presenting a re-formalized source result as a newly solved problem, or declaring catalog acceptance/independent expert endorsement. |
| **Public research notebook** | All reviewable work: proofs, explanations, source comparisons, experiments, failed approaches, scoped conjectures, tooling and the conceptual appendix. | A navigable README, this delivery map, the solution ledger and the current verification status. | Mixing experiments with proof receipts or mixing exploratory analogies with established consequences. Historical files retain their stage but link to the current status. |

“Publishing Lean” here means releasing a reproducible formal proof repository;
it does not mean that a Mathlib contribution, journal submission or registry
listing has already occurred. Those would be separate deliveries.

## The focused submission claim

In the particular Thue-Morse avoiding population from the separate classification
manuscript, let $`L(v)`$ count the greatest number of matching **edges** from start
$`v`$. We prove

```math
3L(v)\le 8v-1\quad(v\ge1),
```

with equality exactly at $`v=3\cdot2^n-1`$, where $`L(v)=8\cdot2^n-3`$.
We also prove the full formula and an executable digit evaluator returning an
attained maximum at every natural start. The prior question is in the
[pinned September manuscript, Section 5](https://github.com/avg-netizen/biological-unavoidability/blob/3d6175e3e23f67bd68e7be591b5a9a6d04e496a3/paper.md#5-universality-and-computability-in-the-witness-family).
It is not an identified Alexander-authored quantitative question.

[VibeMathed's methodology](https://vibemathed.com/methodology) requires a proved
answer to a stated open question with substantive AI involvement and excludes
merely formalizing an already established result. Its
[submission form](https://vibemathed.com/submit) requests a checkable source,
verification/publication status and scope. The catalog's acceptance and status
remain its curators' decisions. Audits by other agents on this project are
internal statement review, not independent human expert endorsement.

## What remains open beyond this release

We do not claim solutions to Alexander's general universal-avoider embedding
question, general ordinal characterization, or general maximal-specieslike
existence without his common-ancestor condition. Nor does a graph-theoretic
species witness establish a biological or psychological theory.

For the immediate Wong bridge, integrate the source-model and sample-restriction
proofs, compose the finite topology adapter with the contrasting completions,
then justify a concrete pedigree instance and its population/cluster hypotheses.
For a further bridge to a concrete dynamics model, the next useful work is to
name the actual state space, transition rule, ancestry/history map and observable,
then prove that this instance satisfies the already explicit preservation and
factorization conditions. That work should have its own problem statement and
evidence, rather than being inferred from the present genealogy theorems.

## Current delivery state

The exact current core and Mathlib endpoint totals and source hashes are in
[the core receipt](verification/formal-audit.json) and [the Mathlib receipt](verification/real-audit.json).
The new Wong proof packet covers finite interval graphs, ordered event conversion,
sample restriction, retained-node contraction, local arity/traversal, a concrete
finite reconstruction counterexample and actual gARG-to-infinite completion ambiguity.
The full formula and certified finite recurrence remain proved independently of
the optional binary-kernel wrapper. Hosted CI must be checked against its actual commit.

The first reviewed email was sent by the coordinating task on 25 September 2026,
covering the earlier immutable verified snapshot. These subsequent Wong results
are a separately verified follow-up; no second email is implied by this note.

The existing coordinating task owns the single public branch/PR, the email
draft, and the VibeMathed submission workflow. This task owns mathematical
integration and this scope map, so those actions are not duplicated.

## Subsequent checked package

The next proof package contains the exact individual finite-edit optimum, automatic finite interval output for the specified Wong simplification, the supported-diamond cutoff collision, and the explicit compatible-completion decoder obstruction. It belongs in the Lean/GitHub archive with exact source receipts. The earlier email and VibeMathed submission refer to their own earlier proof snapshots; this follow-up is not a second email or duplicate submission. The coordinator reports the Thue–Morse entry submitted under review; it does not certify these later results.
