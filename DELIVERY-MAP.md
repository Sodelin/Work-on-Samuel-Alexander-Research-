# What belongs in each research deliverable

This is the scope and delivery map for the coordinated research pass. Its purpose
is to keep the original connections visible while distinguishing attributed
results, new quantitative answers, project extensions and exploratory ideas.
The ten entries in [TEN-SOLUTIONS](TEN-SOLUTIONS.md) answer our ten extension
proposals. They are not ten previously open problems posed by Alexander.

## The bridges, stated precisely

| Connection | What is formally established | Boundary |
|---|---|---|
| The separate avoiding construction to Alexander's specieslike/inspecies definitions | The actual unlabelled $`P_s`$ with natural birthdates satisfies the biosphere and specieslike conditions; its whole graph is an inspecies. Binary unavoidability within the specieslike class is still exactly eventual periodicity. | This is a mathematical connection between the stated graph models. The construction belongs to the separate September manuscript; Alexander supplied the framework and positive theorem. |
| Whole populations to their specieslike subsets | The source graph's two maximal IAP/CONV/CA/REF cones are classified. Lost parent labels are checked, and a fixed infinite subset has an eligible deletion-only repair exactly when its deficient vertices are finite. Productive pruning has exact language-preservation and cluster results. | Whole-graph common ancestry fails in the eligible binary model. A specieslike subset does not automatically inherit all population axioms. These theorems do not solve general maximal-cluster existence. |
| Thue-Morse scale structure to quantitative graph behavior | Dyadic bit identities feed actual boundary/path recursions, a sharp $`8/3`$ bound, exact maxima at every start and a certified integer digit evaluator. | This is a proved recursive description of labels and matching lengths. It is not a theorem that all of Alexander's graphs are self-similar or that a dilation is a graph isomorphism. |
| Wong et al. (2024) genome ARGs to organism ancestry | Conditional owner-map path projection, fixed-locus path preservation under erasure, and explicit failure-of-recovery examples are checked. `SpeciesAdapter` connects the path relation to the existing ancestor relation. | This does not yet instantiate Wong's full gARG structure or derive its edge compatibility with Alexander's population axioms. A faithful embedding and species-cluster preservation remain unproved. |

The first connection is documented in [SPECIESLIKE-BRIDGE](notes/SPECIESLIKE-BRIDGE.md).
Its principal endpoints include `SpeciesBridge.psWhole_bridge`,
`SpeciesGlobalIAP.psWhole_inspecies`, and
`PositiveUnavoidability.specieslike_classification`. The subset boundary is
handled by `SpeciesCones`, `ProductiveCore`, and `BoundaryRepair`.
The [ancestry/observation interface](notes/ANCESTRY-OBSERVATION-INTERFACE.md)
and [exploratory complex-systems appendix](explorations/COMPLEX-SYSTEMS-INTERFACE.md)
make the broader connection's remaining assumptions explicit.

The intended biological bridge is **Yan Wong et al. (2024), A general and efficient representation of ancestral recombination graphs**, [Genetics, iyae100](https://doi.org/10.1093/genetics/iyae100). Its Genome ARGs section and Figure 1 already describe genome ancestry embedded in a pedigree. Our current conditional projection formalizes one preservation principle. It does not certify the complete cross-paper model or a graph self-similarity theorem. The remaining work is to instantiate the full gARG invariants, the owner map, and the required population/species hypotheses.

## Four destinations

| Destination | Include | Lead with | Keep out of the central claim |
|---|---|---|---|
| **Verified Lean release** | The complete checked dependency chain, source/model adapters, new results, counterexamples, pinned versions, axiom receipts, reproduction commands and exact-commit CI. | Actual graph statements and their hypotheses, with source attribution. Include the specieslike bridge, not just numerical formulas. | Uncompiled exploratory proofs; empirical or conceptual implications for which no concrete model was supplied. A passing build alone does not establish originality or statement fidelity. |
| **Email to Alexander** | A short readable introduction, explicit AI-role disclosure, one stable public link, two or three examples, and a request for mathematical feedback or prior references. | The user's interest in the Wong-to-Alexander ancestry connection, explicitly labeled conditional; then the checked quantitative Thue-Morse result and optionally the cap-two construction. | A ten-result dump, claims to solve all his open questions, invented authorship, claims that his graphs generally are self-similar, or speculative psychology conclusions. The coordinating task owns the draft and outreach. |
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

For the Wong bridge, the next useful work is a concrete gARG model with interval coverage, parent and ancestry constraints, a specified organism-owner map, and proved preservation hypotheses. Species conclusions require additional population and cluster assumptions. This remains a separate objective from the ten checked extension proposals.

## Current delivery state

The local core audit passes 370 selected endpoints; the optional Mathlib audit
passes 30 selected endpoints including actual port encoding and the real CA
comparison. The literal binary-kernel finite-generation wrapper is an optional
additional check in progress; the full formula and certified finite recurrence
are already proved without it. Hosted CI and publication status must be read
against their actual commit, not inferred from these local checks.

The existing coordinating task owns the single public branch/PR, the email
draft, and the VibeMathed submission workflow. This task owns mathematical
integration and this scope map, so those actions are not duplicated.
