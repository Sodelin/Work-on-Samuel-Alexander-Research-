# Source-to-result audit, 27 September 2026

Start with the public [one-page reading route](../../../../TIME-AND-MEMORY.md).
This audit continues the canonical [problem ledger](../problem-ledger.json),
the [prior proof structure](../PROOF-STRUCTURE.md), and the
[controlled-abstraction bridge](../controlled-abstraction-bridge/BRIDGE.md).
It does not create a competing inventory or change any full source question
to solved. Final check status is recorded in the source-hashed
[proof receipt](verification/PROOF-RECEIPT.json).

## Primary source and scope

The primary source is Abramsky, Banzhaf, Caves, Levin, Machado, Ofria, Stepney
and White, *Open questions about time and self-reference in living systems*,
Royal Society Open Science 13, 261059,
[DOI 10.1098/rsos.261059](https://doi.org/10.1098/rsos.261059).
We read the published 29-page PDF with SHA256
`8b3940d8ac53c7145584c38c1a95a27c87f9c8173323112865c5439862bf43ce`.
PDF page numbers below agree with the printed body pages. The
[institutional bibliographic record](https://www-users.york.ac.uk/~ss44/bib/ss/nonstd/roysoc26.htm)
and [preprint](https://arxiv.org/abs/2508.11423) are secondary access routes;
we do not assume that a preprint version is identical to the publication.

**Q01–Q12 are our working decomposition.** They combine explicit questions,
gaps, and themes in the paper. The source does not present twelve theorem
statements with the hypotheses we selected. The paper's projection discussion
is broader than exact prediction; its biological time and autonomy questions
are broader than deterministic state machines. No full author question is
claimed solved, and no novelty is claimed for the standard mathematics.

## What was already established

| Artifact at the starting checkpoint | Evidence | Remaining boundary |
|---|---|---|
| Exact deterministic abstraction | Two directions of the fibre-compatibility criterion, uniqueness, all-time preservation, and a two-bit collision/oscillation example in Lean. | A fixed transition semantics and chosen observation; not a universal impossibility of projection or a necessity of physical time. |
| Predecessor-restoring merge/split | Lean collision for legal histories with identical current partitions and different restored partitions; bounded pinned implementation check. | No complete game with changing decision makers, policies, payoffs, and solution concept. |
| Cell/history bridge | Written parity map; finite checks of 32 cell actions, 120 history actions, 20,460 trajectory cases, 95,580 prefix comparisons and 225 partitions. | Arbitrary histories and the generic probe-refinement decoder were not yet mechanized. |
| Impossible-versus-rare testing | Written sharp bound, 15 exact rational cases and 834 deterministic decision rules checked. | The general probability theorem remains unformalized; biological sampling assumptions remain unjustified. |
| Alexander/Wong bridges | Existing graph restriction, fixed-locus extraction, and opposite-completion theorems. | These prove specific graph mappings; they do not automatically transfer a living-system or stochastic-generator claim. |

The old two-module receipt has 16 selected endpoints. The new replay rebuilds
those source files and the project dependencies used by the new wrappers;
it does not infer current verification from an older green badge.
The old controlled finite checker and rare-event checker were also rerun.
Their finite outputs agree with the recorded claims. Enumeration does not
upgrade a written arbitrary-size theorem to a Lean proof.

## What this continuation adds

The [results note](RESULTS.md) gives exact contracts and declaration names.
The main improvement over a toy example is a result for **arbitrary types and
arbitrary finite intervention words**: future-output equivalence defines the
coarsest exact output-preserving controlled state, characterized by a unique
factorization from every onto exact representation. It includes finite
separating words, cardinal lower bounds, action restriction, and a conditional
feedback trajectory theorem.

The old bridge is now an application of those contracts: arbitrary finite
records commute with the parity summary; every exact model retains four
predictive classes; both memory values are necessary at each fixed visible
value; all four classes are attainable from one initialization. Equal-length
histories admit a common distinguishing probe. No fixed suffix window
determines parity on arbitrary records. Changing the probe can invalidate a
formerly adequate representation.

A second general result gives a **global** adequacy certificate: if the
depth-`k` equivalence relation on all declared state pairs is already stable
at `k+1`, it equals full finite-future equivalence. A delayed-revelation
counterexample prevents interpreting finite sampled agreement as that
certificate. A finite partition checker and exact rational examples provide
separate executable illustrations, not biological data or a verified search
algorithm.

The [biology note](BIOLOGY.md) distinguishes mechanism, prediction and example.
Two stable-type counterexamples make the empirical limitation concrete:
history can reveal a fixed cell type; conditioning on a treatment-affected
visible state can introduce an apparent history effect even after randomized
assignment. A theorem proves a specified deterministic same-unit, same-clock
null. The stochastic/causal assumptions needed for a statistical test are
written explicitly, not silently inferred from that theorem.

## Coverage of the working question ledger

Every row below retains `author_question_status: open`.

| Working target and published locator | Contribution and current evidence | Gate remaining between it and the source |
|---|---|---|
| Q01: life and time, §2.2 p.5 | The suffix/parity example separates recorded history from sufficient predictive memory. | Define physical time versus temporal representation; establish an operational biological claim. No emergence-of-time theorem. |
| Q02: non-iterative exploration, §3.3 pp.8–9 | No new theorem. | Choose computation, preparation, probability-of-success and resource models before a speedup or impossibility claim. |
| Q03: self-reference and time, §4.2 pp.10–11 | Earlier oscillation remains a model example; the new quotient adds no necessity-of-time result. | Define the self-reference and temporal predicates; a formal implication or countermodel must target those definitions. |
| Q04: process/result projection, §4.2 p.11 | Exact criterion extended to coarsest predictive state, minimal distinctions, feedback under an explicit policy factorization, and arbitrary-history bridge. | Justify the chosen deterministic prediction interpretation; extend to justified stochastic/biological semantics. |
| Q05: rule-changing open systems, §6 pp.15–16 | Rules or controller memory can be included in a joint state when their interpreter is fixed. | Specify an intended rule-changing system and prove its interpretation map. This observation is not unrestricted semantic change. |
| Q06: changing modeling language, §6.2.3 p.20 and §7 p.24 | No new formal language transformation. | Syntax, interpretations, transformations and retained invariants; a fixed interpreter cannot certify a changing one. |
| Q07: detecting inadequacy, §6.3 p.21 | Stable finite-depth equivalence certifies all-horizon adequacy on the declared system; delayed revelation and a changed probe show limits. | Unknown dynamics, unobserved states, stochastic error and expanding action languages require additional contracts and evidence. |
| Q08: plausible biological mechanism, §6.4.1 p.21 | Operational retention/probe questions, primary-source comparisons, and confounding/selection counterexamples. | An actual biological state, measurement and intervention map, followed by discriminating empirical evidence. No metabolism–repair realization proved. |
| Q09: changing decision makers, §6.4.3 p.22 | The old partition-only obstruction remains checked. The new generic refinement can describe sufficient state after a future operation family is fixed. | Prove a bridge for a complete merge/split game including membership, memory, controllers, payoffs and legality. |
| Q10: game solution notions, §6.4.4 pp.22–23 | No new equilibrium or domain-theoretic result. | Read the cited construction and identify a precise failed/preserved condition before altering its solution concept. |
| Q11: representation and autonomy, §7 pp.23–24 | Predictive state is relative to declared observations and interventions; this clarifies one representational task. | A discriminating operational implication of the philosophical alternatives, plus evidence. |
| Q12: sparse histories and calibration, §7 p.24 | Existing sharp rare-event bound retained as written; new delayed-revelation and exact-completion examples clarify different information limits. | General probability proof, dependent/path-dependent observations, unknown event rate, error model and source-adequate evolutionary calibration. |

## Which cross-project statements are genuine transfers?

| Connection | Preservation established | Classification and limit |
|---|---|---|
| General controlled theorem → ancestral restriction | Compress to `S`; apply any sequence of destructive restrictions to subsets of `S`; same final relation in both pipelines. | Actual theorem invocation in `AncestryObservation`. It does not restore information removed by an earlier action. |
| Ancestral restriction → actual finite interval gARG | Existing `extracted_edge_iff_restrict` identifies fixed-locus extraction with compression; the controlled theorem applies through that equality. | Proved mapping in `WongPredictiveBridge`; not interval-record dynamics or a stochastic generator law. |
| Finite gARG → Alexander-style infinite graph completions | Exact old edges and old ancestry paths preserved; admissible completions disagree on global IAP. | Existing completion bridge plus new no-decoder consequence for a fixed finite input. No genome-owner or biological species interpretation. |
| Wong timed-history contraction → memory theme | Equal retained observations can hide different histories. | Shared argument/analogy here; no new commuting map of timed updates or probability kernels. |
| Merge/split players → cells/tissues | No population/game/organism identification established. | Biological analogy pending membership, action, payoff, memory and empirical maps. |

## Remaining work in executable order

1. Extend the exact-map contract to finite stochastic transition kernels and
   output laws: a specified pushforward kernel must commute for every
   intervention, with an initial-law and observation contract. Prove law
   preservation and distinguish it from weaker trace equivalence. Then select
   one biological observation process that could meet those assumptions.
2. Formalize the existing rare-event testing theorem, including the finite
   product law, randomized decisions, the shared all-zero contribution and
   both attaining rules. This closes a precise certification gap, not the
   source's full calibration question.
3. For changing agents, specify the source game's full state and admissible
   histories, legal controls, memory transfer and payoff semantics. Only then
   ask whether the predictive quotient preserves its relevant solution notion.
4. For biology, specify and collect/read data that distinguish stable type,
   within-unit change, clock/context dependence and selection. A candidate
   storage variable must be measured and causally perturbed under explicit
   controls; a predictive fit alone cannot identify the mechanism.
5. For Wong dynamics, first supply the separate lane's marked-process and
   observation maps. Require kernel/path-law preservation before importing
   the Royal Society interpretation. Do not promote the fixed-locus graph
   pipeline to that stronger statement.

The independent [scope review](INDEPENDENT-SCOPE-REVIEW.md) checks source
correspondence and statement strength. It is separate from compiler evidence.
The [checkpoint](CHECKPOINT.md) records the exact final artifacts, validation
and integration state. Completion of this package leaves the broader research
objective open and the Codex chat visible and unarchived.
