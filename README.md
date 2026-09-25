# Working on Samuel Alexander's research

## Wong completion and feedback follow-up — 25 September 2026

The [Wong completion ledger](research/wong/completion/README.md) now maps 52
claim families and records six new integrated modules (58 selected endpoints;
209 in the real aggregate). The [feedback/speciation package](research/feedback-speciation/README.md)
adds a conditional IAP classification, cultural/genetic boundary examples and
a quantitative fixation bound for the published Fogarty affinity model.
Its five new modules contribute 53 selected standalone endpoints; the repository
CI now checks 113 standalone endpoints in 17 files.

The Wong paper remains partly formalized. The feedback theorem has strong
pedigree assumptions, its probability adapter is still written-only, and none
of these additions proves that DNA determines biological species or establishes
novelty. See the exact scopes and [publication verification boundary](research/feedback-speciation/PUBLIC-INTEGRATION.md).
Hosted status is recorded per commit in [PR #6](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/pull/6/checks).

The previous consolidated author email and VibeMathed curator update were both
delivered on 25 September. The original VibeMathed submission remains under
review. This new research batch has not yet been sent as another outreach update.

**Start here:** [Completion map](COMPLETION-MAP.md) — finished statements, active proof gates, and what the evidence supports.

**Latest focused follow-up:** [What DNA can identify, known results, and a checked finite-evidence step](research/open-questions/genomic-identifiability/next/README.md).


A public, AI-assisted mathematics notebook connecting infinite genealogical
graphs, word avoidance, specieslike clusters and cellular automata. Source
results, new deductions, conjectures and finite experiments are identified
separately. The first reviewed outreach was sent on 25 September 2026; later mathematical additions have their own verification receipts.

**Start with the [ten-proposal solution ledger](TEN-SOLUTIONS.md),
[brief mathematical handoff](HANDOFF-FOR-ALEXANDER.md), and
[formalization coverage](FORMALIZATION.md).** The [original proposals](TEN-RESEARCH-IDEAS.md)
preserve the questions as first posed; the ledger records the subsequent proofs
and precise remaining refinements.


## Wong 2024: the checked mathematical bridge

The current focus is the [source-linked Wong–Alexander outline](WONG-ALEXANDER-OUTLINE.md)
and its [machine-readable connection map](research/wong/connection-map.json).
The finite gARG model, sample restriction and retained-node contraction are
connected by exact preservation theorems. The actual gARG completion theorem
embeds the same finite topology into two infinite populations with real dates,
finite roots and finite children: one whole population is an inspecies and
maximal specieslike cluster, while the other fails IAP. This is an abstract
non-identifiability result, not an inference of an organismal pedigree.

The [claim-by-claim coverage map](notes/WONG-ALEXANDER-BRIDGE-STATUS.md) separates
checked graph mathematics from unformalized stochastic models, biological
owner assignments, executable serialization and software-performance claims.
The paper is not advertised as entirely proved, and no global graph
self-similarity claim is made.

## Current results

| Direction | Result | What remains |
|---|---|---|
| Exact Thue-Morse avoidance | Closed form for every actual maximum $`L(v)`$, proved ten-coordinate binary recurrence, executable digit evaluator, sharp bound and exact equality family. | Broader substitution targets and arbitrary-phase digit recurrences. |
| Stability and phase | Optimal leading coefficient $`8/3`$, exact phase and finite-edit maxima, finite-edit equality test, and sharp universal additive constant $`8m-1`$. | The individual best integer constant is now computed exactly by FiniteEditOptimum; efficient complexity and a smaller cutoff remain open. |
| Quantitative aperiodicity | A local period/antiperiod break modulus gives an explicit matching-length bound; aperiodicity alone permits arbitrarily slow finite avoidance. | Optimal modulus-dependent rates for specific word families. |
| Fixed vertex genders | Cap two suffices for every prescribed aperiodic binary target, even in a whole-graph inspecies. Lower caps are impossible. | Optimal root count and larger-width classification. |
| Critical degree | Conservation, general-$`k`$ rigidity, and an exact finite-port encoding of every critical population tail. Legal periodic schedules realize all words. | Finite width alone does not imply a periodic schedule. |
| Species and boundaries | Productive pruning preserves eligibility and the entire infinite word language. Exact maximal-cluster distinctions and optimal deletion-only boundary repair are proved. | Repairs permitting vertex deletion, new edges or relabelling have a different optimization problem. |
| Stateful cellular automaton | A complete three-state rule has optimal static east bound one but no finite-support horizontally moving spaceship; an explicit oscillator exists. | Stronger certificates for natural binary or published rules. |

The [core audit](verification/formal-audit.json) and [real-number audit](verification/real-audit.json)
record exact endpoints, source hashes and permitted proof dependencies. The
default library is Std-only; the real-number project has a pinned Mathlib
dependency. The [status table](STATUS.md) states the mathematical boundaries.

## Sources and navigation

- [Question ledger](QUESTION-LEDGER.md): where each question originated and what has been answered.
- [Research map](RESEARCH-MAP.md): motivation and relationships between directions.
- [Ten proposals](TEN-RESEARCH-IDEAS.md): precise targets, proved seeds and next decisive tests.
- [Prior-work audit](PRIOR-WORK-AUDIT.md) and [additional source checks](notes/ADDITIONAL-SOURCE-CHECKS.md): verified precedents and remaining priority uncertainty.
- [Biological model scope](BIOLOGICAL-MODEL-SCOPE.md): organism genealogy, fixed genders and genetic inheritance are distinct models.
- [Sharp proof](research/thue-morse/NEXT-INVARIANT.md), [full-height formula](research/thue-morse/FULL-HEIGHT-CONJECTURE.md), and [formalization notes](FORMALIZATION.md): reviewable mathematics.
- [Reproduction](REPRODUCE.md), [statement review](verification/GAP-CLOSURE-REVIEW.md), and [verification receipt](verification/FORMALIZATION-RECEIPT.md): exact evidence.
- [Sources](SOURCES.md), [provenance](PROVENANCE.md) and [editable outreach draft](OUTREACH-DRAFT.md): attribution and an optional owner-controlled review route.

Alexander's [2013 positive theorem](https://arxiv.org/html/1212.0186v2), his
[inspecies results](https://arxiv.org/html/1201.2869), and his
[2026 cluster examples](https://arxiv.org/html/2602.05274v1) remain attributed
prior work. The separate [classification manuscript](https://github.com/avg-netizen/biological-unavoidability)
supplies the target-dependent avoiding graph. The quantitative and structural
extensions here require external mathematical and priority review; formal
verification is evidence for the encoded statements, not a novelty certificate.

## New closed refinements

The [individual finite-edit optimum](notes/REFINEMENT-INDIVIDUAL-FINITE-EDIT.md) is now an exact finite algorithm for every fixed target agreeing with Thue–Morse from a supplied cutoff. The graph and target both use that same edited word. The finite search is proved sufficient and the best integer constant is attained; no efficient-runtime claim is made.

For Wong's graph mathematics, [automatic finite interval output](notes/WONG-SIMPLIFICATION.md) now follows sample restriction and fixed-node contraction. A [fully sample-supported diamond](notes/WONG-DIAMOND.md) proves the precise loss of a crossover cutoff. The [finite-input specieslike verdict obstruction](notes/WONG-FINITE-IDENTIFIABILITY.md) makes the infinite-completion limitation explicit. These checked statements do not establish that DNA observations determine biological species.
