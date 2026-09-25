# Working on Samuel Alexander's research

## Latest research progress

**Updated 25 September 2026.** Read the [human-readable progress report](RESEARCH-PROGRESS.md) for the latest results, evidence and remaining work.

| Where to go | What you will find |
|---|---|
| [Research progress](RESEARCH-PROGRESS.md) | What changed, why it is useful, and what is still local or unfinished |
| [Current research PR #6](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/pull/6) | Newer published work awaiting integration with the main branch |
| [Research architecture](RESEARCH-ARCHITECTURE.md) | Three research leads, shared workers, adversarial review and publication rules |
| [Successful hosted verification](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/actions/runs/36148288120) | The exact checked baseline at commit `138dd529` |

## Newly published: a finite-population comparison

[Read the worked example and proof packet](research/feedback-speciation/finite-epigenetic/README.md): adding finite offspring sampling reverses the genetic/epigenetic ordering in the specified matched models. The package includes four Lean modules, exact reference computations, source correspondence, independent internal reviews and a byte-level publication manifest.

Its **34 selected declarations have local evidence**, with the interrupted deterministic exit explicitly qualified in the receipt. This upload adds them to the strict hosted audit, bringing the registered standalone target to **163 declarations in 23 files**. Consult the commit-specific PR checks before treating that new target as passed. The interpretation remains a comparison of stated models, with novelty and biological applicability assessed separately.

## Current focus: the authors' open problems

The [proof structure and obligation ledger](research/open-problems/time-self-reference/PROOF-STRUCTURE.md) is the detailed entry point for the current program.

The main research direction now follows explicit questions in the supplied time/self-reference and minimal-systems papers. Start with the [problem map and first results](research/open-problems/time-self-reference/README.md), the [seven-paper triage](research/open-problems/time-self-reference/OTHER-PAPERS.md), and the [source catalog](research/source-library/public/CATALOG.md).

The first two Lean modules check **16 selected endpoints**: an exact deterministic abstraction criterion and a merge-history counterexample showing why the current grouping alone cannot determine a predecessor-restoring split. The independently exercised source operators agree with the finite witness. Full-policy reachability, published-paper/code correspondence, general changing-player game theory and novelty remain open. The calibration bound is written mathematics with exact finite checks, not a Lean probability theorem.

The hosted standalone audit is extended to **129 selected endpoints in 19 files**. Each commit's actual hosted result is recorded in [PR #6](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/pull/6/checks); adding a gate does not itself mean it has passed. Previous work remains preserved. Broad Wong completion is currently held at documented checkpoints while this priority is pursued.


## Published Wong and feedback baseline — earlier 25 September 2026

The [Wong completion ledger](research/wong/completion/README.md) now maps 52
claim families and records six new integrated modules (58 selected endpoints;
209 in the real aggregate). The [feedback/speciation package](research/feedback-speciation/README.md)
adds a conditional IAP classification, cultural/genetic boundary examples and
a quantitative fixation bound for the published Fogarty affinity model.
Its five new modules contribute 53 selected standalone endpoints; the repository
CI at that snapshot checked 113 standalone endpoints in 17 files.

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

The earlier Wong work is documented in the [source-linked Wong–Alexander outline](WONG-ALEXANDER-OUTLINE.md)
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
