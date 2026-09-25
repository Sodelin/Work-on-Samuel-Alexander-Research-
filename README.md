# Working on Samuel Alexander's research

This repository develops bounded follow-on questions from Samuel A. Alexander's [2013 paper on biologically unavoidable sequences](https://www.combinatorics.org/ojs/index.php/eljc/article/view/v20i1p31) and the [2026 classification manuscript](https://github.com/avg-netizen/biological-unavoidability). It keeps proofs, finite computations, conjectures, and unfinished formalization separate.

**Start here:** [Research map](RESEARCH-MAP.md) explains the research directions in plain language and traces each to its sources. [Brief handoff](HANDOFF-FOR-ALEXANDER.md) gives a compact route for Dr. Alexander or another reviewer. The [status table](STATUS.md) specifies exactly what is proved, computed, or Lean checked.

> **Current mathematical status:** We prove a quadratic upper bound for finite matching paths in the classification paper's Thue-Morse avoiding population. An exact scan suggests a sharper linear bound, but does not prove it. Two degree-counting observations are proved in prose, with their arithmetic consequences checked in Lean. A short deduction shows that the binary avoiding graph is a specieslike cluster under Alexander's 2026 definitions; it is not Lean checked. A cellular-automaton note gives a conditional periodic-lifeline method and corrects an initially overoptimistic speed-bound target.

## Results and research questions

| Line | Current result | Evidence | Next mathematical step |
|---|---|---|---|
| [Thue–Morse path length](notes/THUE-MORSE-PATHS.md) | `L(v) <= (v+1)(v+6)/2` for the specific avoiding population. A proposed sharp bound `3L(v) <= 8v-1` has no counterexample for `1 <= v < 131072`. | Written proof from overlap-freeness; [exact set BFS](checks/scan-8192.json), [compressed bitset-transition scan](checks/scan-bitset-131072.json.gz), and tests. The linear bound remains a conjecture. | Prove or refute the linear bound and the proposed equality family `v=3*2^n-1`. |
| [Degree boundary](notes/DEGREE-BOUNDARY.md) | If there are `k` labels and a child cap `d<k`, no infinite population satisfies the axioms. At the binary fixed-vertex-gender, two-child boundary, gender counts in any birthdate prefix differ by at most the number of roots. | Direct edge counts; [Lean arithmetic lemmas](lean/SamuelAlexanderResearch/DegreeBounds.lean) compile from explicit count premises. [Formalization scope](notes/FORMALIZATION-SCOPE.md) states what Lean has not checked. | Determine whether every aperiodic binary target has a fixed-gender avoiding witness with at most two children per vertex. |
| [Specieslike-cluster bridge](notes/SPECIESLIKE-BRIDGE.md) | The entire binary avoiding graph `P_s` satisfies Alexander's 2026 specieslike-cluster axioms after labels are forgotten. Thus restricting witnesses to whole-graph specieslike populations leaves the binary classification unchanged. | Short written graph proof from the two source definitions. No Lean proof, novelty claim, or biological species prediction. | Check whether a maximal specieslike *subset* can retain the label-coverage axioms, especially at its boundary. |
| [Periodic lifeline certificate](notes/PERIODIC-LIFELINE.md) | A rule with distinct predecessor witnesses in two step sets has periodic lifelines; for spaceships, constant-label paths give a stronger convex-hull-intersection bound than the alternating polygon. | Reduction to Alexander's periodic theorem and a [finite local-rule checker](checks/check_local_certificate.py). No Lean proof or new rule-specific speed theorem. | Test whether state or phase constraints yield a bound beyond the static intersection, then check prior work. |
| [Automatic-sequence corollary](notes/AUTOMATIC-SEQUENCES.md) | Universality of the specific binary family `P_s` is decidable when `s` is supplied by a finite automaton. | Direct combination of the 2026 manuscript's criterion with the known decidability of ultimate periodicity for automatic sequences. | Implement a certified or independently checked decision procedure if useful. |

The notes identify their precise graph model and quantifiers. A finite search cannot prove an infinite claim; a Lean build checks only the statements encoded in its source. [STATUS.md](STATUS.md) lists the claim by claim verification boundary.

## Navigate and reproduce

- [RESEARCH-MAP.md](RESEARCH-MAP.md): motivation, dependencies, precise questions, current answers, and possible extensions.
- [HANDOFF-FOR-ALEXANDER.md](HANDOFF-FOR-ALEXANDER.md): short external review guide and three specific questions.
- [STATUS.md](STATUS.md): proof, computation, and Lean status for every line.
- [REPRODUCE.md](REPRODUCE.md): local commands and finite-check scope.
- [SOURCES.md](SOURCES.md): primary sources, links, and hashes for the supplied document versions.
- [SEARCH-LOG.md](SEARCH-LOG.md): bounded literature search and its limits.
- [PROVENANCE.md](PROVENANCE.md): attribution and claim language.
- [Local verification receipt](verification/LOCAL-RECEIPT.md): exact checks and saved artifact hashes.
- [GitHub verification workflow](.github/workflows/verify.yml) and [first CI receipt](verification/CI-RECEIPT.md): Lean build and small Python checks on pushes and pull requests.
- [Thue-Morse proof challenge](TASKS/THUE-MORSE-SHARP-BOUND.md) and [degree-boundary Lean challenge](TASKS/DEGREE-BOUNDARY-LEAN.md): bounded briefs for a stronger proof or formalization run.
- [Specieslike-cluster bridge](notes/SPECIESLIKE-BRIDGE.md): direct connection to Alexander's 2026 species paper. An [exploratory interface note](explorations/COMPLEX-SYSTEMS-INTERFACE.md) compares possible dynamical extensions with Levin and Friston; it is outside the core proof program.
- [Outreach draft](OUTREACH-DRAFT.md): an editable note and short video outline that preserve the current proof boundaries. No message has been sent.

The source papers and video transcript are linked and identified, not copied into this public repository. Contributions are welcome when they include exact statements, source citations, a reproducible check where applicable, and a clear separation between checked and conjectural claims.
