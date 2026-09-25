# Brief handoff for Dr. Alexander or another mathematical reviewer

**Purpose.** This public, AI-assisted research notebook follows [Alexander's 2013 paper](https://www.combinatorics.org/ojs/index.php/eljc/article/view/v20i1p31), the separate [2026 classification manuscript](https://github.com/avg-netizen/biological-unavoidability), and a direct connection to [Alexander's 2026 specieslike-clusters paper](https://arxiv.org/html/2602.05274v1). The [research map](RESEARCH-MAP.md) gives plain-language motivation; [STATUS.md](STATUS.md) lists proof, computation, and Lean coverage claim by claim. We would welcome corrections, prior-work pointers, or guidance on which direction is worth pursuing. No message has been sent to Dr. Alexander by this repository.

## What is here now

| Direction | Reviewable item | Current limit |
|---|---|---|
| Quantitative avoidance | A [written quadratic upper bound](notes/THUE-MORSE-PATHS.md) for the longest initial Thue-Morse match from vertex `v` in the classification's explicit avoiding graph: `L(v) <= (v+1)(v+6)/2`. It uses the classical overlap-free theorem. Exact [finite scans and code](checks/) motivate `3L(v) <= 8v-1` and an equality family. | The quadratic proof needs independent review. The proposed linear bound and equality family are **conjectures**, not Lean results; the larger scan covers starts `1..131071`. |
| Restricted populations | A [finite-prefix edge count](notes/DEGREE-BOUNDARY.md) shows that a `k`-label population with finite roots cannot be infinite under child cap `d<k`. At the binary two-child, fixed-vertex-gender boundary, `|M_N-F_N| <= R_N` is necessary. | These are elementary deductions, with no priority claim. [Lean](lean/SamuelAlexanderResearch/DegreeBounds.lean) checks arithmetic consequences from count premises, not the graph-count step. Whether all aperiodic targets admit a two-child fixed-gender avoiding graph is unresolved here. |
| Specieslike clusters | A [short written proof](notes/SPECIESLIKE-BRIDGE.md) shows that the entire binary avoiding graph `P_s` satisfies connectedness, convexity, and the identical ancestor point axiom from Alexander's 2026 species paper. Hence the binary classification is unchanged when whole-graph witnesses must be specieslike in this sense. | No Lean check, priority claim, or inference about real species. The whole graph lacks the separate common-ancestor property used in Alexander's stronger maximal-subset theorem. |
| Cellular automata | A [conditional two-label local certificate](notes/PERIODIC-LIFELINE.md) reduces live-cell paths to Alexander's periodic theorem. For spaceships, the constant-label paths give a stronger convex-hull-intersection bound than the alternating polygon. | The initial alternating-only speed target was weakened by this deduction. No new sharp bound for a specific rule is claimed; the finite rule check is a toy example. |
| Automatic targets | A [direct corollary](notes/AUTOMATIC-SEQUENCES.md) makes universality of the **particular** graph `P_s` decidable when the target `s` is automatic. | It combines two cited results. There is no new implementation, general graph algorithm, or Lean proof. |

## The most useful questions for a brief reply

1. Is the sharp Thue-Morse path-length question, with the exact graph in the [challenge brief](TASKS/THUE-MORSE-SHARP-BOUND.md), familiar from word combinatorics or already answered somewhere? The proven quadratic argument and the finite pattern are in the [note](notes/THUE-MORSE-PATHS.md).
2. Is the [specieslike-cluster bridge](notes/SPECIESLIKE-BRIDGE.md) sound and useful, or does the stronger common-ancestor/reflection setting suggest a better precise question about label coverage inside maximal subsets?
3. Does the two-child, fixed-vertex-gender avoidance variant connect to a known construction or obstruction? The [degree note](notes/DEGREE-BOUNDARY.md) explains why the edge-labelled two-child graph and the four-child fixed-gender lift do not immediately answer it.

A reply on just one point would be useful. Each branch is independent, so a reviewer can ignore the rest.

## Verification and attribution in one place

- [Sources](SOURCES.md) identify the exact papers, transcript context, and hashes of the supplied source versions. The source PDFs and transcript are not rehosted here.
- [Search log](SEARCH-LOG.md) records the bounded prior-work search. It does **not** establish novelty or priority.
- [Reproduce](REPRODUCE.md), [local verification](verification/LOCAL-RECEIPT.md), and [CI verification](verification/CI-RECEIPT.md) give the commands and observed results. CI compiles the pinned Lean arithmetic module and runs small Python checks; it does not prove the conjectures or rerun the long scans.
- [Provenance](PROVENANCE.md) distinguishes attributed earlier results and AI-assisted deductions. A written proof remains subject to independent mathematical review even when local checks pass.
- The optional [complex-systems interface note](explorations/COMPLEX-SYSTEMS-INTERFACE.md) compares possible dynamical extensions with Levin and Friston. It is background for the owner's broader question, outside the core mathematical claims in this handoff.

The repository owner may use the editable [outreach draft](OUTREACH-DRAFT.md) to contact Dr. Alexander. That decision and message belong to the owner.
