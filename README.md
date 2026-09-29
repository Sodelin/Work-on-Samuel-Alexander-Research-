# Working on Samuel Alexander's research

**29 September integration update:** see the [complete result-family ledger](research/publication-2026-09-29/COVERAGE.md), [full publication guide](PUBLICATION-GUIDE-2026-09-29.md), and [new checked embedding/pruning/rank package](research/open-questions/continuation-2026-09-29/RESULTS.md). The dated snapshots below preserve their original evidence and delivery state. The new generic realizing-state and mortal-rank results supersede earlier descriptions of those particular obligations as written-only.


A public, AI-assisted mathematics notebook on labelled ancestry graphs, sequence avoidance, specieslike clusters, inheritance models, and related questions. The repository contains precise theorems, computations, proposed extensions, source comparisons, and verification records. They have different evidence levels.

**Start here: [Complete plain-language mathematics report](MATH-RESEARCH-REPORT.md).** It explains what was proved, what remains open, and how the work relates to Alexander's source questions. For current status by topic, read [Ten solutions](TEN-SOLUTIONS.md) and [three-track research progress](RESEARCH-PROGRESS.md).

For the separate Royal Society track, read [When the same appearance can hide a different future](TIME-AND-MEMORY.md): the paper's questions, our precise results, biological implications, and remaining gaps on one page.

## Current checkpoint

The newer research is in [draft PR #6](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/pull/6), which is **open and unmerged**. Its last cited hosted proof checkpoint is [commit `a2644182`](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/commit/a2644182b147eb40816abb278e00c3c6d4709eb8): [Verify run 36173386580 passed](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/actions/runs/36173386580) with **405 core, 317 real/Mathlib, and 234 standalone selected Lean declarations**. The numbers include supporting lemmas; they are not counts of discoveries or solved historical problems. Subsequent documentation commits do not change the proof snapshot certified by that run.

| Direction | Current result | Remaining boundary |
|---|---|---|
| Thue–Morse matching paths | Sharp length bound, equality cases, [complete maximum at every start](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/a2644182b147eb40816abb278e00c3c6d4709eb8/notes/FULL-HEIGHT-PROOF.md), and a proved ten-coordinate digit evaluator | Broader targets, joint phase digit recurrences, literature priority |
| Permanent vertex labels and child cap | [Cap two suffices](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/codex/research-followup-2026-09-25/notes/CAP-TWO-SPECIES.md) for the specified arbitrary-target binary construction, retaining whole-graph inspecies/reflection; smaller caps fail | Optimal root count and other model classes |
| Critical genealogy structure | Eventual minimum crossing width forces [general finite-label tail rigidity](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/a2644182b147eb40816abb278e00c3c6d4709eb8/notes/GENERAL-RIGIDITY-THEOREM.md) | Larger-width classification |
| Maximal ancestry clusters | [Real founder-window existence theorem](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/codex/research-followup-2026-09-25/notes/REAL-FOUNDER-WINDOW-THEOREM.md) under explicit birth and branching assumptions | Unique partitions and empirical species identification |
| Shared inheritance and pedigree | [One raw random history](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/022df5fc1240c76c6837e89d38e3009cd020b341/research/feedback-speciation/PURE-INDUCTION-ANCESTRY.md) realizes finite marker-count histories and an almost-sure ancestry property | Separate raw infinite-stream fixation-event equality |
| Wong ancestral recombination graphs | Deterministic simplification, count absorption, and physical waiting-time law checked at their stated scopes | Full marked spatial ARG/process correspondence |
| Time and self-reference | Bounded exact-abstraction results and a reviewed two-model information-loss example | Broad source questions and source-specific equilibrium framework |

## Where to look

1. [Mathematics research report](MATH-RESEARCH-REPORT.md): a friend-readable account of the whole project, including evidence and remaining work.
2. [Ten solutions](TEN-SOLUTIONS.md): the exact status of the ten notebook proposals. The [original proposals](TEN-RESEARCH-IDEAS.md) are retained as development history.
3. [Question ledger](QUESTION-LEDGER.md): source attribution and the boundary of each answer.
4. [Research progress](RESEARCH-PROGRESS.md): current Wong, inheritance/ancestry, and abstraction tracks.
5. [Formalization](FORMALIZATION.md) and [status](STATUS.md): precise encoded claims and checks; [research architecture](RESEARCH-ARCHITECTURE.md) explains how publication and review are separated.

Alexander's [2013 unavoidability theorem](https://arxiv.org/html/1212.0186v2), [inspecies work](https://arxiv.org/html/1201.2869), and [2026 cluster examples](https://arxiv.org/html/2602.05274v1) retain their attribution. The separate [classification manuscript](https://github.com/avg-netizen/biological-unavoidability) supplies the target-dependent avoiding graph. Formal verification of a stated theorem does not establish worldwide novelty, biological applicability, or external expert endorsement.

The submission titled “Exact Thue–Morse matching heights in an avoiding population” was observed in [VibeMathed's under-review queue](https://vibemathed.com/queue) on 27 September 2026 UTC. Queue presence is not a curator decision.

Math-rendering repair: [affected-file provenance and presentation boundary](verification/github-math-render-fix-2026-09-27.json). The historical proof commit and frozen packet manifests remain available at their original snapshots.
