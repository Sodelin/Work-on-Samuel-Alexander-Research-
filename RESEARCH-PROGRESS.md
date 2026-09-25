# Research progress: what is finished, what is next

Updated 25 September 2026, 17:34 UTC. This page is the public entry point for the current research work. [Review branch and draft PR #6](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/pull/6) · [Research architecture](RESEARCH-ARCHITECTURE.md).

## Latest verified checkpoint

**GitHub verification passed at [1775ecc8](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/commit/1775ecc85030c0fc55ad17ad4f21490976007a50): 405 core, 293 real and 167 standalone selected Lean declarations.** [Exact hosted run](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/actions/runs/36163709838).

The later [publication checkpoint 42a47a42](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/commit/42a47a4210a11e457a93adc406876af39d417132) adds readable abstraction examples, the [hosted admission receipt](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/42a47a4210a11e457a93adc406876af39d417132/research/wong/completion/probability/HOSTED-ADMISSION.json), and prior-art corrections. It preserves the certified proof sources.

These are selected audited declarations, including supporting lemmas. They are not a count of independent discoveries or open problems solved. Later documentation does not change the source commit certified by this run.

## 1. Wong: from a count process to elapsed time

The deterministic packet added 65 selected declarations concerning ancestry and interval representations, with explicit source correspondence and independent review. Its original 274-declaration real-project integration passed. [Deterministic evidence](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/46aac52e214311fb2c2230b1b4fe37c42ef9e1a9/research/wong/completion/verification/deterministic65/SOURCE-CORRESPONDENCE.md).

**Now published and hosted-verified:** another 19 probability declarations construct the trajectory law of the specified stopped count chain and prove that it reaches one lineage after finitely many jumps with probability one. The combined real audit is now 293 declarations. The source-to-statement comparison and independent statement review are included. [Readable result](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/1775ecc85030c0fc55ad17ad4f21490976007a50/research/wong/completion/probability/RESULT.md).

**Next finish:** construct the exponential waiting-time law and prove that absorption takes finite physical time. A finite number of jumps and the elapsed time attached to those jumps need separate statements. The full spatial/marked ARG projection, Little ARG results and remaining exporter obligations remain open in the [paper coverage ledger](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/1775ecc85030c0fc55ad17ad4f21490976007a50/research/wong/completion/COVERAGE.md).

## 2. Alexander connection: counts, parents and infinite ancestry

The published finite feedback comparison contains **34 checked declarations**. Under its specified assumptions, the finite genetic score is approximately 0.420005, below the epigenetic value 3/7, approximately 0.428571. The deterministic genetic comparison is above 3/7 from the stated fourth generation onward. This illustrates a parameter-specific ranking reversal between the chosen models. [Worked result](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/4fd6f7cc89fda47f245e9ae28fca140fd04de783/research/feedback-speciation/finite-epigenetic/FINITE-RESULT.md).

A subsequent **four-declaration parent-choice checkpoint** is now published and hosted-verified. It checks normalization, a complete parent-table event, one ordinary transition and the distinct initialization pulse. [Reproducible packet](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/ae40ea80a049355e1d463743966464ac75272830/research/feedback-speciation/pure-induction-finite/README.md) · [Its successful hosted run](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/actions/runs/36163149266).

**New local checkpoint awaiting publication and independent admission:** R1/R2 now checks the raw random-choice mapping, all 81 ordinary and nine pulse transition identities, and zero probability outside the embedded support. Its worker reported a successful pinned Lean check and released the compiler. This source is not included in the public 167-declaration audit above.

**Next finish:** R3–R6 must supply the infinite path law, the conditional window argument and the precise ancestry comparison. Finite-prefix examples, possible infinite histories and probability-one conclusions remain distinct.

Earlier literature already contains finite stochastic epigenetic models, normalized marker fixation, and effects of migration/induction timing. Our candidate contribution is the exact specified comparison and its deterministic relationship; priority remains unestablished. [Detailed attribution and biological-scope correction](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/42a47a4210a11e457a93adc406876af39d417132/research/feedback-speciation/PRIOR-ART-UPDATE-2026-09-25.md).

## 3. Information lost through simplification

The completed worked bridge compares a finite cell-state toy with a decision device that can retain an arbitrarily long finite history. Both admit the same four-state description for the specified actions and output.

The concrete insight is that a description retaining only the currently visible bit can support some actions but fail after a probe is allowed. Retaining one additional memory bit restores exact prediction. A written refinement argument establishes minimality relative to those actions and that output.

**Published:** [worked example and proof](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/42a47a4210a11e457a93adc406876af39d417132/research/open-problems/time-self-reference/controlled-abstraction-bridge/BRIDGE.md) · [reproduction and evidence guide](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/42a47a4210a11e457a93adc406876af39d417132/research/open-problems/time-self-reference/controlled-abstraction-bridge/README.md).

**Evidence:** written derivations, bounded Python checks and independent review. The general Q04/Q09 Lean results are reused; these new examples have not been newly formalized in Lean. The work uses established abstraction/congruence ideas, and does not claim a unified theory of organisms, cognition or consciousness.

[Published source-question ledger](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/138dd529643ae5706a9df6a750bd6344ab967a8a/research/open-problems/time-self-reference/problem-ledger.json). None of its twelve broad questions is declared completely solved.

## Work and publication ledger

| Deliverable | Verified evidence | Remaining step |
|---|---|---|
| Wong deterministic additions | 65 declarations, source correspondence, review and hosted pass | Remaining paper obligations |
| Wong count absorption | 19 additional declarations; hosted 293-real audit passed | Actual holding-time law and finite physical time |
| Finite feedback ranking | 34 declarations published and hosted-checked | Wider parameters and empirical applicability remain separate |
| First parent-choice packet | Four declarations published and hosted-checked | Full ancestry construction |
| R1/R2 transition correspondence | Worker reports local Lean pass; not yet in public audit | Independent admission and publication |
| Controlled abstraction bridge | Published written proofs, finite replay and independent review | Optional mechanization of the new refinement lemma |
| Same-prefix/noisy observations | Previously reported local 23-declaration packet | Publication admission remains pending |
| Q10 order-convex Nash obstruction | Previously reported written construction, finite checks and review | Auditor adjudication and publication remain pending |

## How this is being managed

Three research leads own their separate mathematical obligations. Shared workers receive one bounded assignment at a time. The coordinating auditor checks specific failure points, reconciles source interpretations and publishes accepted checkpoints. One local compiler owner is recorded at a time; source preparation can proceed independently. [Roles and resource limits](RESEARCH-ARCHITECTURE.md).

GitHub publication, outside expert review, author email and VibeMathed curation are separate events. This progress update records research and GitHub evidence; it does not represent a new email, site submission or external endorsement. Completed tasks remain visible and unarchived.
