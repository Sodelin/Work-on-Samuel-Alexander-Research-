# Research follow-up publication status

## Completion pass: proved statements and reproducible checks

Start with the [completion map](COMPLETION-MAP.md). It distinguishes proved statements, their source questions, and the remaining questions about priority and biological usefulness.

The current completion packet closes three previously written-only proof obligations:

- **Founder-window specieslike clusters:** a complete existence and constrained-maximality theorem with literal real birthdates, including tied dates, on natural-number organism identifiers. Every organism belongs to a maximal reflecting specieslike cluster whose founders lie in a fixed nonnegative real-time window. The seed, union/intersection, maximality and reindexing arguments are checked. Eight promoted modules add 50 selected endpoints, bringing the real library to **151**; the core remains **405**. See the [theorem and exact assumptions](notes/REAL-FOUNDER-WINDOW-THEOREM.md) and [frozen owner packet](verification/founder-window-packet.json).
- **Universal avoiding populations:** the full generic population construction and nonuniversality proof are compiled, including exact infinite-word language preservation, root equivalence, and exclusion of every countable family under injective edge-preserving maps or maps with a finite global bound on edge stretching. See the [statement and scope](research/open-questions/embedding/UNIVERSAL-AVOIDER-NONEXISTENCE.md).
- **Ordinal characterization:** arbitrary labelled graphs admit an ordinal certificate exactly when they avoid the target; finite branching gives a natural-number certificate. The actual binary natural-date population history tree is also checked: avoidance is equivalent to well-foundedness, the artificial root rank is omega, and the specified finite/omega/omega-plus-one pruning stages are proved. See the [scope map](research/open-questions/ordinal/ORDINAL-CHARACTERIZATION.md).

The new [research artifact auditor](checks/audit_research_artifacts.py) compiles **11 standalone modules with 52 selected endpoints**, in dependency order, after the ordinary library builds. It checks the actual compiler's reported axioms and rejects proof placeholders. The [local combined receipt](verification/research-artifacts-local.json) records the final local audit; the workflow uploads a fresh receipt for its exact checkout. The generic embedding proof is integrated through this standalone gate, instead of changing the frozen real-library aggregate. Its original handoff receipt's proposed library placement is therefore superseded by this reproducible integration route.

The ordinary hosted build for the resulting commit is recorded in [PR #6](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/pull/6) and its [checks](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/pull/6/checks). Publication-stage notes do not predict the result of that subsequent build. These counts describe audited declarations, not independent discoveries.

Still outside the checked claims are the written Schmidt-rank/kernel discussion, the realizing-case pruning fixed-point statement, and extension of the actual root-rank/pruning modules beyond the binary natural-date model. Arbitrary unbounded-stretch or ancestry-only embeddings, fixed child-cap preservation, empirical species identification, and global novelty are also not established. Those boundaries do not leave the displayed formal theorem statements unfinished.

The [genomic-identification notebook](research/open-questions/genomic-identifiability/README.md) preserves the distinction between ambiguity of abstract infinite completions and identification under a specified statistical model. The positive three-taxon example uses a known law. Its prose now states the probability of each particular alternative correctly, separately from their combined probability; the Lean law was already correct.

## Integrated refinement packet

The [research closure packet](verification/research-closure-packet.json) records 32 exact files, with **405 core and 101 Mathlib selected endpoints** passing fresh local aggregate checks. This adds 43 endpoints in ten modules to the preceding Wong snapshot. It includes the exact individual finite-edit optimum, automatic finite interval simplification, a sample-supported diamond whose distinct inputs have the same finite output, and the three finite-completion identification endpoints. The owner's source and receipt bytes are preserved exactly. The ordinary hosted build is recorded at the resulting commit in [PR #6](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/pull/6).

## Earlier checked Wong follow-up

This checked follow-up extends the initial public snapshot at `19544a4d7608c8cc0d5a1205605c0f38631ca05f`. The exact 33-file inventory is in [verification/wong-packet.json](verification/wong-packet.json), published alongside those files. All packet hashes matched at publication intake; original receipt bytes are preserved.

At that earlier snapshot, local audits passed **393 core and 70 Mathlib selected endpoints**, permitting only `propext`, `Classical.choice`, and `Quot.sound`. This adds 63 selected endpoints across three core modules and five Mathlib modules.

The central theorem embeds a finite interval ARG into two connected infinite populations preserving its raw edges and ancestry. One completion is a whole inspecies and maximal specieslike set; the other fails the identical ancestor point property (IAP). This is ambiguity of abstract infinite completions, not biological owner-map inference. Other results cover sample restriction, contraction, explicit ARG examples, breakpoint locality, local arity and ordered event encodings.

Read the [Wong-Alexander outline](WONG-ALEXANDER-OUTLINE.md), [connection map](research/wong/connection-map.json), [delivery map](DELIVERY-MAP.md) and [refinement ledger](REFINEMENT-LEDGER.md). Stronger unanswered targets remain explicit. A literal binary-kernel wrapper, proof-feedback-tool edits, caches and uncompiled refinement drafts are excluded.

The Wong snapshot `bcef6da64672310b314f2bc17c96f9535fcaaf5b` passed [Verify run 36120063594](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/actions/runs/36120063594). A later commit's hosted result is recorded separately in [PR #6](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/pull/6). That earlier repository build did not automatically compile the isolated research artifacts. The current completion pass adds the standalone gate described above.

## Initial snapshot checked and shared

The initial snapshot at `19544a4d7608c8cc0d5a1205605c0f38631ca05f` passed [Verify run 36116271138](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/actions/runs/36116271138), including the Lean build, 370 core and 30 Mathlib endpoint audits and computational checks. Its final formatting audit covered 109 Markdown files and 3,068 mathematical expressions with zero delimiter or MathJax rendering errors.

The reviewed email to Dr. Alexander was sent on 25 September 2026 with immutable links to that initial snapshot. No second email accompanies this update. **Exact Thue–Morse matching heights in an avoiding population** was submitted to VibeMathed on 25 September 2026 and was observed under review in the [public queue](https://vibemathed.com/queue). Its proof links remain pinned to that initial snapshot. The [saved proposal](research/research-packet/VIBEMATH-SUBMISSION-DRAFT.md) is historical preparation material; current submission status supersedes its earlier pending wording.

The sharp quantitative Thue-Morse result answers a question in the separate September AI-assisted manuscript. The [ten extensions](TEN-SOLUTIONS.md) are not ten historic Alexander open problems. [Exact open-problem attribution](research/research-packet/OPEN-PROBLEM-STATUS.md) remains available. Worldwide priority and independent expert review remain unconfirmed. Historical audit notes preserve their original stage; use this page, STATUS.md and the exact-commit PR receipt for current delivery status.

The [original handoff](HANDOFF-FOR-ALEXANDER.md) and [saved line-ending fix](notes/LINE-ENDINGS.md) remain available.
