# Feedback, ancestry and gene–culture dynamics

Review package, 25 September 2026. Start with this file. This is a reproducible mathematical research draft; originality, external statement review, biological validity and venue eligibility remain unsettled.

## Public integration

The archived local run below describes the handed-off source snapshot. Read
[PUBLIC-INTEGRATION.md](PUBLIC-INTEGRATION.md) for the formatting transformations,
current repository audit registration, and exact-commit hosted verification.

## What is ready

All seven packaged Lean source files were freshly compiled with Lean 4.33.1 against Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474. The runner audited 72 selected endpoints: 53 in five new modules and 19 in two unchanged dependency modules. All printed only standard Lean axioms. The exact source hashes, declarations and compiler mode are in [the receipt](package/verification/receipt.json).

1. **A conditional ancestry classification.** Under explicit strong pedigree assumptions, an infinite set satisfies Alexander's identical ancestor point axiom precisely when it is contained, apart from finitely many organisms, in one recurrent reproductive component. That component is unique. Sufficiently late component tails satisfy the actual connectedness, convexity, IAP and reflection predicates. One-way and bidirectional two-deme examples are also checked.
2. **A boundary example for the cultural idea.** A rational polarized cultural equilibrium is locally asymptotically stable in the full two-dimensional model. An explicitly culture-dependent positive neutral-exchange rate nevertheless makes neutral allele frequencies converge. Culture is distinct while this neutral marker homogenizes. The model has one-way coupling, not a full reciprocal epigenetic–cultural model.
3. **A result directly in a published gene–culture model.** From the affinity-bias equations of Fogarty, Zhang and Feldman (2025), the proof derives simplex preservation, an exact drift identity, absence of a fixed point with both polymorphisms under positive selection, and a global cultural fixation bound. With B initially present in both genetic backgrounds, arbitrary admissible affinity sequences satisfy
   0 <= 1 - q_n <= max(x2(0)/x1(0), x4(0)/x3(0)) / (1+s)^n.
   The theorem includes an actual recursively defined evolution and epsilon convergence, not only assumed recurrence relations.

The third result is the most direct contribution to an existing published model. Its comparison argument is standard nonnegative-matrix order preservation; the source-specific rate and its priority need review. See [the final prior-art check](RATE-PRIOR-ART-CHECK.md). The ancestry result connects most directly to Alexander, but its universal local-dissemination assumption excludes ordinary lineage extinction and has probability zero in the standard fixed-size independent two-parent model. That limitation is part of the result.

## Read the mathematics

- [MANUSCRIPT.md](MANUSCRIPT.md): complete conditional ancestry proof, stochastic interpretation explicitly labelled written-only, cultural counterexample and prior-work discussion.
- [FOGARTY-GLOBAL-RATE.md](FOGARTY-GLOBAL-RATE.md): the source-model rate theorem and complete proof.
- [CLAIM-LEDGER.md](CLAIM-LEDGER.md): manuscript-to-declaration mapping and exact exclusions.
- [OPEN-PROBLEMS.md](OPEN-PROBLEMS.md): source-proposed directions distinguished from questions newly posed here.
- [PRIOR-WORK-AUDIT.md](PRIOR-WORK-AUDIT.md) and [SOURCE-AUDIT.md](SOURCE-AUDIT.md): literature evidence, nearest prior work and access limits.
- [REVIEW-NOTES.md](REVIEW-NOTES.md) and [rate-statement-review.md](rate-statement-review.md): internal adversarial and statement reviews.
- [HANDOFFS.md](HANDOFFS.md): Samuel review draft, candidate VibeMathed entry and publication routing.
- [WONG-REMAINING-WORK.md](WONG-REMAINING-WORK.md): separate whole-paper formalization status.

## Reproduce the verified compilation

The successful route uses an existing dependency directory containing the pinned Mathlib checkout and its compiled dependencies. Install Lean 4.33.1, then run from PowerShell:

    ./package/Check-All.ps1 -MathlibPackages /path/to/existing/.lake/packages -LeanExe /path/to/lean

This script freshly recompiles the packaged custom sources sequentially, checks the dependency revision, audits endpoint axioms, and writes package/verification/receipt.json. It uses one compiler worker and a 4096 MB per-process limit. Git ownership trust is limited to the explicitly supplied Mathlib path for that invocation; no global Git setting is changed.

A portable Lake configuration and pinned manifest are included in package/. Lake successfully loaded the configuration and translated it to TOML without fetching dependencies. A conventional clean checkout can obtain dependencies with Lake and then build the five default module targets. **A clean-machine dependency download and hosted CI have not been tested for this package.** Do not replace the recorded local verification claim with a clean-CI claim. The dependency binaries used here were pre-existing; these sources were freshly compiled.

## What has not been solved

This package does not prove that DNA uniquely determines species, that cultural societies constitute biological species, that arbitrary ancestry graphs are self-similar, or that the full Wong paper is formalized. It does not prove a full genetic–epigenetic–cultural mechanism or demonstrate one in biological data.

The unresolved next step is to replace universal lineage dissemination by biologically meaningful extinction-or-establishment conditions and derive those conditions from an explicit reproduction model. Source-proposed finite-population epigenetic and nonvertical-learning questions also remain open in this package.

No named long-standing open mathematical problem is claimed solved. Internal AI review and Lean acceptance do not establish novelty. The current material is ready for review and reproducibility checks; VibeMathed eligibility and publication merit are not certified. All outreach text is a draft; no message was sent by this package-producing lane.

## Provenance

The user proposed investigating feedback among inherited states, expression, learning and reproductive separation. AI agents developed the mathematical models and proofs, formalized them, searched sources and performed internal reviews. The two unchanged Alexander predicate modules come from the user's existing research repository at the immutable revision recorded in [SOURCE-ORIGINS.md](SOURCE-ORIGINS.md). No external reviewer endorsement is implied.
