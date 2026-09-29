# Review release: finite sampling and barrier ordering

Prepared 2026-09-25. This is a reproducible research example and internal review package, not an accepted publication or an established priority claim.

## Precisely checked statements

| Component | Selected endpoints | Exact formal scope |
|---|---:|---|
| FiniteFixation | 11 | Finite forward probabilities; harmonic-certificate identification; transient-mass and error bounds; pulse-mixture convergence |
| FiniteEpigenetic | 10 | Explicit 81-state N=1 count kernel; boundary closure; terminal mass; exact pulse values; finite genetic/epigenetic comparison |
| DeterministicEpigenetic | 10 | Reduced frequency recurrence; selected-background invariant; exact generation-four marker bound; all subsequent means; pure-induction mean; conditional limit bound |
| RankingReversal | 3 | Joint opposite ordering; genetic barriers on opposite sides of 3/7; explicit gap between the model outputs |

The [combined receipt](verification/combined-receipt.json) lists all 34 selected names, exact source/log/object hashes, and standard axiom reports. The count measures selected checked declarations, not mathematical importance or a paper-completion percentage.

The finite model's limiting RI is 937945083/2233177303 for genetic inheritance and 3/7 for pure epigenetic induction. The deterministic genetic RI is at least 1027087570805/2255346713174, strictly above 3/7, at every biological generation from four onward. The common parameters are m=1/4, s=r=1/2 with matched secondary-contact initialization and marker pulse. One diploid offspring is sampled per deme; selfing is permitted.

## Verification provenance

FiniteFixation, FiniteEpigenetic and RankingReversal have directly observed terminal exit code zero. DeterministicEpigenetic emitted a clean complete log and fresh compiled object before its process handle was lost during a task interruption. The original exit code was not recovered. RankingReversal subsequently imported that object and exited zero. The combined receipt explicitly uses null for the unretrieved exit and PASS_WITH_RECOVERED_EXIT_EVIDENCE for its status.

No compiler was launched by the receipt writer. A fresh clean-machine dependency build has not been performed for this release. Lean 4.33.1 and the exact Mathlib commit are pinned. Check.ps1 records the local cached-dependency route. Portable Lake declarations include the four checked modules.

## Boundaries that remain visible

- The correspondence from the source's full phased life cycle to the count and reduced-frequency models is written and independently audited using exact arithmetic. It is not a Lean transport theorem.
- The deterministic common-limit existence proof is written and independently audited. The checked limiting-RI theorem explicitly takes a convergence premise. The unconditional finite-tail reversal does not need that premise.
- The finite proof uses actual finite forward distributions. It does not construct a separate probability measure on infinite paths.
- This is a deliberately specified N=1 offspring-sampling extension, not a unique finite interpretation or an empirical species model. General population size, imperfect induction, alternative migration/mating rules, modifiers and culture remain additional questions.
- Marker fixation, organism-level ancestry, and locus-dependent ancestral recombination graphs are different observations. Neither Alexander-IAP nor completion of the Wong paper follows from this result.
- Novelty, external mathematical statement review, VibeMathed eligibility and journal suitability remain unestablished.

A later uncompiled convergence draft, if present in the working directory, is excluded from this release and does not change its formal scope.

## Reading and handoff order

Start with [README.md](README.md), then [FINITE-RESULT.md](FINITE-RESULT.md), [DETERMINISTIC-COMPARISON.md](DETERMINISTIC-COMPARISON.md), and [SOURCE-MODEL-CONTRACT.md](SOURCE-MODEL-CONTRACT.md). The independent audit notes and [PRIOR-WORK.md](PRIOR-WORK.md) state what was checked and credited. [RESEARCH-QUESTIONS-AND-HANDOFF.md](RESEARCH-QUESTIONS-AND-HANDOFF.md) contains precise remaining questions, a Samuel Alexander draft and a VibeMathed eligibility inquiry.

The coordinating task owns public integration and outreach. This release is local and no message or submission to a human has been sent by this lane.
