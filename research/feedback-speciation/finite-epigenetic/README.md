# Finite sampling and the ordering of genetic and epigenetic barriers

An exact research example motivated by Planidin et al. (2025), *Adaptive epigenetic divergence can facilitate ecological speciation*. The point is a matched comparison: the same life-cycle parameters can rank genetic and epigenetic barriers differently when final offspring sampling is introduced.

The finite limiting probabilities, deterministic ordering from generation four onward, and their joint ranking reversal are checked in Lean. The [combined receipt](verification/combined-receipt.json) covers 34 selected endpoints across four modules. Deterministic common-limit existence and derivations from the full phased life cycle remain written and independently audited, outside those modules.

## The matched experiment

There are two demes, migration m=1/4, additive selection s=1/2 and free recombination r=1/2. Initially the selected locus is locally adapted in each deme. A single migrant pulse introduces a neutral marker. Compare mutation-free genetic inheritance with complete environmental resetting of the selected epigenetic state after reproduction.

The finite model samples one diploid offspring per deme after the weighted migration/selection/reproduction cycle. It permits selfing. The deterministic model updates the corresponding population frequencies. These choices are part of the theorem.

| Comparison | Genetic marker barrier | Epigenetic marker barrier |
|---|---:|---:|
| Finite model: limiting fixation-based measure | 937945083/2233177303, about 0.420005 | 3/7, about 0.428571 |
| Deterministic model: every generation from four onward | at least 1027087570805/2255346713174, strictly above 3/7 | exactly 3/7 |

The deterministic asymptotic genetic value is numerically about 0.531569, but that decimal is not required for the strict comparison. The exact four-generation upper bound and its preserved convex region establish the ordering.

## Read the result

- [FINITE-RESULT.md](FINITE-RESULT.md): finite theorem, exact fractions, model and proof.
- [DETERMINISTIC-COMPARISON.md](DETERMINISTIC-COMPARISON.md): source-derived recurrences, exact finite-prefix certificate, written common-limit argument and numerical diagnostics.
- [SOURCE-MODEL-CONTRACT.md](SOURCE-MODEL-CONTRACT.md): stage order, initialization and assumptions.
- [RESEARCH-QUESTIONS-AND-HANDOFF.md](RESEARCH-QUESTIONS-AND-HANDOFF.md): precise new questions, Samuel Alexander draft and VibeMathed disposition.
- [PRIOR-WORK.md](PRIOR-WORK.md): nearest literature and the boundaries of novelty screening.

## Verify the mathematics

- [FiniteFixation.lean](FiniteFixation.lean): finite forward probabilities and certificate convergence.
- [FiniteEpigenetic.lean](FiniteEpigenetic.lean): explicit 81-state finite kernel and exact result.
- [DeterministicEpigenetic.lean](DeterministicEpigenetic.lean): reduced deterministic recurrence and strict finite-tail bound.
- [RankingReversal.lean](RankingReversal.lean): comparison of the two statements.
- [verification/finite-receipt.json](verification/finite-receipt.json): the checked finite components and hashes.
- [INDEPENDENT-MODEL-AUDIT.md](INDEPENDENT-MODEL-AUDIT.md), [DETERMINISTIC-INDEPENDENT-AUDIT.md](DETERMINISTIC-INDEPENDENT-AUDIT.md): independently implemented checks and source-correspondence review within the same agent team.

The current finite receipt covers 21 selected endpoints and permits only propext, Classical.choice and Quot.sound. Independent internal agent review is not external expert endorsement.

Lean verifies the explicit count and reduced-frequency models. Their derivation from the authors' phased life cycle is written and independently checked with exact arithmetic; it is not a separately formalized transport theorem. The written deterministic common-limit argument is likewise distinguished from the Lean finite-tail theorem.

## Use and scope

This is an exact test case for a published finite-population research direction. The source's pure-induction formula and the general fixation/certificate machinery are established theory. The matched comparison is a candidate contribution whose priority and publication relevance require assessment.

The result does not settle a universal effect of population size, establish an empirical speciation event, or prove that DNA determines species. It contains no cultural mechanism. Neutral-marker fixation is distinct from Alexander's organism-level ancestry predicates. The Wong whole-paper formalization remains a separate undertaking.

## Reproduction

The Lake project pins Lean 4.33.1 in `lean-toolchain` and Mathlib at commit `0df444a360eaa60ab8c11dca51a86af692955474` in `lakefile.lean`. From this directory, the portable project route is:

```sh
lake build
```

Lake resolves the declared dependency and builds all four Lean modules. A clean dependency fetch was not repeated for this frozen packet; network access may be needed when the pinned dependency is not already cached.

For a cached per-file replay after the Lake dependencies are available, run the modules sequentially in dependency order:

```powershell
./Check.ps1 -File FiniteFixation.lean
./Check.ps1 -File FiniteEpigenetic.lean
./Check.ps1 -File DeterministicEpigenetic.lean
./Check.ps1 -File RankingReversal.lean
```

`Check.ps1` accepts only those four module names. It defaults to `-PackagesPath $PSScriptRoot/.lake/packages`, `-LeanCommand lean`, and `-OutputDirectory $PSScriptRoot/replay`; the per-file build output and logs go under `replay/`, so the frozen verification receipts and logs are not overwritten. Pass those options explicitly to use a different local dependency cache, Lean executable, or replay directory. The cached route preserves the recorded compiler flags (`-j1 -M4096`) and searches each package's `.lake/build/lib/lean` in `LEAN_PATH`. Python checks use only the standard library. The linked notes distinguish reference computations from formal verification.
## Process recovery provenance

Three modules have directly observed terminal exit code zero. DeterministicEpigenetic emitted its complete clean 10-report log and fresh compiled object before its process handle was lost during a task interruption. Its original exit code was not retrieved. RankingReversal subsequently imported that object and exited zero. The combined receipt preserves this distinction and all four source hashes. Its status is PASS_WITH_RECOVERED_EXIT_EVIDENCE. The 21-endpoint finite receipt remains unchanged.

