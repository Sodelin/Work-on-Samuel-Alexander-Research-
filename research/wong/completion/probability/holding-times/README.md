# From lineage jumps to elapsed time

**Status:** local Lean verification and independent internal statement review passed for 24 selected declarations. Fresh hosted admission is pending. This result adds a clock to the already checked stopped lineage-count process.

## What the theorem says

A jump chain records a sequence such as “two lineages, then three, then two, then one.” Its order alone does not say how much time passed. The new construction supplies the waiting times and proves their relationship to that sequence.

At a transient count $`k\ge 2`$, the total event rate is

```math
q_k=bk+\frac{a\,k(k-1)}{2},
\qquad a>0,\quad b\ge 0.
```

Take the previously constructed random count path and an independent sequence of unit-exponential random variables. Divide each innovation by the rate at the current count, up to the first visit to one lineage. This defines an actual joint probability law for the count history and its waiting times.

Under that law:

- Each finite collection of waiting times, conditional on a positive hitting count path, has the specified product of exponential survival probabilities.
- Integrating the conditional waiting-path law against the count-path law gives the joint observation probabilities.
- Every initial count of at least one reaches count one in finite physical time with probability one.
- Every wait before absorption is strictly positive, so successive actual event times strictly increase.
- Starting at one takes zero time; starting at two or more takes strictly positive, finite time, almost surely.

The definition assigns infinite absorption time to nonhitting paths. The theorem proves those paths have probability zero for the specified law. The zero-padded tail after absorption represents no further events.

## A concrete check

Set $`a=b=1`$ and start at two lineages. The total rate is three: the splitting rate is two and the merger rate is one. The selected Lean endpoints check the total rate and the upward jump probability of two thirds. The general survival theorem then gives a waiting-time survival probability of $`e^{-3t}`$ for nonnegative $`t`$ at that pre-absorption state.

The construction uses standard exponential clocks and product measures. Its contribution here is the checked connection to the particular previously proved count law. It is not presented as a new general theorem about exponential distributions.

## Source correspondence and remaining work

The Big ARG discussion in [Wong et al. (2024)](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/) specifies common-ancestor rate $`\binom{k}{2}`$ and recombination rate $`k\rho`$. The specialization $`a=1,b=\rho`$ matches those count rates. The [independent review](INDEPENDENT-REVIEW.json) records the exact local source XML hash and paragraph locator.

This packet does not construct a real-time state process with a proved Markov property, select marked lineages or breakpoints, or prove a spatial ARG projection. It supplies no exact expected-event formula, deterministic upper bound on absorption time, or full-paper completion claim. Those obligations remain in the [coverage ledger](../../COVERAGE.md).

## Evidence and reproduction

- [Canonical Lean source](../../../../../real/WongWaitingTimes.lean)
- [Original worker source](worker/WongWaitingTimes.lean)
- [Original local receipt](worker/verification/WongWaitingTimes-receipt.json)
- [Original final log](worker/verification/WongWaitingTimes-final.log)
- [Independent statement review](INDEPENDENT-REVIEW.json)
- [Reproduction instructions](REPRODUCE.md)
- [Publication and source hashes](PUBLICATION.json)

The original worker bytes are preserved. The canonical library copy is byte-identical to the original worker source and already uses LF line endings. Hosted CI rebuilds the library copy against Lean 4.33.1 and the pinned Mathlib revision.
