# Q12: what an unobserved branch does and does not tell us

**Status:** written mathematical derivation, checked by exact finite enumeration on small cases. Not Lean-verified. This is an elementary statistical testing result, not a claimed new solution of the paper's entire calibration problem.

## Source question

Abramsky et al., *Open questions about time and self-reference in living systems*, [DOI 10.1098/rsos.261059](https://doi.org/10.1098/rsos.261059), §7, published PDF p.24, asks how to calibrate evolutionary models when observed data cover far fewer histories than the models permit. In particular, an unseen outcome might be possible but unobserved, or structurally impossible.

The precise question considered here is: can finitely many observations perfectly distinguish a model in which a branch is impossible from one in which that branch is rare?

## Explicit restricted model

Observe n independent binary trials. A 1 records occurrence of a designated branch.

- Model M0 always produces 0.
- Model Me produces 1 with known probability e on each trial, independently, with 0 < e < 1.
- A decision procedure may be randomized. Its output is which of the two models to select.

This restriction is deliberate: independence, constant branch probability, known alternative probability and full observation of the branch are assumptions. Arbitrary path-dependent evolutionary models need different analysis.

Let q be the probability that all n observations are zero under Me:

```math
q=(1-e)^n.
```

Let a be the probability that the decision procedure selects Me after observing the all-zero sample. Define alpha as its error probability under M0 and beta as its error probability under Me. Then

```math
\alpha=a,\qquad \beta\ge q(1-a).
```

Therefore every such decision procedure satisfies

```math
\alpha+\beta\ge q,\qquad
\max(\alpha,\beta)\ge\frac{q}{1+q}.
```

For the second inequality, if a is at least q/(1+q), alpha has that lower bound; otherwise q(1-a) exceeds it. This argument also covers n=0, for which q=1.

Both bounds are sharp in their respective optimization problems:

- To minimize the sum of errors, select Me whenever any 1 occurs and select M0 on the all-zero sample. The sum is q, so the minimum equally weighted average error is q/2.
- To minimize the worst of the two errors, select Me whenever any 1 occurs, and on the all-zero sample select Me with probability q/(1+q). Both error probabilities then equal q/(1+q).

These are different decision criteria; one rule need not optimize both.

## Consequences and limits

For fixed positive e, increasing n reduces this bound to zero. The two models have different full observation laws and can be distinguished with arbitrarily small error as n grows; no finite n gives perfect certainty for 0 < e < 1. This example is **finite-sample uncertainty**, not structural non-identifiability.

For any fixed finite n, if arbitrarily small e is allowed, q approaches 1 and the minimax lower bound approaches 1/2. Thus a uniform, high-confidence decision between “impossible” and “arbitrarily rare” needs additional assumptions or evidence. No amount of formal verification of the decision procedure supplies missing observations.

A useful positive assumption is a known lower bound e_min on the probability of any branch considered possible. Under independent trials, zero occurrences in n trials then have probability at most

```math
(1-e_{\min})^n
```

when that branch is possible. This supports a statistical exclusion at a specified error level, rather than a certainty claim. Active interventions, better measurements, repeated independent systems, mechanistic restrictions or a prior distribution can also change the inference problem; their effects require their own models.

## Connection to the user's proposed framework

There are two separate losses:

1. **Observation/compression loss:** distinct mechanisms may produce the same observed law after information is discarded.
2. **Sampling uncertainty:** distinct observed laws may still produce the same finite dataset.

Q04 addresses one exact deterministic form of the first problem. The calculation here addresses a simple form of the second. Combining them without keeping this distinction would overstate an impossibility result.

## Reproduction

Run `python calibration_demo.py`. The script enumerates complete binary samples with rational probabilities, checks normalization, computes both optimal decision rules and exhausts deterministic rules for small n. It verifies the finite instances it enumerates; the general argument is the derivation above.
