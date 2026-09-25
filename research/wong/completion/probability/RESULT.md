# Why the stopped lineage-count chain eventually reaches one

Wong et al.'s Appendix B describes a competition between recombination, which
adds a lineage, and a merger, which removes one. Splitting grows linearly with
the number of lineages; merging grows quadratically. The new formal result
shows that the corresponding **discrete jump chain reaches one lineage with
probability one**, for every finite positive starting count and every finite
nonnegative splitting parameter.

The statement concerns the random number of jumps before stopping. It does
not yet construct the random time between events or the full spatial ARG.

## A small example

Set both rate scales to one. Before the stopping state, the rates are:

| Current lineages | Split rate | Merger rate | Probability that the next jump splits |
|---|---|---|---|
| 2 | 2 | 1 | 2/3 |
| 3 | 3 | 3 | 1/2 |
| 4 | 4 | 6 | 2/5 |

Thus the count need not fall on every step; from two lineages, an increase is
actually more likely than a decrease. The theorem still guarantees eventual
absorption almost surely. It permits arbitrarily long excursions and does not
provide a fixed number of steps that bounds every trajectory.

## Exact result and assumptions

The source rates are represented as `lambda(k)=b*k` and
`mu(k)=a*k*(k-1)/2`, with `a>0` and `b>=0`. The embedded upward probability is
`theta/(theta+k-1)`, with `theta=2*b/a`; the other possible jump goes down by
one. Count one is absorbing because the source process stops there.

The Lean development constructs a probability measure on infinite count
trajectories and proves that almost every trajectory is eventually constantly
one. Its final theorem supplies the finite drift witness internally; it does
not assume absorption or recurrence. The case `b=0` is included. Natural count
zero is only a disclosed totalization and is almost surely avoided from a
positive start.

The rate identities match the literal formulas in
[Wong et al. (2024), Appendix B](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app2).
The source's `choose(k,2)` and `k*rho` convention therefore corresponds to
`theta=2*rho`. That factor is retained explicitly when discussing later
expected-event calculations.

## Verification and remaining work

The packet has 19 selected endpoints: two scalar drift lemmas, ten actual
kernel/path-law endpoints, and seven bridge endpoints. The worker's pinned
Lean 4.33.1 runs passed; the exact source/log inventory contains only the
permitted standard axioms. The independent statement review returned
**PASS WITH SCOPED LIMITS**. No fresh combined library audit or hosted check
of these 19 endpoints is claimed by this review packet.

The remaining steps are to construct the continuous holding-time law, connect
it to the count paths, and verify the relationship to an ARG carrying lineage
identities and genomic marks. Little ARG dynamics, Big/Little equality in law,
exact expected-event formulas and source asymptotics remain separate. This is
a formalization of a known count-process property, not a new biological claim.

The exact evidence is in [SOURCE-MANIFEST.json](SOURCE-MANIFEST.json), the
[primary-source comparison](SOURCE-CORRESPONDENCE.md), and the
[independent review](ADVERSARIAL-REVIEW.md). The
[statement-first brief](PROBABILITY-STATEMENT-BRIEF.md) records the scope and
counterexample challenges set before the review.