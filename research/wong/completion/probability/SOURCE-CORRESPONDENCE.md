# Source correspondence: the 19-endpoint embedded count-chain result

**Source verdict: an appropriate partial formalization of Appendix B's
absorption claim.** The exact discrete count law and its almost-sure stopping
result are now supplied. The source's continuous-time and marked-ARG claim
remains broader. This is a source correspondence review, complementary to the
separately assigned adversarial statement review; it is not another compiler
run or an independent proof audit.

The reviewed source is Wong et al. (2024), *A general and efficient
representation of ancestral recombination graphs*,
[DOI 10.1093/genetics/iyae100](https://doi.org/10.1093/genetics/iyae100),
[Appendix B](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app2), printed
pp. 12–13. Primary XML SHA-256:
`2b77c349f39d2885b3e36d3bcab639a7ef3b9c6217263031aa4bc8f1c2a0d05e`.
The exact source paragraph is `/article/body[1]/sec[11]/p[5]`, section `app2`.
Its MathML was inspected directly rather than interpreting the flattened
binomial display as an ordinary fraction.

## Exact rate correspondence

| Primary source component | Formal counterpart | Interpretation |
|---|---|---|
| IM38: common-ancestor rate `choose(k, 2)` | General merger rate `a*k*(k-1)/2`, with `a>0` | The literal source scale is `a=1`. Each merger reduces the lineage count by one. |
| IM39: recombination rate `k*rho` | General splitting rate `b*k`, with `b>=0` | The literal source scale is `b=rho`. Each split increases the count by one. |
| Two possible next event types before stopping | `WongCountChain.transition`, `jumpKernel`, upward and downward singleton-mass theorems | For `k>=2`, the embedded probabilities are `lambda/(lambda+mu)` and `mu/(lambda+mu)`. These identify both outcomes of the actual constructed kernel. |
| A sample of `n` initial lineages | `pathLaw theta n` and `initial_lintegral` | This supplies the initial count distribution; it does not create labelled sample nodes in a graph. |
| Continue until one lineage remains | `one_absorbing`, `ae_eventually_one`, `ae_finite_jump_absorption` | The source's stopping convention is represented by a constant tail at count one. Repeated tail indices are not additional source events. |
| Finite-time arrival asserted from quadratic merger versus linear splitting | Explicit scalar potential, actual-kernel drift, and almost-sure finite jump-index absorption | This proves the embedded-chain part. Continuous waiting times and graph interpretation are not contained in the 19 endpoints. |
| Uniform lineage selection, pair selection and IM40 breakpoint `0<x<m`; record graph nodes and edges | Not represented in these three modules | A marked spatial construction and its count projection remain separate proof obligations. |

The algebraic normalization is `theta=2*b/a`, so the displayed source rates
specialize to `theta=2*rho`. This factor is visible in `normalizedRatio_value`,
`literal_up_kernel_mass` and `literal_down_kernel_mass`. The formalization does
not silently replace the source split rate with `k*rho/2` or the merger rate
with `k*(k-1)`.

## What can now be said

The source-bound result is: for the stopped embedded lineage-count chain
whose upward and downward probabilities are induced by the displayed literal
rates, every finite positive starting count reaches one after finitely many
jumps with probability one. The stronger exported normalized theorem states
that almost every trajectory is eventually constantly one. The literal-rate
endpoint assumes `a>0`, `b>=0` and starts at `n+2`; the general normalized
endpoints also cover the already absorbed initial count one.

The natural count zero is an explicit totalization, sent directly to one. It
has no interpretation as an initially empty biological sample. The separate
positive-state theorem ensures that zero is almost surely avoided from a
positive starting count. Stopping at one follows the source; continuing births
from one would be a different process.

The important progress beyond the old scalar certificate is that the
probability space is now constructed. `pathLaw` uses `Kernel.traj`; the
one-step expectation law is derived for that measure. The final absorption
endpoints have no drift, recurrence or absorption hypothesis. The scalar
potential is instantiated in the actual kernel by the bridge. The earlier
conditional drift theorem remains an intermediate statement, not the final
claimed source result.

This is attributed formalization of a known count-process property, with
explicit finite-potential proof infrastructure. The particular proof witness
is not being advertised as new mathematics. No new biological mechanism or
empirical applicability is established by these modules.

## What the result does not yet provide

1. **Continuous time.** The modules contain no exponential holding-time
   variables, no random event-time sums, and no continuous-time process.
   Connecting finite jump absorption to the source's finite physical time
   requires that additional construction and its laws. Continuous-time
   nonexplosion is therefore still an explicit coverage gap.
2. **Spatial ARG semantics.** There is no graph-valued stochastic process,
   uniform choice of lineage/pair/breakpoint, event labelling, or theorem that
   forgetting those marks produces this count law. The earlier deterministic
   finite interval-gARG results are not automatically a stochastic projection.
3. **Big/Little equivalence.** The Little ARG has segment retirement and
   different active-lineage dynamics. The result neither proves its absorption
   nor couples its sampled ancestry law to the Big ARG.
4. **Expected cost and rate conventions.** `sum_transient_le` gives a
   drift-based tail-probability sum bound; after instantiation it is useful
   input for expectation work. The exported endpoints do not identify an exact
   expected-event formula, prove the source's exponential asymptotic, or settle
   the rate-normalization concern in the ledger. A coarse finite potential is
   not a sharp asymptotic result.
5. **Literal event records and likelihood.** The modules do not recover
   event times or lineage groupings from a simplified gARG, construct the
   source's likelihood, or verify a simulator/exporter.

## Coverage disposition

The existing 52-family ledger should be updated only through a separate
admitted release of these 19 endpoints. Proposed changes:

- **B05 becomes partial**, with almost-sure finite jump-index absorption of
  the constructed count law checked. Holding times, the continuous-time
  process, nonexplosion and the spatial interpretation remain named gaps.
- **B04 becomes partial**, limited to the embedded count kernel and literal
  rate calibration. Event recording and an exponential-holding sampler remain
  open.
- **A01 and B06 remain open.** No Big/Little projection/equality-in-law or
  Little-ARG retirement result follows from this packet.
- **B07 and B08 retain source clarification required.** The factor `2*b/a`
  is checked algebra, not a resolution of the growth-rate statements.
- **B09 remains partial** with its existing timed-observation result. This
  discrete count law adds no continuous-time likelihood construction.

The deterministic 65-endpoint release stays frozen and separate. A future
combined library count would be 293 only if all 19 endpoints are registered
and a fresh combined audit verifies that exact inventory; no 293-endpoint
verification is claimed here.

## Evidence binding

`SOURCE-MANIFEST.json` records the exact 2+10+7 source and log inventories. The
lead matched every selected endpoint to the actual printed reports, which use
only `propext`, `Classical.choice` and `Quot.sound`. The warning counts are
2 scalar, 5 count-chain and 2 bridge warnings. The original worker handoff
reports compiler exit zero; this source review did not rerun Lean.

The source hashes are:

| Module | SHA-256 |
|---|---|
| `WongBigARGDrift.lean` | `167d448eb3e0c016e24a0590b2263f7685b244f21999b2b6303d105e09dfcb43` |
| `WongCountChain.lean` | `5f7629af4619220f77dd0c6344df4d3d096e3ca089e9f439c9cbf8808d6c59ae` |
| `WongBigARGAbsorption.lean` | `50b18cf23019c05c477c35ca38025d2516b662788d65e7c4cb6f98fecb3ff518` |

Independent statement review, public registration and exact hosted checks are
separate evidence states. Neither these local receipts nor this source review
complete the paper.