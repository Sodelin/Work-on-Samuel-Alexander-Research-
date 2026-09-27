# Exact stochastic state reduction and its predictive limit

This is the next mathematical gate after [RESULTS.md](RESULTS.md), continuing
Q04 and Q07 of the [canonical ledger](../problem-ledger.json). It addresses a
precise part of the Royal Society paper's projection question (§4.2, p.11) and
its discussion of path-dependent internal variables (§7, p.23). The state,
interventions, observation interface and causal transition semantics are
fixed assumptions. None of the authors' full questions is declared solved.

The proof sources are [StochasticAbstraction.lean](StochasticAbstraction.lean)
and [StochasticExamples.lean](StochasticExamples.lean). Their exact checked
bytes, compiler results and axiom reports are in the
[current receipt](verification/PROOF-RECEIPT.json). The
[independent review](STOCHASTIC-SCOPE-REVIEW.md) audits statement strength and
prior mathematics separately from compilation.

## The necessary and sufficient condition

Choose state types `X,R`, interventions `A`, an encoding `q : X → R`, and
controlled transition laws `K : A → X → PMF X`. Mathlib's `PMF` allows arbitrary
carrier types but only countably supported distributions. This is not a
theorem for arbitrary continuous probability kernels.

For an **onto** encoding, an exact reduced kernel exists precisely when
states with the same code have the same pushed next-state law, for every
intervention. If it exists, it is unique on `R`:

```math
\begin{aligned}
q(x)=q(y)&\ \Longrightarrow\ q_*K_a(x)=q_*K_a(y)\quad\text{for all }a,x,y,\\
q_*K_a(x)&=\overline K_a(q(x)).
\end{aligned}
```

`exact_iff` proves existence and necessity; `exact_unique` proves uniqueness.
The representative construction uses classical choice, so it is not an
executable reduction algorithm for arbitrary types. Once a commuting kernel
is supplied, preservation needs no surjectivity. Without surjectivity, global
uniqueness outside the image is not asserted. `exact_iff_all_initial_laws`
also proves necessity by testing point-mass initial laws; success for one
selected initial mixture is not substituted for this uniform contract.

Supply a visible output `p : X → O` and a decoder `d : R → O` satisfying
`d(q(x))=p(x)`. Begin the reduced process with `μ.map q`, where `μ` is the
actual microscopic initial law. These are separate hypotheses.

## What is preserved, including adaptive intervention

`experiment` records every preceding `(state, action)` pair and the final
state. A policy chooses its next action according to a PMF conditional on
that complete recorded history. It may randomize, remember past actions,
and change its choice after earlier measurements.

| Declaration | Exact conclusion |
|---|---|
| `runLaw_preserves`, `runLaw_initial` | Every finite fixed action word preserves the pushed endpoint law, from a state or initial distribution. |
| `experiment_preserves`, `experimentLaw_preserves` | The complete finite joint retained-state/action law is preserved if the actual policy factors through retained history and the current retained state. |
| `observed_experiment_law` | A common observation/action-history policy gives the same complete joint observed transcript law in both models. |
| `observed_statistic_preserves` | Every declared statistic of that transcript has the same distribution. |
| `deterministic_instance` | The earlier commutation equation supplies this stochastic contract through point-mass transitions. |

These statements hold at **every finite horizon**; no infinite-path measure
theorem is claimed. Policies are conditional sampling rules: the generative
step samples the action from the declared history and then the next state
from `K a x`. Equal unconditional action frequencies are insufficient.
Additional controller information or noise correlated with the system must
enter the joint state or satisfy the conditional factorization. Factorization
is required on all declared histories, including unreachable ones.

## Noisy observations require a joint contract

Let `J a x : PMF (X × O)` produce the next latent state and its measurement
together. No independence between those two draws is assumed. Retain
`(q(x),o)` and require the pushforward of **this joint law** to equal
`Jbar a (q(x))`. `joint_sensor_exact` and `joint_sensor_observed_law` then
preserve the full finite measurement/action transcript, including a possibly
correlated initial state/measurement law.

This interface is Markov in `X`: previous measurements affect the next draw
through the chosen action. Persistent sensor memory, drift, or environmental
history must be represented in `X` to use this contract.

Why not just match two marginals? The Lean counterexample compares a fair
bit copied twice with a fair bit paired with its complement. Both component
marginals agree. Equality of the two components has probability one in the
first model and zero in the second. `matching_marginals_different_joint`
checks that the joint laws differ. This is invented mathematics, not sensor
data.

## All future output predictions still need not give an exact state quotient

Here is a six-state, one-action counterexample. All unmarked probabilities
are one; the two branches in a mixture each have probability one half.

| State | Output | Next-state law |
|---|---:|---|
| `s` | 0 | mixture of `u,b` |
| `t` | 0 | `c` |
| `u` | 0 | `u` |
| `b` | 0 | `v` |
| `c` | 0 | mixture of `u,v` |
| `v` | 1 | `v` |

The **complete joint output trace** from either `s` or `t` is the equal
mixture of the patterns `000…` and `00111…`, truncated to the chosen horizon.
`same_all_traces` proves equality for every finite horizon. The proof includes
the zero and one-transition cases, where the patterns coincide. The corollary
`no_trace_based_test_separates` covers every randomized decision based only
on such a trace, not just its mean or a chosen summary statistic.

Define a state's predictive profile as its whole function from horizons to
joint output distributions. `s` and `t` have equal profiles. Yet the next
profile from `t` is certainly the profile of `c`, whereas the next profile
from `s` is that of `u` or `b`, each distinct from `c`. The pushed next-profile
laws therefore disagree. `no_commuting_profile_kernel` proves that there is
**no kernel on these profiles that commutes with the actual transitions**.
The proof uses the complete profile itself, without assuming a finite
enumeration discovered all its equivalence classes.

This does not rule out a different Markov realization of the output laws.
Nor does it prove failure under observation-history-only feedback: the
counterexample has one action. In a causal controlled model, equality of all
fixed-action **joint** output laws can preserve output-history policies even
when a commuting state quotient is unavailable. Controllers reading hidden
states have a different information interface.

## The geometry and biological relevance

There is an exact geometric feature here: at every horizon, `c`'s predictive
distribution is the midpoint of those of `u` and `b`. `c_is_mixture` proves
this affine relation for all horizons. Distinct state profiles can be
linearly dependent. A model can therefore represent a mixture of fixed
response programs and an internal random transition by the same observable
response law. No test of those admitted traces identifies which mechanism
generated them.

This is geometry of **predictions**, not a proved geometry of tissue or
morphogenesis. A biological application must name response coordinates and
interventions; a distance or approximation claim additionally needs an
explicit metric. A concrete next mathematical target is a total-variation
bound for approximate joint-kernel preservation under the same controller
interface, including accumulation with horizon. It must be proved before a
nearby response profile is treated as a reliable approximation.

The paired [Stentor evidence contract](STENTOR-EVIDENCE.md) asks which assigned
histories, common probe and cell/lineage records could reject a declared
history-insensitive response model. It preserves the distinction between a
mathematical example, a fitted prediction and a measured biological mechanism.
Neither the exact kernel hypothesis nor a biological carrier of memory has
been inferred from that study's data.

## Prior mathematics and transfer limits

The fibre criterion is established strong-lumpability/bisimulation
mathematics. See [Givan, Dean and Greig (2003), §§3.1, 3.3 and 4](https://cs.brown.edu/people/tdean/publications/archive/GivanetalAIJ-03.pdf).
Their policy comparisons depend on controller information; reward and value
transfer also require a reward-preservation contract. No novelty claim is
made for this standard theory or the elementary examples. The implementation
reuses Mathlib's `PMF.map`, `bind`, uniform finite distribution, and their
algebraic laws rather than reimplementing probability.

The existing [ancestry mapping](RESULTS.md) remains an actual proved transfer
for destructive restrictions of fixed-locus relations. This stochastic packet
does **not** establish a new mapping from Wong's marked ARG generator: its
real-valued clocks/cuts use more general measures, and kernel, observation,
initial-law and controller correspondences remain unproved. An analogy to
biological individuality likewise remains an analogy.

## Exact statement reserved for the next mathematical gate

**Proposed theorem, not yet mechanized in this packet.** Start with finite
types, the same output decoder and history-policy factorization as above,
initial laws `μ,ν`, and numbers `δ,ε` in `[0,1]`. Define total variation on a
finite type as half the sum of absolute differences of probability masses.
For the existing list-valued transcript, prove support at the fixed length
and use the finite fixed-length subtype, or extend the definition to
finite-support PMFs on that carrier; the list type itself is not finite.
Require `TV(μ.map q,ν) ≤ δ` and, uniformly in every intervention and microscopic
state, `TV((K a x).map q,L a (q x)) ≤ ε`. The target is

```math
\mathrm{TV}(\text{pushed microscopic transcript law},
                  \text{reduced transcript law})
\le 1-(1-\delta)(1-\varepsilon)^n
\le \min\{1,\delta+n\varepsilon\}.
```

The proposed proof couples the initial states and each transition while the
retained histories still agree; the policy then permits identical actions.
For sharpness use `X=R={good,bad}`, one action and identity encoding/output.
The microscopic kernel is the identity at **both** states, with initial law
concentrated at good. The reduced kernel sends good to bad with probability
`ε` and makes bad absorbing; its initial bad-state probability is `δ`.
The uniform kernel mismatch is `ε` at good and zero at bad. The transcript
differs exactly on an initial or later escape. Prove the coupling
construction, bound and attainment together before
marking this gate checked. A local fitted error estimate is not a uniform
kernel bound, and finite sampling would need its own confidence statement.
