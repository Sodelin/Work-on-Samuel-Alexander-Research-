# Independent stochastic-contract review

Status: independent contract and implemented-source review; no Lean was run by
this reviewer. The sections below preserve the original contract review and
the subsequent source reviews, with inspected hashes. This file owns no proof,
runner, ledger, public-route, or biological-source edits. It concerns the next
stochastic gate after the deterministic predictive-memory packet.

**Conclusion.** The proposed exact abstraction is defensible as actionwise
strong lumpability with an output decoder. It preserves joint finite histories
under controllers that use the declared retained history. Equality of all
fixed-action output trace laws is strictly weaker than this kernel condition.
The six-state example below proves that distinction without finite-data,
zero-probability, approximation, or infinite-state qualifications.

## General contract and proof targets

Let `X`, `R`, `A`, and `O` be types. Supply total transition kernels
`K : A -> X -> PMF X`, a retained-state map `q : X -> R`, an output
`p : X -> O`, and a decoder `d : R -> O` with

```text
output decoding:       p x = d (q x)                     for every x
kernel commutation:   (K a x).map q = Kbar a (q x)       for every a,x.
```

For **onto** `q`, the following exact criterion holds:

```text
(forall a x y, q x = q y -> (K a x).map q = (K a y).map q)
    iff
(exists unique Kbar : A -> R -> PMF R,
    forall a x, (K a x).map q = Kbar a (q x)).
```

Choose a representative of each fibre to construct `Kbar`; fibre constancy
makes the result independent of the choice. Surjectivity proves global
uniqueness. Without surjectivity, uniqueness is only guaranteed on `range q`;
values outside that image are unconstrained. The preservation theorem itself
does not require surjectivity if a commuting `Kbar` is already supplied.
Output decoding is a separate condition; for onto `q`, an output decoder
exists exactly when `p` is constant on its fibres.

State the path theorem for joint retained states **and actions**, including the
initial state. A convenient mathematical type is
`History_n(X) = X x (A x X)^n`. Let `Q_n` apply `q` to every state component and
leave all action components unchanged. For each step `n`, choose any policy

```text
pi_n : History_n(R) -> PMF A.
```

Generate the microscopic history from initial `mu : PMF X`: sample an action
from `pi_n(Q_n h)`, then the next state from `K a (last h)`, then append the
action and state to `h`. Generate the retained history with the same `pi_n`,
kernel `Kbar`, and initial law `mu.map q`. For every finite `n`, prove

```text
(microHistoryLaw n mu pi).map Q_n
    = retainedHistoryLaw n (mu.map q) pi.
```

Induct on the history length, using `map`/`bind` identities and the one-step
commutation equation. Mapping each retained state through `d` then gives the
joint output/action law. Controllers reading only output histories are the
special case `pi_n = rho_n o D_n`, where `D_n` maps every retained state through
`d`; remembered past actions can be included. Deterministic controllers are
Dirac-valued policies. This states a stronger result than preservation of an
endpoint distribution or separate one-time marginals.

The policy is a **conditional sampling rule on the declared history**. A
controller using an additional microscopic variable, hidden private state, or
noise correlated with the system is not covered merely by giving its
unconditional action distribution. Include its information and initial joint
law in the model, or prove that its conditional decisions factor through the
retained history. A fully observed MDP policy and an output-only policy have
different information interfaces.

The theorem is uniform over initial laws. Preservation only for one chosen
initial mixture can be weaker than fibre constancy; the necessity direction
for a universally commuting kernel is already tested by Dirac initial states.
No conditioning on positive-probability histories is needed for the basic
`PMF.bind` proof.

## Six-state strictness example

Use one total action and states `X = {s,t,u,b,c,v}`. All outputs are zero except
`p(v)=1`. Write `delta_x` for a point mass. The complete transition table is:

| State | Output | Next-state law |
|---|---:|---|
| `s` | 0 | `(delta_u + delta_b)/2` |
| `t` | 0 | `delta_c` |
| `u` | 0 | `delta_u` |
| `b` | 0 | `delta_v` |
| `c` | 0 | `(delta_u + delta_v)/2` |
| `v` | 1 | `delta_v` |

The rational rows sum to one. Define trace equivalence by equality, for every
finite horizon, of the **joint** output sequence starting with the current
output. From either `s` or `t`, this law is the equal mixture of the two
infinite patterns `000...` and `00111...`, truncated to the requested length.
Thus `s` and `t` have equal joint output trace laws for every action word, since
there is only one action. At horizons zero and one the two patterns coincide,
so the mixture is a single point mass; no exceptional base case is omitted.

A direct all-horizon proof uses the entire future trace distributions:
the law at `c` is half the law at `u` plus half the law at `b`. Prepending zero
to that equality gives equality of the laws at `t` and `s`, respectively.
This is an affine dependence among predictive laws, not equality of the
individual laws at `u`, `b`, and `c`.

The trace-equivalence classes are exactly

```text
S = {s,t}, U = {u}, B = {b}, C = {c}, V = {v}.
```

To verify that no other classes merge: `v` differs at the initial output;
the next-output probabilities of one at `b`, `c`, and each of `u,s,t` are
respectively `1`, `1/2`, and `0`; the time-two probability of one at `u` is
zero and at `s,t` is `1/2`. These observations distinguish every remaining
pair of classes. Let `q` map states to these five classes. It is onto and
admits the decoder that assigns one exactly to `V`. Nevertheless,

```text
(K s).map q = (delta_U + delta_B)/2
(K t).map q = delta_C.
```

The two measures assign class `C` probabilities zero and one. Since
`q(s)=q(t)=S`, no `Kbar` satisfies kernel commutation with this `q`. This is
strictness between output trace equivalence and an exact retained-state
quotient, using finite states, total actions, and rational probabilities.

Be precise about what is impossible: there is **no commuting quotient kernel**.
A separately chosen Markov realization on these five labels can reproduce
the output laws; for example, choosing the `S` transition to be `delta_C`
does so. It fails to reproduce the actual pushed state transition from `s`.
The result does not deny existence of a smaller output predictor or of
another state representation.

Independent bounded arithmetic check: an in-memory `BigInt` enumeration used
integer transition weights `1` for half-probability edges and `2` for
probability-one edges, with denominator `2^n` after `n` transitions. It checked
equal joint laws from `s,t` for `n=0,...,10`, and that length-three output laws
give exactly the five classes displayed above. For `n=2`, both laws put
numerator `2` over denominator `4` on each of `000` and `001`. This finite
check supports the construction; the preceding mixture proof supplies the
all-horizon argument. Neither has yet been independently Lean-checked here.

## Correlation and feedback boundaries

A fair bit held fixed and a fair bit alternated have the same Bernoulli-half
marginal at each time. Their consecutive-bit equality probabilities are one
and zero. This is why separate output marginals are insufficient for the
history theorem or a claim about memory.

Do not strengthen the strictness result into a claim that fixed-action
**joint** output trace equivalence fails under all feedback. In the same
causal total-kernel model, any output/history-only behavioral policy satisfies
the cylinder identity

```text
P_pi(o0,a0,...,a[n-1],on)
 = P_do(a0,...,a[n-1])(o0,...,on)
     * product_t pi_t(a[t] | o0,a0,...,o[t]).
```

Equal open-loop joint output laws therefore preserve such output-only policy
laws too. This identity uses multiplication, not division by a history's
probability. It does not give a commuting state quotient. Nor does it cover a
policy with additional access to hidden microscopic states. Treat the identity
as a written observation unless a corresponding theorem is implemented.

The present deterministic decoder also avoids a further stochastic observation
issue. If state transition and noisy measurement share randomness, preserve
their joint kernel `J : A -> X -> PMF (X x O)` through
`(q x id)_* J_a(x) = Jbar_a(q x)`. Separate transition and emission marginals
do not determine their coupling. Factored transition/emission kernels require
the asserted conditional independence. This is a later observation-model gate,
not a missing hypothesis for the current deterministic `p=d o q` theorem.

## Existing mathematics and library reuse

[Givan, Dean and Greig (2003)](https://cs.brown.edu/people/tdean/publications/archive/GivanetalAIJ-03.pdf)
is directly relevant prior work: section 3.1 (author PDF pp. 9-11) distinguishes
action-sequence distributions from state-aware policies; section 3.3
(pp. 12-14), especially Theorems 5 and 7, gives stochastic bisimulation and
quotient transfer; section 4 develops refinement. Their reward-preservation
condition must accompany any use of their policy-value conclusions. Our
output-decoding/kernel result is an instance of established abstraction
mathematics, not a new discovery of lumpability. Their state-aware policy
counterexample should not be cited as refuting output-only feedback
preservation.

The repository pins Mathlib commit
`0df444a360eaa60ab8c11dca51a86af692955474` in `real/lakefile.lean` and its
manifest. The exact pinned primary source was inspected:

- [PMF Constructions](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Probability/ProbabilityMassFunction/Constructions.lean):
  `map_comp`, `pure_map`, `map_bind`, `bind_map`, `ofFintype`, and
  `map_ofFintype` cover the main algebra and finite example construction.
- [PMF Monad](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Probability/ProbabilityMassFunction/Monad.lean):
  `bind_bind`, `pure_bind`, and `bind_pure` supply the sequencing laws.
- [PMF Basic](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Probability/ProbabilityMassFunction/Basic.lean):
  `support_countable` makes the distributional scope explicit. Arbitrary
  carrier types do not turn PMF into a model of non-atomic continuous noise.

Finite state spaces are useful for the example and executable refinement, but
are unnecessary for the general finite-history PMF induction. Constructing
infinite path measures, handling non-atomic distributions, and measurable
quotient selection belong to additional measure-theoretic theorems.

## Geometry and source-faithfulness gates

No metric or topology is needed for the exact algebra above. Conversely, it
establishes no distance, continuity, physical geometry, smoothness, or robust
approximation result. Calling the quotient a geometry requires specifying the
chosen structure and its relationship to measurement/intervention. A distance
built from total variation of output trace laws would vanish on `s,t` in the
example; that would describe trace behavior, not strong bisimulation. A
Wasserstein claim additionally needs a ground metric and its relevant
measurability/integrability assumptions. Giving a finite set its discrete
topology by default does not explain biological spatial organization.

For the [Royal Society paper](https://doi.org/10.1098/rsos.261059), this extends
the ledger's controlled-projection subproblem toward noisy transition models.
It is relevant to the projection discussion in section 4.2 (p. 11) and the
path-dependent-variable discussion in section 7 (p. 23). It still fixes the
state, action, output, and kernel semantics. It does not solve the authors'
full questions about emergent time, agent change, self-reference, or the
creation of new representational variables. A fitted stochastic model, an
exact mathematical abstraction of that model, and an established biological
mechanism remain separate evidence levels.

At the contract-review stage, the acceptance gates were: mechanize the fibre criterion and
uniqueness; preserve the joint finite retained/output history under the stated
controller interface and pushed initial law; mechanize the all-horizon
strictness witness and its failure of commutation; attach a fresh compiler and
axiom receipt; and keep all claimed model transfers conditional on a proved
kernel/output/initial-law correspondence. A stochastic coarsest-bisimulation
theorem, a noisy observation interface, approximate distances, and a
biological model correspondence are separate extensions, not consequences
already delivered by this contract.

## Implemented core: independent statement review

The reviewer inspected `StochasticAbstraction.lean`, 225 lines, at SHA-256
`05e112c7395d968c65d289f3a09c26f933eab900fca45705e03bab1a84a1cec6`.
The coordinator reports successful Lean checking. This pass read the actual
definitions, hypotheses and proofs; it did not execute Lean or independently
verify a compiler receipt. `StochasticExamples.lean` was explicitly deferred
until the coordinator declares that separate file ready.

**No mathematical blocker or vacuous preservation contract was found.** The
core implements the following reviewed claims:

| Declarations | What the actual statement establishes |
|---|---|
| `exact_iff`, `exact_unique` | Existence from actionwise fibre constancy and global uniqueness for onto `q`. The two declarations together establish the existence-and-uniqueness contract. |
| `exact_iff_all_initial_laws` | One-step commutation for every initial PMF is equivalent to pointwise exactness; the reverse direction explicitly uses Dirac initial laws. |
| `runLaw_preserves`, `runLaw_initial` | Fixed finite words preserve the retained endpoint law, both from a fixed state and from the pushed initial PMF. |
| `experiment_preserves`, `experimentLaw_preserves` | Joint action/state histories, including the initial state and final state, commute with the retained-history map under factored conditional policies. |
| `observationPolicy_factors`, `observed_experiment_law` | Every common output/action-history policy has the same complete observed transcript law, using the decoder and matching initial pushforward. |
| `observed_statistic_preserves` | Any deterministic statistic of that observed transcript has the same distribution. |
| `deterministic_instance` | The earlier deterministic commutation condition embeds by point masses. |
| `joint_sensor_exact`, `joint_sensor_observed_law` | An arbitrary commuting joint next-state/measurement law yields exact augmented-state and observed-transcript preservation within the declared latent-state Markov semantics. |

The record representation `List (X x A) x X` contains the past state/action
pairs and current state. Each recursive step appends the current state and
chosen action before proceeding to the next state, so no state or action is
discarded. The zero-step law retains the supplied record. Starting from
`experimentLaw` with an empty past produces `n` actions and `n+1` state/output
values after `n` steps. This confirms that the main result is a joint-law
statement, not merely an endpoint or a collection of marginals.

The policy hypothesis is global:

```text
choose past x = chooseR (mapHistory q past) (q x)
```

It covers all histories, including those outside the chosen process's support.
That is stronger than a support-restricted premise, but is nonvacuous:
`observationPolicy_factors` constructs it from any common observation-history
policy and valid decoder. Policies can use past actions and the length of the
record, hence the statement includes randomized, history-dependent and
time-dependent decisions in that interface.

The meaning of controller randomness is fixed by the generative definition:
given microscopic history `h` ending at `x`, the joint next-step mass is
`choose(h)(a) * K(a,x)(y)`. Thus `choose` is the conditional action law on that
history, and `K` is the conditional next-state law after that action; the
transition draw has no further dependence on controller information omitted
from `X`. Equality of unconditional action frequencies would not satisfy this
contract. A private seed correlated with future transition noise or latent
state must be included or shown to obey these conditional laws. The theorem
does not independently establish such assumptions for data or interventions.

The sensor extension is genuinely joint: `J a x : PMF (X x O)` is arbitrary,
so it need not factor into a transition PMF and an independent emission PMF.
Its hypothesis pushes the complete pair `(q(nextX),nextO)`, and the initial
`mu : PMF (X x O)` may also correlate state and measurement. The equality of
joint laws, rather than separate marginals, is used by the proof.

The sensor boundary is equally explicit in the code: `sensorStep J a s =
J a s.1` ignores the previous measured coordinate. Conditional on the current
latent state and selected action, neither that coordinate nor earlier
measurements otherwise affect the next joint law. The controller can still
respond to those measurements through its action. A persistent sensor state,
time-varying drift or direct dependence on previous readings must be included
in `X`, or handled by a more general augmented-state kernel. Adding this
sentence to the `sensorStep` comment was recommended for publication clarity;
it is not a missing hypothesis or defect in the present theorem.

The identity map with identical kernels provides an immediate nonempty class
of instances; observation-policy factorization and the deterministic instance
provide further explicit witnesses. Onto hypotheses occur only in existence
and uniqueness, not in path preservation. No conclusion about minimality,
non-atomic noise, a physical geometry or a biological mechanism appears in
these core theorem statements.

## Final examples and public-explanation review

This pass inspected the completed example source and `STOCHASTIC.md`, and
verified the revised latent-state Markov comment in the core source. The
inspected snapshot hashes are:

| File | SHA-256 |
|---|---|
| `StochasticAbstraction.lean` | `943a395e85d3df0fbd8e4570fa205f3a2748cfdaa744ce1add9380b8d41453ce` |
| `StochasticExamples.lean` | `78c2f7ea2a59e2d3f3446b22df575353e527d067117863c9a0b3568f38ac1f2c` |
| `STOCHASTIC.md` | `03ef9a5b80afe39139ac9ee8ad25978ff5242001572b3fa230a5eafe783a2a08` |

The coordinator reported that the all-horizon/profile examples passed Lean;
the newly added `no_trace_based_test_separates` declaration was replaying when
this review was requested. This is a statement review, not an independent
compilation claim. The full fresh packet receipt and hosted CI remain separate
verification gates, including the public page's reference to checked bytes.

**No unresolved mathematical or public-scope blocker was found.**

`coin` is the uniform distribution on `Bool`, so the displayed mixtures are
fair. `c_is_mixture` states equality of complete trace PMFs at every horizon,
not equality of means or only the next output. Its zero case accounts for the
coincident current outputs; its successor case identifies both branch laws
directly. `same_all_traces` then proves equality from `s,t` for every horizon,
including the initial output and every output after the specified transitions.

`profile` is the full horizon-indexed function of trace distributions.
`same_profile` identifies the profiles at `s,t`. The separate one-transition
support witnesses prove `c_profile_ne_u` and `c_profile_ne_b`.
`profile_pushes_differ` then uses positive support of the profile of `c` from
`t` and its absence from both successors of `s`. Consequently,
`no_commuting_profile_kernel` excludes every kernel satisfying the exact
pushforward equation for that profile map. The proof does not require onto
profiles or an enumeration of all trace-equivalence classes. The earlier
five-class calculation is a mathematical description of the example, not an
extra class-enumeration theorem silently attributed to this implementation.

The public explanation states the right obstruction: no profile kernel that
commutes with the actual state transitions. It explicitly allows another
Markov realization of the same output laws. Its observation-history feedback
caveat is also correct; the one-action example does not demonstrate a failure
of an output-only adaptive-control equivalence theorem.

`no_trace_based_test_separates` applies an arbitrary kernel
`test : List Bool -> PMF D` to an already recorded finite trace. It establishes
equality of the randomized decision laws for the two starts. It does not add
new measurements or interventions during the experiment, nor identify a
biological mechanism. The source comment and public wording respect this
postprocessing scope.

`matching_marginals_different_joint` proves both marginal equalities and
inequality of the pair laws. The `agrees` statistic has a point-mass-true law
for copied bits and a point-mass-false law for complemented bits, establishing
the probability-one versus probability-zero distinction in the public page.
The page correctly presents a joint-distribution counterexample, without
claiming that this declaration formalizes an entire repeated-bit process.

The midpoint language has a precise algebraic meaning here: under their
probability coordinates, the distributions and profiles have the displayed
pointwise convex-mixture relation. That does not require a metric or topology.
It licenses the page's affine-dependence observation, while establishing no
distance, approximation bound or physical tissue geometry. Those additional
claims remain explicitly gated.

The requested sensor comment is resolved in the inspected core source: the
next joint draw is stated to be Markov in latent `X`, and persistent sensor
memory or drift must be included there. The public page preserves this
restriction and the conditional-controller-randomness restriction. It also
keeps PMF's countable-support scope, the fixed model semantics, the unfinished
Wong stochastic correspondence, and the separation of mathematical examples,
fitted predictions and biological mechanisms explicit.

## Reserved approximate-kernel gate: UNMECHANIZED review

The appended proposal in `STOCHASTIC.md` was inspected at SHA-256
`28eac1bbef460643255680ba69b81ecd4a5c183f29eaceae7d408072477c31cb`.
**This is a reviewed mathematical target, not a Lean theorem or a completed
verification gate.** No proof source was changed or executed in this pass.

With finite base types, identical decoded outputs and factored conditional
history policies, assume `0 <= delta,epsilon <= 1`,
`TV(mu.map q,nu) <= delta`, and
`TV((K a x).map q,L a (q x)) <= epsilon` for every `a,x`. The proposed bound

```text
TV(pushed microscopic joint transcript, reduced joint transcript)
  <= 1 - (1-delta)*(1-epsilon)^n
  <= min(1, delta+n*epsilon)
```

survives this falsification review. Couple the initial fine/retained states so
their retained values agree with probability at least `1-delta`. While entire
retained histories agree, policy factorization permits the same action in
both processes. A maximal coupling of the next retained values then fails
with probability at most `epsilon`. Induction bounds the probability of no
disagreement through `n` transitions below by
`(1-delta)*(1-epsilon)^n`; the coupling inequality gives the first bound.
The second follows from the elementary product/union bound and probability
being at most one. Independence between successive coupling failures is not
required. Mapping retained states through the common decoder yields the same
TV bound for decoded-output/action transcript laws by data processing.

The coupling construction must retain the correct microscopic marginals.
Lift each coupling of `q_*K(a,x)` and `L(a,q(x))` using the conditional
microscopic law inside each positive-mass `q` fibre, or directly construct a
fine-state/retained-state coupling. Choosing an arbitrary representative of
the sampled fibre would generally change the microscopic law. Zero-mass
fibres require no conditioning contribution. The analogous lift applies to
the initial laws. These finite-space constructions are proof obligations,
not hypotheses silently discharged by the exact-kernel theorem.

A fully specified sharpness witness avoids an otherwise ambiguous unused
transition row. Let `X=R={good,bad}`, use one action and identity encoding and
output, and set

```text
mu = point(good)
nu = (1-delta)*point(good) + delta*point(bad)

K(good) = point(good)       K(bad) = point(bad)
L(good) = (1-epsilon)*point(good) + epsilon*point(bad)
L(bad) = point(bad).
```

The microscopic process from `mu` stays good. The initial TV is exactly
`delta`; the kernel TV is `epsilon` at good and zero at bad. The reduced
probability of the all-good transcript is exactly
`(1-delta)*(1-epsilon)^n`. Since the microscopic transcript law is a point
mass on that transcript, its TV from the reduced law is the proposed first
bound exactly. This includes `n=0` and parameter endpoints, with the usual
natural-power convention for exponent zero. This supplies a written sharpness
argument for the universal finite-horizon bound; machine verification remains
open.

Interpreting "microscopic always good" instead as `K(x)=point(good)` for
every state would give kernel TV one at bad and violate the uniform premise
when `epsilon<1`. The explicit identity microscopic kernel above is the
required clarification, even though its bad state is initially unreachable.

There is one representation detail for the future Lean implementation: finite
`X,A` do not make the existing carrier `List (X x A) x X` finite. Either use a
fixed-length subtype or `Fin`-indexed transcript, with the length/support
invariant proved, or define the TV calculation for PMFs/finite-support laws.
The finite-horizon distribution has finite support; this does not by itself
supply a `Fintype` instance for all lists. This is an implementation gate,
not a mathematical counterexample.

The coupling construction, transcript support/representation, data processing,
both inequalities and the attainment witness all remain **UNMECHANIZED** in
this review. The fresh replay of the already implemented exact results does
not certify this new approximation target, and fitted error estimates do not
establish its uniform transition-error premise.
