# What would demonstrate a retained biological state?

The formal quotient tells an analyst which distinctions an exact model must
retain for specified interventions. It does not identify a molecule, prove
that an organism uses an internal representation, or supply unobserved
counterfactual data. Here “same visible state” always means equality under a
declared measurement map, not equality of the complete physical state.

## Three different evidence claims

| Evidence class | Present example | Supported conclusion |
|---|---|---|
| Mathematical construction | The prime/wait/probe/reset model, with a parity memory and an irrelevant bit | A precise state distinction is necessary and sufficient under the stipulated transition rules. |
| Fitted prediction | A declared model for measured next-response probabilities, assessed on held-out cells/dates and reported with uncertainty | Relative predictive performance for that dataset and model class; it does not identify a storage pathway. |
| Experimentally supported mechanism | A candidate physiological variable is measured and manipulated, with response, timing and pathway controls | Evidence for a causal contribution under those conditions, stronger than a successful fit but still distinct from exact model correspondence. |

No biological data fit or new biological experiment was run in this
continuation. The examples below use invented probabilities. They do not
reproduce or validate the separate Stentor data-analysis track.

## What a discriminating observation must establish

Declare the output, intervention set, horizon, experimental unit, and measured
context first. If two admissible states share the current readout but differ
under a common probe, that readout is insufficient for exact prediction. A
required distinction could be acquired intracellular state, permanent cell
type, environment, unobserved clock, or an unmeasured part of the controller.
The formal result alone cannot locate it.

For noisy systems the target is equality of **interventional response laws**,
not equality of individual responses. A single differing binary response is
not an inequality witness between two unknown probability laws. Nor does a
finite fitted-model advantage prove exact biological insufficiency: model
classes, regularization, missing interactions, sampling uncertainty and
selection can create an advantage.

`HistoryObservation.stable_type_matched_history_null` specifies one exact
counterfactual null: permanent type plus an external clock, with output a
function of those variables only. Equal-length histories on the same unit
then have identical outputs. This is a deterministic implication, not a
statistical rejection procedure.

A stochastic empirical null can instead be stated explicitly as

```math
\mathcal L(Y\mid\mathrm{do}(H=h),\mathrm{do}(P=a),\Theta=\theta,C=c)
=K_{\theta,c,a}\qquad\text{for every admitted }h.
```

With a common type/context distribution independent of assigned history and
the same sampling/measurement rule, the null gives equal **marginal** probe
laws across history assignments by mixing the same kernels. This mixing
argument is written here; it has not been mechanized as a measure-theoretic
causal theorem. A reproducible intervention effect challenges that null or
its design assumptions. It does not uniquely determine its replacement.

## Two exact counterexamples that prevent overinterpretation

**Predictive order without response-induced learning.** Two permanent types
have different, prespecified time profiles, with independent responses
conditional on type. Earlier outcomes help identify type. Two six-response
histories have equal count and current response, yet their next-response
probabilities are `7/10` and `3/10`. Neither type changes in response to its
history. The checked rational enumeration uses invented probabilities,
not Stentor measurements.

**Selection after randomization.** Let history assignment `H` and permanent
type `Theta` be independent fair bits. Define visible state `V=H xor Theta`
and later outcome `Y=Theta`. For each fixed type, changing history never changes
the outcome. Both randomized groups have response probability `1/2`.
Nevertheless, among records with `V=0`, the response equals history perfectly:
the probabilities are zero and one. Each history/selection event has mass
`1/4`. Selecting an equal post-history visible state has selected different
types. The two structural identities are in Lean; the four-row probability
table is checked with exact rational arithmetic.

These examples are in [check_examples.py](check_examples.py) and
[EXACT-EXAMPLES.json](verification/EXACT-EXAMPLES.json). They disprove inference
rules, not the biological existence of memory.

## A concrete connection to Levin's biological questions

In [Durant et al. (2017)](https://pmc.ncbi.nlm.nih.gov/articles/PMC5443973/),
morphologically normal, previously perturbed planarians could reveal a different
regenerative outcome on recutting in water. The authors combined physiological
measurement with interventions that changed later regenerative outcomes.
This is experimental support for a bioelectric contribution, not an
instantiation of our Boolean model. The study's stochastic outcomes and
limited-depth voltage reporter require a stochastic observation contract;
the exact minimal physiological state remains unestablished here.

The [Stentor reviewed preprint, version 1](https://doi.org/10.7554/eLife.112314.1)
reports repeated single-cell responses across stimulation and recovery
protocols and fits latent response curves. It provides a useful setting for
comparing response level, history and learning rate. Behavioral and fitted
evidence should remain separate from identifying the molecular storage
substrate. This is a distinct study and distinct authorship from the planarian
work.

The formal bridge suggests a **model-discrimination design**, not a ready
biological protocol: track unit/fragment identity; assign histories before
selection; hold probe and elapsed-time context fixed; record all eligible
outcomes and censoring; and measure candidate state before the probe. Repeated
within-unit observations and time-matched controls constrain stable-type
accounts, while carryover and time trends remain explicit assumptions. A
candidate mechanism then needs interventions that predictably erase, alter or
restore the retained distinction, with controls for direct probe effects and
general responsiveness. Quantifying a complete physiological state or
identifying a mechanism is a remaining experimental gate.

## Exact next formal contract

Select one finite-state stochastic model before generalizing further. Specify
state `X`, actions `A`, measurements `p`, and kernels `K_a(x)` with a declared
time step. For a proposed retained state `q`, require output decoding and
actionwise pushforward equality `q_* K_a(x) = Kbar_a(q(x))`, including the
initial law. Prove finite-word response-law preservation, and then a converse
or counterexample appropriate to the chosen notion of stochastic equivalence.
Deterministic future equivalence must not silently be substituted for
probabilistic bisimulation or observational predictive sufficiency. Data
identification, partial actions, approximation error and model misspecification
remain additional obligations.
