# Finite harmonic-certificate machinery

Status: uncompiled draft, 2026-09-25. No compiler has been started in this lane for this task; the shared slot is assigned elsewhere. This is standard finite Markov-kernel machinery, with no novelty claim.

`FiniteFixation.Kernel S` supplies a finite state type, nonnegative real entries `transition s t`, and each row summing to one. `Boundary S` gives disjoint Win and Loss classes. `Absorbing K B` sets transition probabilities to zero when leaving either terminal class; it allows arbitrary motion within that class, including changes at other loci. `UniformTerminal K B epsilon` bounds below the sum of transition probabilities into the union of those classes. The convergence endpoints require `0 < epsilon` and `epsilon <= 1`; already-terminal rows are allowed and remain terminal.

The distribution is defined, not postulated: `marginal K start 0` is the point mass at `start`, and the next value at state t is the finite sum of the current values at s times `transition s t`. `marginal_nonneg` and `marginal_total` establish its finite-distribution properties. `winProbability` is the expectation of the Win indicator, while `transientMass` is the expectation of the nonterminal indicator. The one-step duality `expect_push` connects this forward recursion to the backward action on functions (the operator customarily written P). No matrix-power notation is required.

A `Certificate K B h` requires four independently checkable conditions: h in [0,1]; h=1 on Win; h=0 on Loss; and the finite harmonic identity `sum_t P(s,t)*h(t)=h(s)`. The proposed proof derives rather than assumes that the certificate's expectation remains h(start). It then bounds the nonnegative difference `h(start)-winProbability(n)` by transient mass. This works because the pointwise difference between h and the Win indicator is zero on terminal states and lies in [0,1] elsewhere.

The main intended endpoints are:

- `transient_mass_geometric`: transient mass at time n is at most `(1-epsilon)^n`.
- `certificate_error_bound`: `0 <= h(start)-winProbability(n) <= transientMass(n)`.
- `win_probability_error`: absolute error is at most `(1-epsilon)^n`.
- `certificate_identifies_limit`: for every initial state and every positive tolerance, all sufficiently large finite-time win probabilities are within that tolerance of h(start).
- `transient_mass_vanishes`: transient mass tends to zero with the same explicit geometric bound.

The geometric estimate includes n=0 and epsilon=1. Its proof first establishes a pointwise one-step contraction of the nonterminal indicator: absorbing terminal rows contribute zero, and all other rows retain at most 1-epsilon nonterminal probability. Nonnegative finite summation propagates this bound through the actual marginal recursion.

Interpretation boundary: the source proves statements about real-valued finite-time distributions and their limits. If this kernel is realized by a stochastic process, absorbing classes make the limit the usual eventual-win/fixation probability. That path-space construction and event identification are not encoded here; no almost-sure infinite-path theorem is claimed. Biological adequacy, generation of the concrete transition counts, and verification of the proposed 81-state harmonic certificate belong to the separate concrete-model module.

All imports are present in the pinned local Mathlib cache. No dependency on UniformParentCounting or on FeedbackDynamics.olean is needed; the short epsilon argument uses the cached Archimedean power lemma directly. Optional uniqueness of bounded harmonic certificates is not yet packaged as a separate endpoint.

The draft also includes a one-off pulse distribution μ: its entries must be nonnegative and sum to one. `winProbabilityFrom K B μ n` is defined by the finite weighted sum of the existing state-start win probabilities. `certificate_mixture_error` bounds the nonnegative difference between `expect μ h` and that probability by `(1-epsilon)^n`; `win_probability_from_error` gives its absolute-value form; and `certificate_identifies_mixture_limit` gives explicit epsilon convergence to `expect μ h`. This is finite conditioning on the initial post-pulse state. No extra independence premise or infinite path-space construction is assumed. The concrete module must prove normalization of μ and evaluate its certificate average.

## Verification addendum, 2026-09-25

Historical draft/audit statements above are preserved. The [combined receipt](verification/combined-receipt.json) records 34 selected endpoints across FiniteFixation, FiniteEpigenetic, DeterministicEpigenetic and RankingReversal. The final deterministic source hash is ece655b0af42fbd580ca86b3f8176a8b4323fe3fd716da9429f13f6366f3117f. Changes after its reviewed draft repaired proof syntax/status text without changing the recurrence or mathematical statements. Reports use only propext, Classical.choice and Quot.sound. RankingReversal imported the preserved deterministic object and exited zero; the earlier deterministic process exit remains unretrieved and explicitly null. This addendum does not extend formal scope to source transport or deterministic common-limit existence.
