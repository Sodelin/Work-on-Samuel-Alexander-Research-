# Claim-to-proof ledger

Date: 2026-09-25. This ledger identifies the exact scope of statements; the aggregate package receipt records final source hashes and compiler results.

| Claim | Formal declaration / evidence | Limits |
|---|---|---|
| Eventual organism ancestry equals recurrent-deme reachability for late organisms | AncestryMixing.Pedigree.eventual_descendant_iff_recurrent_reach | All five Pedigree premises; actual ancestry derived, not assumed |
| Infinite S has IAP iff contained modulo finite in one recurrent component | AncestryMixing.Pedigree.iap_iff_one_recurrent_component_mod_finite | Containment, not equality with the full component; S need not be convex or connected |
| Representative component uniqueness | AncestryMixing.Pedigree.component_unique_mod_finite in AncestryExamples | Checked in the concrete-examples supplement; equality of components, not equality of their chosen representatives |
| Whole-population IAP iff recurrent strong connectivity | AncestryMixing.Pedigree.whole_iap_iff_recurrent_strongly_connected | Not merely undirected connectivity |
| Common-cutoff component tails are infinite Specieslike and Reflection | AncestryMixing.Pedigree.recurrent_component_tails_specieslike_reflection | No maximality assertion |
| Concrete two-deme models satisfy premises; one-way fails IAP and bidirectional succeeds | AncestryMixing.Examples.twoDeme, oneWay_not_iap, bidirectional_iap | One organism per deme/generation; mathematical witness, not empirical fit |
| Culture remains in the frequency square | FeedbackDynamics.culture_mem_square and culture_trajectory_mem_square | Cultural mixing parameter in [0,1] |
| Full local asymptotic stability of supplied polarized fixed point | FeedbackDynamics.polarized_locally_asymptotically_stable | 0<m<1/8 and supplied 0<d<1 satisfying polynomial fixed-point equation |
| Stable rational witness, actual culture-dependent neutral convergence | FeedbackDynamics.explicit_cultural_genetic_counterexample | m=7/78, cultural limit (7/8,1/8), rational response 1/(2(1+d²)); one-way coupling |
| General residual-exchange floor and neutral convergence | FeedbackDynamics.rationalFlow_bounds, coupled_neutral_convergence | 0<g<=1/2, k>=0; real frequency recursion, not conditional probability of a mating event |
| Neutral frequencies remain valid | FeedbackDynamics.neutral_frequency_invariant | Valid initial frequencies and convex mixing weights |
| No polymorphic fixed point for positive selection in source affinity recursion | FogartyAffinity.no_polymorphic_fixed_point and step_not_fixed | Simplex, s>0, beta1,beta2 in [0,1]; not the paper's other model |
| Uniform odds contraction under arbitrary admissible affinity sequences | FogartyAffinity.source_contracts_odds, trajectory_odds_bound | Explicit initial odds bound, constant selection; derived from four source equations |
| Global fixation and finite-time deficit for actual model | FogartyAffinity.model_global_fixation | Initially x1>0 and x3>0, s>0, both affinity sequences in [0,1] |
| Sharper deficit r/(1+r) from odds bound | FogartyAffinity.odds_deficit_sharp | Compose with trajectory_odds_bound; no separate optimality assertion |
| Conditional-probability sums identify recurrent parenthood | Written Corollary 2 + standard conditional Borel–Cantelli | Stochastic adapter NOT Lean checked; assumes structural conditions almost surely |
| Uniform L may be replaced by per-organism finite local dissemination times | Written proof observation | NOT a checked generalized Pedigree structure |
| Explicit square-root parameter exists throughout 0<m<1/8 | Elementary real formula in explanatory prose | General sqrt existence NOT checked; supplied-d family and rational witness are checked |
| Nonlinear instability above 1/8 | Not claimed as a separate proved endpoint | First-order expansion and coefficient thresholds checked; no imported nonlinear-instability theorem |
| Biological gene–epigenetic–cultural speciation mechanism | Research motivation only | Not empirically established or fully modelled here |
| Originality / published-open-problem solution | Not established | Internal proof review and Lean do not settle prior art |
| Full Wong2024 formalization | Unfinished separate task | Existing selected graph formalization must not be called whole-paper completion |

## Statement alignment notes

The manuscript defines recurrent edges only between distinct demes. The Lean Recurrent relation also permits diagonal recurring edges. Adding or removing diagonal edges does not change reflexive transitive reachability or strongly connected components. Both interfaces therefore use the same component partition; this convention is stated, not hidden.

Strict organism ancestry is the existing SpeciesBridge.Descendant nonempty-path relation. FiniteSupport is the repository's finite-subset predicate on Nat; generation need not equal organism identifier. Component-tail convexity uses ambient ancestry, not only paths inside the chosen tail.

LocallyAsymptoticallyStable includes fixedness, full-neighbourhood Lyapunov epsilon stability and attraction. It is not a synonym for a selected eigenvalue condition. Neutral convergence is a literal epsilon statement, not a conclusion drawn from a finite numerical run.

CultureFixates means the marginal q tends to one. It does not assert fixation of the genetic allele A. The odds theorem permits varying affinity probabilities but keeps selection positive and constant. Positive initial x1 and x3 are explicit, so the finite initial ratio is well-defined.

## Verification distinctions

The final aggregate runner freshly compiles packaged custom source against pinned prebuilt Mathlib dependencies. This is a reproducible local compilation mode. It is not a clean-machine download or hosted-CI receipt. Source hashes and the exact mode must accompany any public claim.

There are no custom postulated theorems in the claimed endpoints. The permitted standard axioms are propext, Classical.choice and Quot.sound. A source scan alone is not the verification; the compiler and explicit endpoint axiom reports are the evidence.

Internal review found no identified proof gap under the encoded hypotheses. An independent external statement and novelty review remains outstanding.
