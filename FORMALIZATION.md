# Checked mathematics and exact remaining scope

The Lean 4.33.1 library now includes the positive binary theorem, constructed
birth-order enumeration, full infinite degree counts, productive fixed-gender
cores, general species criteria, and quantitative extensions of the sharp
Thue-Morse result. The [core audit](verification/formal-audit.json) and
[real-number audit](verification/real-audit.json) give the selected endpoint
counts, dependency checks and exact source hashes. The default library uses
Std; the optional [real project](real/lakefile.lean) pins Mathlib separately.

This package formalizes the statements listed below. The positive classification
is binary; it is not a formalization of every finite-alphabet theorem or every
cellular-automaton argument in the sources. The earlier conditional helper
remains available, while the new positive module proves its missing premise.

## Coverage

| Development | Checked conclusion | Exact scope |
|---|---|---|
| [PositiveUnavoidability](lean/SamuelAlexanderResearch/PositiveUnavoidability.lean) | Every eventually periodic binary word is realized; unconditional binary natural-population and specieslike classifications follow. | Derives finite branching and infinite-path selection from actual population axioms. This formalizes the attributed positive theorem. |
| [BirthOrder](lean/SamuelAlexanderResearch/BirthOrder.lean) | Constructs a bijective enumeration in nondecreasing birth order from infinitude and finite sublevels. | Arbitrary vertex type and linearly preordered time; tied dates are allowed. No enumeration or countability premise. |
| [PopulationReindex](lean/SamuelAlexanderResearch/PopulationReindex.lean) | Constructs the actual natural-index counting population; preserves labels and child caps; transports subcritical impossibility and at least `k` distinct roots. | Functional `Option Nat` labels below `k`, chronological edges, finite roots, finite sublevels and actual child covers of length at most `d`. |
| [RealBridges](real/RealBridges.lean) | Binary classification for arbitrary real-birthdated vertex sets; real-date finite-alphabet degree/root results; real-valued sharp coefficients and actual convex-hull inclusion. | Literal Mathlib reals. Coefficients multiply natural vertex indices cast to reals, not arbitrary birth timestamps. See the [real scope note](notes/REAL-BRIDGES-FORMALIZATION.md). |
| [PopulationCounting](lean/SamuelAlexanderResearch/PopulationCounting.lean) | Actual finite double counts, predecessor-closed prefix bounds, subcritical impossibility, and fixed-gender imbalance. | Simple labelled graphs. The old arithmetic-only DegreeBounds layer remains available. |
| [InfiniteConservation](lean/SamuelAlexanderResearch/InfiniteConservation.lean) | Full infinite-graph identity `D_N+E_N+C_N=kR_N`; `C_N>=k(k+1)/2` after all roots; finite total defects, eventual full degree `k`, and constant crossing width. | Conservation uses critical child cap `d=k`. The triangular lower bound permits any cap. The defect budget is `D+E<=kR-k(k+1)/2`. |
| [MinimalCrossing](lean/SamuelAlexanderResearch/MinimalCrossing.lean) | Binary crossing width three on every tail cut forces exactly the `+1,+2` tail edges. With permanent source genders it realizes every word. An avoiding critical fixed-gender population has eventual crossing width at least four. | The four is crossing width, not a child-cap lower bound. General-`k` rigidity and cap-two avoidance remain open. |
| [BinaryAvoidance](lean/SamuelAlexanderResearch/BinaryAvoidance.lean) and [BinaryPopulation](lean/SamuelAlexanderResearch/BinaryPopulation.lean) | The actual target-dependent graph avoids every non-eventually-periodic target; all population and specieslike hypotheses are checked. | Independent composable formalization of the classification manuscript's negative binary construction; not a claim to have originated it. |
| [FixedGenderLift](lean/SamuelAlexanderResearch/FixedGenderLift.lean) | A productive core avoids any prescribed aperiodic target with permanent source genders, cap three, exactly two roots, and whole-graph specieslike/inspecies/reflection properties. The earlier cap-four cleaned lift is also checked and is not an inspecies. | Population membership is the retained subset. Deleted indices are not extra vertices or roots. [FixedGenderReindex](lean/SamuelAlexanderResearch/FixedGenderReindex.lean) constructs the subtype enumeration and proves the unconditional cap-three fixed-gender classification. |
| [SpeciesGlobalIAP](lean/SamuelAlexanderResearch/SpeciesGlobalIAP.lean) | Finite/cofinite descendant criteria for IAP and reflection; whole-inspecies/cofinite-descendant equivalence; exact specializations to `P_s`. | Strict ancestry and ambient-versus-internal infinitude are explicit. Broad cofinite-descendant phenomena have prior results in Alexander's 2013 work. |
| [SpeciesRootCriterion](lean/SamuelAlexanderResearch/SpeciesRootCriterion.lean) | Under root coverage, root-cone IAP is equivalent to the exact maximal IAP/CONV/CA/REF cone classification. Strict natural birth order derives root coverage. | Maximal for the four stated properties, not a general maximal-species theorem. [SpeciesCones](lean/SamuelAlexanderResearch/SpeciesCones.lean) gives the two exact cones of `P_s`. |
| [GeneralRootObstruction](lean/SamuelAlexanderResearch/GeneralRootObstruction.lean) | The first `k` indices are roots, at least `k` distinct roots exist, and whole-population common ancestry fails for `k>=2`. | Simplicity and all required incoming labels are essential; the count is at least `k`, not exactly `k`. |
| [LayeredUnavoidability](lean/SamuelAlexanderResearch/LayeredUnavoidability.lean) | Every binary word is realized when every edge advances one layer, all roots are at layer zero and arbitrary layer depths exist. | This is the precise consecutive-layer specialization, not universality from connectedness alone. |
| [SharpThueMorse](lean/SamuelAlexanderResearch/SharpThueMorse.lean), [ThueMorseBits](lean/SamuelAlexanderResearch/ThueMorseBits.lean), [ThueMorseBound](lean/SamuelAlexanderResearch/ThueMorseBound.lean) | Actual bits and exact interval reachability imply `3L(v)<=8v-1` for `v>=1`, with equality exactly at `v=3*2^n-1`, where `L=8*2^n-3`. | Actual original edges, edge-count lengths, attained maxima, no unchecked trajectory premise. |
| [SharpCorollaries](lean/SamuelAlexanderResearch/SharpCorollaries.lean) | Exact first-hit classification of the auxiliary baseline trajectory, including starts 0, 1 and 2; rational-coefficient optimality. | Baseline hitting time and matching maximum are distinct definitions. Real coefficient optimality is separately proved in RealBridges. |
| [FiniteEditStability](lean/SamuelAlexanderResearch/FiniteEditStability.lean) | If `s=t` from index `m`, actual finite matches transport with unchanged length and start displacement at most `m`; `3L_s(v)<=8v+8m-1` for `v>=1`, maxima exist, and arbitrarily late near-sharp witnesses exist. | `m` bounds the edited initial segment. The exported displacement is at most `m`; `min(m,ell)` is the suffix cutoff. |
| [PhaseShift](lean/SamuelAlexanderResearch/PhaseShift.lean) | For the graph rebuilt from `t(k+a)`, `3L_a(v)<=8v+5a-1` for `v>=1` and actual dyadic lower witnesses exist in a specified start interval. | Both graph and target change. [PhaseExtremal](lean/SamuelAlexanderResearch/PhaseExtremal.lean) proves equality exactly when `v=3*2^n-a-1` and `a<=2^n`, with maximum `8*2^n-a-3`; see its [scope note](notes/PHASE-EXTREMAL-FORMALIZATION.md). |
| [QuantitativeAvoidance](lean/SamuelAlexanderResearch/QuantitativeAvoidance.lean), [SlowAvoidance](lean/SamuelAlexanderResearch/SlowAvoidance.lean), [FiniteAvoidance](lean/SamuelAlexanderResearch/FiniteAvoidance.lean) | Periodic prefixes give explicit long matches. Every aperiodic target has an attained finite maximum at every start. For every function `f`, an aperiodic target has finite maxima exceeding `f(v)` at strictly increasing starts. | The word is executable relative to `f`; no separate formal Turing-computability predicate or effective uniform bound is claimed. |
| [AncestryViews](lean/SamuelAlexanderResearch/AncestryViews.lean), [SpeciesAdapter](lean/SamuelAlexanderResearch/SpeciesAdapter.lean), [HistoryProjection](lean/SamuelAlexanderResearch/HistoryProjection.lean), [ObservationPrediction](lean/SamuelAlexanderResearch/ObservationPrediction.lean) | Fixed-index paths survive erasure; erasure can lose ancestry information; history paths project; exact recovery and prediction have explicit observation-fibre criteria and counterexamples. | These distinguish indexed genetic/history information from unlabelled organism ancestry. See the [interface note](notes/ANCESTRY-OBSERVATION-INTERFACE.md). |
| [StaticMixing](lean/SamuelAlexanderResearch/StaticMixing.lean) and RealBridges | Rational weighted-mix inclusion, a strict midpoint example, and actual real convex-hull inclusion. | Static algebra only. Infinite CA lifelines, limiting velocities and a new rule-specific speed theorem remain outside these endpoints. |

## Source and review boundary

The [classification manuscript, pinned Section 2](https://github.com/avg-netizen/biological-unavoidability/blob/3d6175e3e23f67bd68e7be591b5a9a6d04e496a3/paper.md#2-an-explicit-binary-avoiding-population)
supplies `P_s` and the negative offset argument. Alexander's
[2013 paper](https://arxiv.org/html/1212.0186v2) supplies the population framework
and positive eventual-periodic theorem. His [inspecies paper](https://arxiv.org/html/1201.2869)
and [2026 cluster paper](https://arxiv.org/html/2602.05274v1) supply the species
definitions and important precedents. The [older-construction audit](notes/OLDER-CONSTRUCTIONS-AND-RANK-AUDIT.md)
shows that `T_h` and `H_h` already have inspecies structure; the cap-three
construction's distinction is arbitrary prescribed target plus a uniform cap.

The avoiding graph has no `0 -> 1` edge, path length counts edges, and the
first edge spells target index zero. Fixed source genders are an additional
restriction relative to independently labelled edges. Common ancestry of the
whole graph differs from common ancestry inside a selected cone.

The [statement review](verification/STATEMENT-REVIEW.md) and [gap-closure review](verification/GAP-CLOSURE-REVIEW.md)
record independent checks of these premises. The [ten proposals](TEN-RESEARCH-IDEAS.md)
distinguish checked seeds from open generalizations. In particular, the
[full-height digit formula](research/thue-morse/FULL-HEIGHT-CONJECTURE.md) remains
conjectural despite exact finite agreement. No review or build establishes
global literature novelty or an author's private prior knowledge.

## Reproduction

```sh
python checks/audit_lean.py --output verification/formal-audit.json
python -m unittest discover -s checks -p 'test_*.py' -v
python checks/check_local_certificate.py
python research/thue-morse/interval_check.py
python research/thue-morse/sharp_check.py
```

The audit first builds the library, verifies the toolchain, checks every selected
endpoint is reported, and allows only `propext`, `Classical.choice` and
`Quot.sound`. See [REPRODUCE.md](REPRODUCE.md) and the [real-project note](notes/REAL-BRIDGES-FORMALIZATION.md)
for Mathlib preparation and `python checks/audit_lean.py --real`. The [workflow](.github/workflows/verify.yml)
runs the core and real audits independently on Linux. Historical receipts
apply to their recorded stages, not later changes.
