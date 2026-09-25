# Brief mathematical handoff

This notebook studies the target-dependent avoiding population in the separate
[September classification manuscript](https://github.com/avg-netizen/biological-unavoidability),
alongside Alexander's [2013 unavoidability paper](https://arxiv.org/html/1212.0186v2)
and [2026 specieslike-cluster paper](https://arxiv.org/html/2602.05274v1).
The [question ledger](QUESTION-LEDGER.md) distinguishes historical questions
from follow-ons posed here. No message has been sent to Dr. Alexander.

## Results worth reviewing

1. **Sharp quantitative avoidance.** In the manuscript's Thue-Morse graph,
   `3L(v)<=8v-1`, with equality exactly at `v=3*2^n-1`, where
   `L=8*2^n-3`. The [proof](research/thue-morse/NEXT-INVARIANT.md) and
   [Lean development](lean/SamuelAlexanderResearch/SharpThueMorse.lean) include
   actual target bits, edge semantics and attained maxima.
2. **Stability and phase.** Finite target edits preserve the optimal coefficient
   `8/3`. Rebuilding the graph from `t(k+a)` gives `3L_a(v)<=8v+5a-1` and the
   same optimal coefficient. The exact shifted family is developed separately
   in [PhaseExtremal](lean/SamuelAlexanderResearch/PhaseExtremal.lean).
3. **Arbitrarily slow finite avoidance.** For every growth function `f`, an
   explicit relative construction gives an aperiodic target with actual finite
   maxima larger than `f(v)` along strictly increasing starts. All starts have
   finite maxima. See [FiniteAvoidance](lean/SamuelAlexanderResearch/FiniteAvoidance.lean).
4. **Uniform cap-three fixed-gender witness.** Productive pruning of the
   manuscript's two-copy lift gives an inspecies avoiding any prescribed
   aperiodic binary target, with permanent vertex genders and at most three
   children. The [formalization](lean/SamuelAlexanderResearch/FixedGenderLift.lean)
   treats the retained vertex set explicitly. Earlier `T_h` and `H_h` examples
   already have inspecies structure; the arbitrary-target/uniform-cap conjunction
   is the distinction to review.
5. **Critical population structure.** Full-degree conservation bounds all
   defects and forces eventual degree regularity. Crossing width is at least
   `k(k+1)/2`. In the binary minimum-width case, the tail is exactly the
   `+1,+2` graph; permanent genders then force universal realization.

The [ten proposals](TEN-RESEARCH-IDEAS.md) describe these results and five further
structural/computational directions. The most concrete next conjecture is a
[closed form for all matching heights](research/thue-morse/FULL-HEIGHT-CONJECTURE.md),
supported by exact stored and fresh computations but not yet proved.

## Formal and source scope

The package now constructs the birth-order enumeration, proves the positive
binary theorem, transports the binary classification to actual real birthdates,
and encodes general IAP/root-cone and degree/root interfaces. The default core
is Std-only; the optional real project pins Mathlib. Exact endpoints and hashes
are in [FORMALIZATION.md](FORMALIZATION.md) and its audit receipts.

The source classification, the positive theorem and broad cofinite-descendant
and cone phenomena retain their original attribution. The
[older-construction audit](notes/OLDER-CONSTRUCTIONS-AND-RANK-AUDIT.md) and
[prior-work ledger](PRIOR-WORK-AUDIT.md) prevent conflating those precedents
with the narrower quantitative and uniform-cap claims developed here.

Useful outside feedback would concern an equivalent earlier height formula,
the cap-two fixed-gender question, the general-`k` rigidity problem, or a
counterexample to the full-height conjecture. External review and literature
priority remain open. The repository owner can adapt the
[outreach draft](OUTREACH-DRAFT.md); sending it is a separate action.
