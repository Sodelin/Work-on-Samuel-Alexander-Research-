# Formal comparison of static speed regions

**Current integration update.** RealBridges now proves the normalized weighted inclusion for actual real modules and real convex hulls. The rational-only descriptions below refer to StaticMixing itself. Infinite dynamics and a new rule-specific speed limit remain outside both modules.

`StaticMixing.lean` checks the algebraic obstruction identified in the prose audit: a point common to all fixed permitted regions belongs to every normalized weighted Minkowski combination of those regions. It does so for actual two-dimensional rational vectors, finite lists of indices, explicit rational weights, and arbitrary region predicates.

The general endpoint is `StaticMixing.intersection_subset_weightedMix`. Its assumptions say that the weights are nonnegative and sum to one, and that the point belongs to every input region. The conclusion constructs the weighted-mix witness. The proof establishes that repeating the same vector in every summand returns that vector. It does not assume the desired set inclusion as an algebraic premise.

The two-region specialization is `StaticMixing.intersection_subset_midpointMix`. A further checked example shows strict containment: the vertical segments from $`(1,0)`$ to $`(1,1)`$ and from $`(1,-1)`$ to $`(1,0)`$ intersect only at their common endpoint, while their midpoint mix also contains $`(1,\tfrac12)`$.

The finite-list representation chooses one point per index value. Repeated indices therefore reuse that point. This suffices for the inclusion witness, including in an occurrence-wise Minkowski sum, but the module does not assert equality with an independent-choice sum for repeated indices and nonconvex regions. Distinct labels with frequency weights cover the intended static application directly.

This explains why a static alternating-label speed polygon cannot sharpen the intersection of the corresponding constant-label bounds. The reasoning that converts local-rule certificates into infinite lifelines and identifies all spaceship path limits remains a written argument using Alexander's theorem. This module does not formalize that infinite dynamical bridge, real convex hulls, or a new rule-specific speed limit. Its rational-vector theorem covers the algebraic comparison relevant to rational spaceship velocities; the real-vector version is not claimed as an encoded endpoint here.

The generic weighted theorem is a universal proof. `decide +kernel` is used only for exact rational constants and the finite strict-containment example, so those computations are checked by Lean's kernel. No native evaluation axiom is used.

Primary context: Alexander's [2013 periodic unavoidability and lifeline application](https://arxiv.org/html/1212.0186v2), and the repository's [corrected periodic-lifeline note](PERIODIC-LIFELINE.md). The comparison is a separately reviewed deduction, with no established literature-priority claim.
