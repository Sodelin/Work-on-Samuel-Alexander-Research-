# Binary avoidance: the offset proof in Lean

The [2026 classification manuscript](https://github.com/avg-netizen/biological-unavoidability/blob/main/paper.md), Section 2, supplies the construction and mathematical argument. `BinaryAvoidance.lean` is a fresh formalization using the repository's existing Lean 4.33.1 and its standard library. This is verification of prior work, not a claim to have discovered that construction.

For a Boolean target $s$, the module defines $r(2j)=s(j)$ and $r(2j+1)=\neg s(j)$. An edge into $w$ exists only for $w\ge2$. It comes from $w-1$ with label $r(w)$, or from $w-2$ with the complementary label. Thus the missing edge $0\to1$ is encoded, and the edge at path index $k$ must spell $s(k)$.

The formal proof establishes:

1. Every matching infinite path satisfies $\operatorname{path}(k)\ge2k$.
2. The natural offset $\operatorname{path}(k)-2k$ never increases.
3. Every nonincreasing natural sequence eventually stabilizes, using a proved minimum-of-range argument.
4. A stable even offset forces an eventually complementary shift, and applying it twice gives a positive period. A stable odd offset directly gives a positive period.
5. Consequently an aperiodic target has no infinite matching path, from any starting vertex.

The exported negative endpoint is `BinaryAvoidance.aperiodic_target_avoided`. It assumes only that $s$ is not eventually periodic; it does not assume the existence of a barrier, an offset invariant, or the desired graph conclusion.

`BinaryPopulation.lean` composes this theorem with the independently formalized graph geometry and checks that the label predicate has the required population properties. See the species bridge note and the central formalization report for that endpoint's exact scope.

The positive binary theorem is formalized separately in [PositiveUnavoidability](../lean/SamuelAlexanderResearch/PositiveUnavoidability.lean), and [RealBridges](../real/RealBridges.lean) supplies the actual real-birthdate classification. Nor does it formalize the finite-alphabet copy-lift, the Thue–Morse overlap-free theorem, or the classical overlap-free proof. The sharper quantitative theorem is checked separately in SharpThueMorse. Natural-number birthdate properties are checked separately; the real-valued specialization is in the optional pinned Mathlib project.

The source manuscript already has its own formal negative endpoint. This implementation keeps the current repository independent of its external mathlib project, while preserving attribution and enabling direct composition with the new local graph results.
