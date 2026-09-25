# Maximal specieslike clusters with a real founding window

Date: 2026-09-25. The complete existence theorem below is proved in Lean on graphs whose organism identifiers are natural numbers and whose birthdates are real numbers. The eight modules contribute 50 selected audit endpoints. This note replaces the earlier written-proof-only status for this specific founder-window theorem; the registered aggregate audit passed with 151 real endpoints; its receipt is [real-audit.json](../verification/real-audit.json).

## Source question and contribution

Alexander's [Specieslike clusters based on identical ancestor points, Section 6](https://arxiv.org/html/2602.05274v1#S6) proves maximal-cluster existence under common ancestry (CA) and reflection (REF), then asks for alternative constraints without CA. Its Theorem 13 first constructs a suitable set through each organism before maximizing it. The formalization below supplies that seed construction and proves a replacement theorem using a fixed real founding duration. It is a mathematical response to the stated direction; biological plausibility, literature priority, and the author's intended sense of a qualitatively different constraint remain unestablished.

## Exact theorem

Let organisms be identified by `Nat`, let `E a b` mean that a is a parent of b, and let `birth : Nat -> Real` be their actual birthdate function. Assume:

1. Every parent has a strictly earlier birthdate than its child.
2. For every real t, only finitely many organisms have birthdate strictly less than t.
3. Every organism has finitely many children.

The vertex universe is countably infinite because it is `Nat`. Identifiers need not be chronological, and different organisms may have the same birthdate. No finite-root assumption is needed.

For a nonempty set S, a **founder** is a member with no strict ancestor in S, using ancestry in the ambient graph. Founders need not be parentless in the ambient graph. Let m(S) be the earliest birthdate of a member of S. The proof establishes that this minimum is attained. Fix a real duration Delta, shared by every candidate and competitor, and define:

~~~math
W_\Delta(S)\quad\Longleftrightarrow\quad
\forall r\in F(S),\quad \operatorname{birth}(r)\le m(S)+\Delta.
~~~

Let K_Delta consist of the sets that are nonempty, connected in their induced undirected graph, ancestry-convex, satisfy the identical ancestor point axiom (IAP), satisfy reflection (REF), and satisfy W_Delta. IAP means that each member has either only finitely many descendants in the set or only finitely many nondescendants in it. REF means that a member with infinitely many ambient descendants has infinitely many descendants inside the set.

**Proved theorem:** every member of K_Delta extends to an inclusion-maximal member of K_Delta. For every nonnegative real Delta, every organism belongs to such a maximal member.

Maximality is precisely against all supersets satisfying the same connectivity, convexity, IAP, REF, and fixed real-window requirements. It is not maximality among arbitrary specieslike sets. No uniqueness, partition, effective construction, or biological classification algorithm is asserted.

The strongest public endpoint is [RealSpeciesTheorem.every_vertex_in_maximal_real_window](../real/RealSpeciesTheorem.lean):

```lean
theorem every_vertex_in_maximal_real_window (E : Graph) (birth : Nat → ℝ)
    (finite : RealFounderWindow.StrictFiniteSublevels birth)
    (chronological : RealFounderWindow.Chronological E birth)
    (children : ∀ v, FiniteSupport (E v))
    (duration : ℝ) (nonnegative : 0 ≤ duration) (v : Nat) :
    ∃ M, M v ∧ MaximalWindowSpecies E birth duration M
```

The conditional extension endpoint `RealSpeciesTheorem.maximal_window_extension` does not need a separate nonnegative-duration premise because its initial member already supplies a valid window. The universal existence endpoint above uses nonnegativity to put its constructed common-ancestor seed inside K_Delta.

## Proof structure and source map

| Checked step | Source and endpoint | Role |
|---|---|---|
| Founder coverage in an ordered presentation | [FounderWindow.lean](../real/FounderWindow.lean), `founder_covers` | Every member equals or descends from an internal founder. |
| Directed-union IAP | [DirectedIAP.lean](../real/DirectedIAP.lean), `iap_directed_union_of_finite_founders` | Convex, reflecting IAP stages retain IAP when the union has finitely many founders. |
| Intersection compactness | [SeedIntersections.lean](../real/SeedIntersections.lean), `reflection_intersection` | REF survives nonempty downward-directed intersections of convex reflecting stages. |
| Genuine seed | [SpeciesSeed.lean](../real/SpeciesSeed.lean), `exists_seed` | Every vertex belongs to a connected convex IAP+CA+REF set; no assumed seed or `RootConesIAP`. |
| Literal real window | [RealFounderWindow.lean](../real/RealFounderWindow.lean), `window_directed_union` and `window_finite_founders` | The same real duration survives directed unions and supplies finitely many union founders. |
| Constrained Zorn extension | [FounderMaximal.lean](../real/FounderMaximal.lean), `maximal_window_extension_ordered` | Extends an existing class member to an inclusion-maximal member, with every competitor in the same class. |
| Faithful relabelling | [SpeciesReindex.lean](../real/SpeciesReindex.lean), `actual_presentation` and `window_iff` | Obtains strict index order while preserving literal real birthdates, ties, ancestry, all species predicates, and the unchanged duration. |
| Original-graph theorem | [RealSpeciesTheorem.lean](../real/RealSpeciesTheorem.lean), `every_vertex_has_seed`, `maximal_window_extension`, `every_vertex_in_maximal_real_window` | Composes the proofs for the original graph and every original competitor. |

The union argument locates a founder with infinitely many descendants in an offending nondescendant region. Productive-child induction supplies arbitrarily large productive descendants there. Reflection and IAP in a larger stage, followed by convexity, force those vertices into one fixed stage, contradicting IAP in that stage. The proof does not assume or separately construct an infinite ray.

The seed proof minimizes convex reflecting sets anchored at the prescribed organism. Actual intersections supply the lower bounds for reverse-inclusion Zorn. If a minimal set failed IAP, the productive part of its nondescendant region would be a smaller anchored convex reflecting set. That contradiction supplies IAP. This formalizes the seed obligation rather than assuming Theorem 13 as an axiom. A whole descendant cone can fail IAP, and a singleton at an organism with infinitely many descendants can fail REF; neither shortcut is used.

The real-date proof obtains an ordered enumeration internally. Its transported birth function is literally `fun i => birth (e.toFun i)`. Ranks never replace durations. Pulling an arbitrary original competitor back along the bijection ensures that the final maximality quantifier excludes no original competitor.

## A strict weakening of common ancestry

The following explanatory counterexample is verified mathematically here, but is **not a separately registered Lean endpoint** in this eight-module batch.

Use edges 0 -> 2, 1 -> 2, and n -> n+1 for n at least 2. Give organisms 0 and 1 birthdate 0, and organism n at least 2 birthdate n-1. Every edge increases birthdate, every organism has one child, and every real birth sublevel is finite. Strict ancestry is exactly the relation a < b and b at least 2. Each vertex therefore has cofinite descendants. The whole graph is connected, convex, IAP, and reflecting. Its founders are precisely 0 and 1, both born at its earliest time, so W_0 holds. Neither founder has an ancestor, so no member can be a common ancestor of both.

Thus W_0 permits multiple coeval founders. In particular, the real zero-duration condition must not be confused with the identity-date natural-number window, which has a unique earliest index. The example shows why removing CA from the conclusion has content; it does not establish biological plausibility for the replacement parameter.

## Relation to the Wong bridge

This theorem strengthens the infinite-organism side of the project. It does not change the meaning of Wong's finite interval-annotated genome graphs. The separately checked [Wong bridge coverage](WONG-ALEXANDER-BRIDGE-STATUS.md) and [finite-genome identifiability result](WONG-FINITE-IDENTIFIABILITY.md) retain their original assumptions: a finite genome observation does not by itself determine an infinite organism history or its specieslike status. A biologically justified genome-to-organism owner map remains a modelling obligation. The founder-window existence theorem neither supplies that map nor proves global graph self-similarity.

## Verification and bounded end state

The promoted sources are byte-for-byte the individually checked and independently reviewed eight modules. Their 50 selected endpoints are registered in [RealAudit.lean](../real/RealAudit.lean); the real project has 151 selected endpoints in total. Allowed axioms are only `propext`, `Classical.choice`, and `Quot.sound`. Some helper endpoints use no axioms. No `sorryAx` is permitted. Lean is pinned to 4.33.1 and Mathlib to `0df444a360eaa60ab8c11dca51a86af692955474`.

For this theorem, the mathematical gates are closed: directed-union IAP; real-window closure; connectivity, convexity and REF closure; constrained Zorn extension; a genuine per-vertex seed; and faithful transport to original real birthdates. The separate release gate is publication and hosted CI for the exact frozen packet. The existing core library remains unchanged at 405 audited endpoints. No arbitrary-vertex-type wrapper, full-paper completion, additional founder-count theorem, literature novelty certificate, or biological plausibility claim is included in this batch.
