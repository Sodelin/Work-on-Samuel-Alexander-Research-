# Formalization challenge: degree boundaries from population axioms

**Status:** The finite graph target, fixed-gender bound, predecessor-closed restriction, and infinite natural-order subcritical contradiction are now checked in [PopulationCounting.lean](../lean/SamuelAlexanderResearch/PopulationCounting.lean). The [scope note](../notes/FORMALIZATION-SCOPE.md) and [endpoint audit](../verification/FormalAudit.lean) identify the evidence. The original target below is retained to make acceptance review possible.

**Subsequent closure:** BirthOrder, PopulationReindex and RealBridges now handle the presentation/real-date bridge; InfiniteConservation proves the full infinite identity and regularity. Cap-two fixed-gender avoidance and general minimum-width rigidity remain mathematical research questions.

## Mathematical target

Model a finite birthdate prefix of a population with `N` vertices and `R_N` roots. For each nonroot, require an incoming edge of each of `k` labels, with distinct parent edges because each ordered pair has at most one label. Assume each vertex has at most `d` children. Edges strictly increase birthdate, so all parents of a prefix vertex lie in the prefix. Prove from these graph assumptions that

```text
k * (N - R_N) <= d * N,
(k - d) * N <= k * R_N.
```

For binary fixed vertex genders and `d=2`, prove from the corresponding graph assumptions that, among the first `N` births, `|M_N-F_N| <= R_N`. If practical, formalize the infinite consequence: finite roots and `d<k` preclude an infinite population with the stated birthdate finiteness axiom.

## Deliverable and acceptance checks

- Define the finite graph, labels or fixed vertex genders, roots, birthdate-prefix closure, and child cap explicitly. The edge-count inequality cannot be a theorem hypothesis in the end-to-end version.
- Compile under a pinned Lean toolchain; a pinned Mathlib dependency is fine if needed. Add a CI check and record exact commands and versions.
- Inspect `#print axioms` for every exported endpoint. No `sorry`, extra `axiom`, or `native_decide` standing in for the general theorem.
- Compare each formal hypothesis with Alexander's [population definition](https://www.combinatorics.org/ojs/index.php/eljc/article/view/v20i1p31) and write a short statement audit. Note any strengthening such as finite vertex types or a chosen total birth order.
- Keep attribution modest: the counting proof is elementary, and the targeted search in this repository does not establish literature priority. A Lean proof of the finite prefix is valuable even if the infinite corollary remains prose.
- Return a patch or PR plus a clear table of formally checked and still-prose claims.

This is a formalization challenge, not a request to prove the separate two-child fixed-gender avoidance question.
