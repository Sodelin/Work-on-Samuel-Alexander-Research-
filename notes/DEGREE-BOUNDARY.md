# The offspring-degree boundary in gendered populations

Status: self-contained counting observations and two checked arithmetic lemmas. This is a research note, not a priority claim. The Lean file does not formalize the population graph or its birthdate ordering.

## Model and sources

Use Alexander's directed graph with a finite set of roots, strictly increasing real birthdates along edges, finite birthdate sublevels, and a distinct incoming edge of each of `k` labels at every nonroot. The graph is simple: an ordered pair of vertices carries at most one edge and one label. See Alexander, *Biologically Unavoidable Sequences*, Definition 1 and Section 6: https://www.combinatorics.org/ojs/index.php/eljc/article/download/v20i1p31/pdf/ .

The 10 September 2026 classification manuscript, Section 2, constructs a binary edge-labelled avoiding population with exactly two roots, two parents per nonroot, and at most two children per vertex. Its Section 3 converts to fixed genders on vertices by taking copies, yielding four roots and at most four children per vertex: https://github.com/avg-netizen/biological-unavoidability/blob/main/paper.md .

## Proposition 1: offspring threshold

Let each vertex have at most `d` children, and let the population have `R` roots. In any finite prefix of `N` vertices ordered by nondecreasing birthdate, let `R_N` be the roots in that prefix. Every parent of a vertex in the prefix is also in the prefix, because edges strictly increase birthdate. Each of the `N - R_N` nonroots has at least `k` distinct incoming edges, so the prefix contains at least `k(N - R_N)` edges. Its vertices supply at most `dN` outgoing edges. Therefore

```text
k(N - R_N) <= dN,
(k - d)N <= kR_N <= kR.
```

If `d < k`, every such prefix has `N <= floor(kR/(k-d))`. An infinite population has prefixes of arbitrarily large size, so no infinite population exists under this stricter child cap. The classification manuscript's binary construction attains `d = k = 2`, showing that the threshold is sharp for binary edge-labelled populations.

This proposition is a direct edge count. No novelty or literature priority is claimed. The targeted search found no source explicitly isolating this bound in this setting.

## Proposition 2: fixed-vertex-gender balance at the binary boundary

Now suppose genders are fixed on vertices, every nonroot has both a male and a female parent, and each vertex has at most two children. Let `M_N` and `F_N` be the male and female counts in the same birthdate prefix, so `N = M_N + F_N`. Its nonroots require at least `N - R_N` incoming edges from male parents and at least `N - R_N` from female parents. Hence

```text
N - R_N <= 2M_N,
N - R_N <= 2F_N,
|M_N - F_N| <= R_N <= R.
```

Thus any binary fixed-gender population with at most two children per vertex has uniformly bounded gender discrepancy in birthdate order. This is only a necessary condition. It neither constructs a two-child fixed-gender avoiding population nor proves all sequences unavoidable in that class.

**Precise next question.** For every noneventually-periodic binary sequence `s`, is there a binary population that avoids `s`, assigns one permanent gender to each vertex, and gives every vertex at most two children? The classification manuscript's edge-labelled construction and four-child fixed-gender lift do not settle this variant. Targeted searches of Alexander's paper, the classification manuscript and associated repository, and web results for fixed vertex genders with degree two found no resolution; that is a search limit, not an open-problem priority claim.

## Lean verification scope

`DegreeBounds.lean` imports only `Std`. It checks the arithmetic implications from the edge-count assumptions:

```text
lake build
```

On the original Windows host, elan required `ELAN_HOME` to point at the existing elan directory first. Checked with Lean 4.33.1; `lake build` exited successfully. The file contains no `sorry`. It does not formalize the graph-theoretic step that supplies the edge-count inequalities, so it is not an end-to-end formal theorem about populations.
