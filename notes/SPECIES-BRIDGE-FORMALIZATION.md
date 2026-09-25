# A specieslike-cluster bridge for the binary avoiding graph

**Current integration update.** The module-specific scope below records the original bridge. Its former project gaps are now closed by BirthOrder, PositiveUnavoidability and RealBridges; the old conditional helper remains a conditional helper. See [current coverage](../FORMALIZATION.md).

The graph geometry is kernel-checked in
[`SpeciesBridge.lean`](../lean/SamuelAlexanderResearch/SpeciesBridge.lean).
[`BinaryPopulation.lean`](../lean/SamuelAlexanderResearch/BinaryPopulation.lean)
joins it to the checked binary avoidance proof and all the displayed
natural-date population axioms.
[`SpeciesCones.lean`](../lean/SamuelAlexanderResearch/SpeciesCones.lean) classifies
the two maximal clusters after adding CA and REF. The positive
eventual-periodic unavoidability theorem remains an explicit external
dependency. No novelty or human peer-review claim is made.

## Exact graph and theorem

The binary edge-labelled construction $P_{s}$ has the same underlying graph for
every target word $s$. Its vertices are `Nat`, with

$$
\operatorname{PsEdge}(u,w)\iff 2\le w\land(w=u+1\lor w=u+2).
$$

There is no edge $0 \to 1$. Labels do not enter the species predicates, so the
module works directly with this explicit graph rather than assuming that some
unspecified population is a cluster. The principal theorem is:

```lean
SpeciesBridge.psWhole_bridge :
  NaturalDateBiosphere PsEdge ∧
  MaximalSpecieslike PsEdge Whole ∧
  Reflection PsEdge Whole ∧
  ¬ CommonAncestor PsEdge Whole
```

`Whole` is all of `Nat`. Maximality compares subsets of this same ambient graph;
it does not assert maximality after adding vertices or edges to the ambient
population.

## Definition fidelity

The species definitions are checked against
[Alexander (2026), Definitions 2–4, 8–9](https://arxiv.org/html/2602.05274v1).
Ancestorhood is a directed path of positive length. IAP requires, for each
member, finitely many descendants in the set or finitely many non-descendants
in the set. Convexity uses ancestry in the ambient graph. Connectivity uses
undirected paths contained in the induced subgraph, and the whole graph is
nonempty. A specieslike set is connected, IAP, and convex. REF compares global
infinitude of a member's descendants with infinitude inside the set. CA requires
one member to be ancestor of every distinct member.

The implementation represents a finite natural-number set by a finite list
cover. `finiteSupport_iff_bounded` proves this is equivalent to containment in
some initial segment. The forward proof bounds every list member by the list
sum; the reverse proof supplies `List.range bound`. Infinitude is the negation
of this finite-cover property, not an assumed cardinality predicate.

## Verified coverage

| Lean result | Mathematical content |
| --- | --- |
| `positive_reaches` | Every $u \ge 1$ reaches every $w > u$. |
| `zero_reaches` | Vertex $0$ reaches every $w \ge 2$. |
| `psDescendant_iff` | Strict reachability is exactly $u < w$ and $2 \le w$. |
| `psNonDescendant_iff` | A non-descendant $w$ is exactly one with $w \le u$ or $w \le 1$. |
| `psNonDescendant_bound`, `psNonDescendants_finite` | Every non-descendant of $u$ is below $u + 2$, giving an explicit finite cover. |
| `psWhole_weaklyConnected` | Any two vertices connect through the common descendant $u + v + 2$. |
| `psSubset_iap` | Every subset of this graph has IAP, since each global non-descendant set is finite. |
| `psSubset_specieslike_iff` | In this graph, a subset is specieslike exactly when it is weakly connected and convex. |
| `whole_convex`, `whole_reflection` | The whole vertex set is convex and satisfies REF for any ambient graph on `Nat`. |
| `psWhole_specieslike`, `psWhole_maximalSpecieslike` | The whole graph is a specieslike cluster and is inclusion-maximal in itself. |
| `psRoot_iff` | A vertex has no parents exactly when it is $0$ or $1$. |
| `psWhole_not_commonAncestor` | The two roots rule out CA. A proposed common ancestor equal to $0$ cannot reach $1$; any other candidate cannot reach $0$. |
| `psDescendants_infinite` | Every vertex has infinitely many descendants. |
| `psChildren_finite` | All children of $v$ belong to $[v + 1, v + 2]$. |
| `psNaturalDateBiosphere` | Parent dates increase; natural-date prefixes and each child set are finite; the vertex set is infinite. |
| `psEvery_vertex_in_maximal_cluster` | Each vertex of this graph belongs to a maximal specieslike cluster satisfying REF. |

The last result is specific to this graph. It does not solve the general
alternative-assumptions question about arbitrary ambient biospheres.

## Birthdate boundary

[Alexander's Definition 1](https://arxiv.org/html/2602.05274v1#S2) uses real
birthdates and finite populations before every real bound. This module uses
$t(v) = v$ with natural-number date bounds. To specialize the same construction
to real birthdates, the remaining standard mathematical step is: for each real
$r$, choose a natural $N > r$; then the vertices with real birthdate below $r$
are contained in `List.range N`. The strict-order-preserving embedding of `Nat`
into `Real` supplies the parent-date condition. That real embedding and
Archimedean step are **not formalized here**. `Std` is the only dependency.

## Checked labelled population and avoidance endpoint

`BinaryPopulation.ForgetLabels` converts the actual labelled relation
`BinaryAvoidance.Edge s` into an unlabelled graph.
`BinaryPopulation.forget_edge_eq` proves it equals `SpeciesBridge.PsEdge`;
there is no assumed identification between two separate witness models.

`BinaryPopulation.BinaryNatPopulation` combines functional labels on ordered
vertex pairs, the natural-date biosphere package, finitely many roots, and an
incoming edge of each Bool label at every non-root. The module proves these
properties for `Edge s`. It additionally checks that each incoming label has
exactly one parent, the two parents are distinct, the roots are exactly $0$
and $1$, vertex $0$ has only child $2$, and every positive vertex has exactly
the two indicated children.

The imported local module
[`BinaryAvoidance.lean`](../lean/SamuelAlexanderResearch/BinaryAvoidance.lean)
is a fresh Std-only formalization of the binary argument in
[the classification manuscript, Section 2](https://github.com/avg-netizen/biological-unavoidability/blob/main/paper.md).
A matching path has $\operatorname{path}(k)\ge2k$; the natural offset `path(k) - 2k` is
nonincreasing and stabilizes. A stable odd offset gives period $e + 1$, while a
stable even offset gives period $2(e + 1)$. Starts are unrestricted, so the
conclusion covers paths from every vertex. Independent inspection of this
local proof found no discrepancy with the manuscript's argument; this is
separate AI review, not human review.

The complete combined negative endpoint is:

```lean
BinaryPopulation.explicit_specieslike_avoider
  (s : Nat -> Bool)
  (aperiodic : ¬ BinaryAvoidance.EventuallyPeriodic s) :
    BinaryNatPopulation (Edge s) ∧
    MaximalSpecieslike (ForgetLabels (Edge s)) Whole ∧
    Reflection (ForgetLabels (Edge s)) Whole ∧
    ¬ CommonAncestor (ForgetLabels (Edge s)) Whole ∧
    ¬ Realizes (Edge s) s
```

`BinaryPopulation.aperiodic_specieslike_counterexample` packages the same
explicit construction existentially. The labelled graph, population axioms,
species properties, and avoidance are all checked in the natural-date model.
The real-date boundary described above still applies.

## Precise conditional classification corollary

`BinaryPopulation.SpecieslikeUnavoidable s` means that every
`BinaryNatPopulation` whose whole graph is specieslike realizes $s$.
The theorem
`BinaryPopulation.specieslike_unavoidable_implies_eventuallyPeriodic` proves
unconditionally that this property forces eventual periodicity, by applying
the explicitly constructed avoiding population.

The converse remains conditional. The exact Lean theorem is
`BinaryPopulation.specieslike_classification_of_positive`, and it requires the
following named positive premise:

```lean
forall (s : Nat -> Bool), EventuallyPeriodic s ->
  forall E : LabelledGraph, BinaryNatPopulation E -> Realizes E s
```

Under that premise it proves
`SpecieslikeUnavoidable s ↔ EventuallyPeriodic s`. The positive result is the
prior-result dependency ALEX13 in [`SOURCES.md`](../SOURCES.md). It has not been
proved or imported here. Thus this equivalence is a **conditional Lean
theorem**, not an unconditional end-to-end formalization of the classification.
The counterexample implication has no such missing input.

The same mathematical conditional argument works when the restricted class
additionally requires REF or maximality of the whole specieslike graph:
`explicit_specieslike_avoider` supplies both. CA cannot be added to this
whole-graph witness argument because its conclusion explicitly includes CA
failure. No fixed-vertex-gender copy construction is covered by this module.

## Exact classification after adding CA and REF

The whole graph's maximal specieslike property and its failure of CA concern
different requirements. In `SpeciesCones.lean`, `FourAxioms S` is exactly IAP,
convexity, CA, and REF inside the fixed ambient `PsEdge` graph.
`MaximalFourAxioms S` is inclusion-maximality among sets with those four
properties.

For $\operatorname{Cone}(r)=\{r\}\cup\{\text{strict descendants of }r\}$, the module proves all four
properties and weak connectivity. In particular:

$$
\begin{aligned}C_0&=\operatorname{Cone}(0)=\{0\}\cup\{v:2\le v\},\\C_1&=\operatorname{Cone}(1)=\{v:1\le v\}.\end{aligned}
$$

`SpeciesCones.c0_iff` and `SpeciesCones.c1_iff` verify these descriptions. The
main endpoint is the exact classification

```lean
SpeciesCones.maximalFourAxioms_iff (S : SpeciesBridge.NatSet) :
  MaximalFourAxioms S ↔ S = C0 ∨ S = C1
```

The key lemma `commonAncestor_subset_root_cone` uses CA alone: a common
ancestor equal to $0$ puts the entire set inside $C0$; a positive common
ancestor puts it inside $C1$. Both root cones meet the four predicates. A
proper extension of $C0$ or $C1$ satisfying CA cannot move into the other cone,
because it would have to retain its original root. Maximality therefore forces
one of the two displayed sets.

`SpeciesCones.c0_ne_c1` proves they are distinct.
`SpeciesCones.maximalFourAxioms_specieslike` proves the classified maximal
sets are specieslike clusters, and
`SpeciesCones.every_vertex_in_maximal_four_cluster` gives a containing maximal
constrained cluster for every vertex. Vertex $0$ belongs only to $C0$, vertex
$1$ only to $C1$, and vertices from $2$ onward belong to both, by the explicit
membership characterizations. This exact classification remains specific to
the binary graph; it does not answer the general arbitrary-biosphere problem.

The related root-cone phenomenon already appears in Alexander's [2026 Example 14(1)](https://arxiv.org/html/2602.05274v1#S6), for a different generational graph with $k$ initial roots. This two-cone proof is a checked specialization to the avoiding construction, not a novelty claim for the general phenomenon.

## Reproduction and axiom audit

Verified with Lean `4.33.1`, Windows x86-64, commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`:

```powershell
$env:ELAN_HOME = 'C:\Users\Owner\.elan'
& 'C:\Users\Owner\.elan\bin\lake.exe' env lean lean/SamuelAlexanderResearch/SpeciesBridge.lean
& 'C:\Users\Owner\.elan\bin\lake.exe' build SamuelAlexanderResearch.BinaryAvoidance SamuelAlexanderResearch.SpeciesBridge
& 'C:\Users\Owner\.elan\bin\lake.exe' env lean lean/SamuelAlexanderResearch/BinaryPopulation.lean
& 'C:\Users\Owner\.elan\bin\lake.exe' env lean lean/SamuelAlexanderResearch/SpeciesCones.lean
```

Run from the repository root. All displayed commands were verified with exit
code $0$. The dependency build makes the local imports available to the two
composition checks. The three modules contain 21 `#print axioms` commands,
covering the principal graph, population, avoidance, conditional classification,
and two-cone endpoints. Their union is exactly the standard Lean axioms
`propext`, `Classical.choice`, and `Quot.sound`; there are no project axioms or
`sorryAx`. There are no `sorry`, `admit`, or `native_decide` proofs.

These direct commands verify the modules independently of the repository's
root import list. Integration into the full library build is a separate owning
task.
