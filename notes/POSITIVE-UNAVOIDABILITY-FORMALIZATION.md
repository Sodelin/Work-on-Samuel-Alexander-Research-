# Positive unavoidability in actual binary natural-date populations

**Status:** proved in Lean 4.33.1 with Std only. The new
[`PositiveUnavoidability.lean`](../lean/SamuelAlexanderResearch/PositiveUnavoidability.lean)
closes the positive premise for the existing natural-date model and supplies
unconditional all-population and specieslike classifications. Its direct
compiler check exits 0, and every audited endpoint uses only subsets of
`propext`, `Classical.choice`, and `Quot.sound`.

This is a formalization of Samuel A. Alexander's known theorem, not a new
unavoidability or classification result. The primary source was read in full
for the relevant argument: [*Biologically unavoidable sequences*,
arXiv:1212.0186v2, Section 2](https://arxiv.org/html/1212.0186v2#S2), especially
Proposition 5 and Theorem 6. The source first obtains periodic paths through
finite branching and backward full-period blocks, then prepends the finite
initial word after obtaining a sufficiently late periodic tail. The local
implementation proves its finite-branching argument internally, using bounded
endpoint sets on Nat rather than importing a compactness theorem.

## Exact final statements

The main theorem has the following complete mathematical input and output:

```lean
theorem PositiveUnavoidability.eventuallyPeriodic_realized
    (s : Nat → Bool)
    (eventually : BinaryAvoidance.EventuallyPeriodic s)
    (E : BinaryPopulation.LabelledGraph)
    (population : BinaryPopulation.BinaryNatPopulation E) :
    BinaryPopulation.Realizes E s
```

Here eventual periodicity means that there exist `start` and `p>0` with
`s(k+p)=s(k)` for every `k>=start`. Realization means the existence of an
actual function `path : Nat → Nat` with
`E (path k) (path (k+1)) (s k)` for every `k`, beginning at target index zero.
No start vertex, family of populated layers, matching path, compactness
principle, or positive unavoidability theorem is an additional premise.

The population is exactly the existing `BinaryNatPopulation` definition:
functional Boolean edge labels; parent dates strictly below child dates;
finite date sublevels; finitely many children per vertex; infinitely many
vertices; finitely many roots; and an incoming parent of each Boolean label
at every nonroot. Birthdates are the identity on Nat. The proof constructs
what it needs from these hypotheses. In particular, the finite starting
interval and the infinite path are conclusions of internal lemmas.

Two classification endpoints now have no unproved positive premise:

```lean
PositiveUnavoidability.binaryNat_classification (s : Nat → Bool) :
  (∀ E, BinaryPopulation.BinaryNatPopulation E →
    BinaryPopulation.Realizes E s) ↔
  BinaryAvoidance.EventuallyPeriodic s

PositiveUnavoidability.specieslike_classification (s : Nat → Bool) :
  BinaryPopulation.SpecieslikeUnavoidable s ↔
  BinaryAvoidance.EventuallyPeriodic s
```

The specieslike statement uses the existing exact definition, which asks for
realization in every binary natural-date population whose whole graph is
specieslike. Its negative implication remains the earlier explicit avoiding
construction. Its positive implication is now supplied by
`eventuallyPeriodic_realized`, rather than left as a theorem parameter.

## Proof components and orientation

The internal `FinitePath E s k n u v` predicate describes a genuine length-`n`
edge path from `u` to `v`, spelling target indices `k` through `k+n-1`.
Concatenation, final-edge extension, strict endpoint growth, and shifting by
a period are proved for this predicate.

- `finite_children_uniform` derives one bound for all children of vertices in
  any finite initial interval. It follows from the actual finite-child covers.
- `backward_word` proves that any prescribed finite word can be pulled backward
  from every sufficiently late endpoint while keeping its start above a chosen
  root bound. It appends the last labelled edge after constructing the earlier
  prefix, so labels stay in forward order.
- `periodic_spanning` repeatedly removes a whole positive period. Strict dates
  make this recursion decrease on the endpoint. It produces a matching path to
  every sufficiently late vertex from a fixed bounded starting interval.
- `periodic_good_above` derives a start in that interval whose matching endpoint
  set is unbounded. If every candidate start had bounded endpoints, their finite
  union would contradict the spanning statement.
- `good_successor` proves the finite-branching step: a vertex with unbounded
  matching endpoints has a child with unbounded matching endpoints for the next
  target phase. `infinite_path_from_good` uses this proved successor property
  and ordinary classical choice to construct the infinite path.
- `periodic_realized_above` obtains a periodic realization whose initial vertex
  is above any requested natural bound.

For an eventually periodic word, the proof defines `tailWord k = s(start+k)`.
It first applies `backward_word` to the original length-`start` prefix and obtains
a threshold. It then realizes the periodic tail above that threshold, pulls the
original prefix backward to the tail's initial vertex, and applies
`FinitePath.prepend_infinite`. The final edge at the prefix/tail junction is
therefore indexed consistently: the prefix uses `s(0),...,s(start-1)`, and the
tail begins with `s(start)`. This construction also covers `start=0`.

## Verification

From the repository root, on the original Windows host:

```powershell
$env:ELAN_HOME = 'C:\Users\Owner\.elan'
$env:PATH = 'C:\Users\Owner\.elan\bin;' + $env:PATH
lake env lean lean/SamuelAlexanderResearch/PositiveUnavoidability.lean
```

The final command exits 0 without warnings on the pinned
`leanprover/lean4:v4.33.1` toolchain. Its exact axiom reports are:

```text
'PositiveUnavoidability.good_successor' depends on axioms: [propext, Classical.choice, Quot.sound]
'PositiveUnavoidability.infinite_path_from_good' depends on axioms: [propext, Classical.choice, Quot.sound]
'PositiveUnavoidability.backward_word' depends on axioms: [propext, Quot.sound]
'PositiveUnavoidability.periodic_spanning' depends on axioms: [propext, Quot.sound]
'PositiveUnavoidability.periodic_realized_above' depends on axioms: [propext, Classical.choice, Quot.sound]
'PositiveUnavoidability.eventuallyPeriodic_realized' depends on axioms: [propext, Classical.choice, Quot.sound]
'PositiveUnavoidability.binaryNat_classification' depends on axioms: [propext, Classical.choice, Quot.sound]
'PositiveUnavoidability.specieslike_classification' depends on axioms: [propext, Classical.choice, Quot.sound]
```

There is no `sorry`, admitted theorem, project axiom, `native_decide`, or Mathlib
dependency. No finite scan is used to justify an infinite statement. The
coordinating writer owns integration into the default import and endpoint audit;
this receipt establishes the direct check of the complete new module.

## Scope retained

This closes the positive and classification gaps for Boolean words and the
actual binary natural-date population model. It does not itself construct an
enumeration of a real-date population, generalize the type of labels to an
arbitrary finite alphabet, or prove new species existence results. Alexander's
source definitions, construction, and positive theorem retain their attribution.
