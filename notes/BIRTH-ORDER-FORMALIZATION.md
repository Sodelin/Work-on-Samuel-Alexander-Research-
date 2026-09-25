# Constructing a natural enumeration from finite birthdate sublevels

[`BirthOrder.lean`](../lean/SamuelAlexanderResearch/BirthOrder.lean) constructs a
bijection from `Nat` to the vertex type using infinitude and finite birthdate
sublevels. No enumeration, countability result, minimum-selection theorem, or
family of finite population prefixes is assumed. The module uses only `Std`.

## Exact hypotheses and endpoint

The vertex type `V` and time type `Time` are arbitrary types. The time type has
`LE Time` and `Std.IsLinearPreorder Time`: its non-strict comparison is
reflexive, transitive, and total. Antisymmetry is not needed for the enumeration
argument. The other data are:

```lean
birth : V -> Time
infinite : BirthOrder.InfiniteVertices V
finite : BirthOrder.FiniteSublevels birth
```

The two predicates have their full mathematical meaning in the definitions:

```text
InfiniteVertices V:
  every finite list of vertices omits some vertex.

FiniteSublevels birth:
  for every time r, some finite list contains every x with birth(x) <= r.
```

`infiniteVertices_iff_not_finiteCover` proves that the first condition is
equivalent to the absence of a finite list cover of the whole type. Finite
lists may contain duplicates or additional vertices; neither concession
weakens the finite-cover condition.

`BirthOrder.orderedEnumeration birth infinite finite` constructs an
`OrderedEnumeration birth` with these fields:

| Field | Meaning |
| --- | --- |
| `toFun : Nat -> V` | The constructed enumeration. |
| `injective` | Distinct indices name distinct vertices. |
| `surjective` | Every vertex appears at an index. |
| `nondecreasing` | `i <= j` implies `birth(toFun i) <= birth(toFun j)`. |

`BirthOrder.orderedEnumeration_exists` exports existence of that complete
record from the stated hypotheses. The later transport lemmas accept the
record, but its construction is proved in this module, not supplied as an
unverified interface assumption.

## Why the enumeration exists

`exists_least` first proves that every nonempty subset of vertices has a member
of least birthdate. Pick any member `a`. A finite sublevel through `birth a`
contains `a` and every potentially earlier member. An induction over that
finite list selects a minimum among members of the subset. Totality of the
time comparison makes that minimum global. This step derives the needed
minimum property from local finiteness rather than assuming a well-order on
time.

At stage `n`, the construction chooses a vertex of least birthdate outside
the finite list of previously chosen vertices. Infinitude supplies a remaining
vertex. Classical choice resolves the selection, including ties. The first
`n` choices form a list of length `n` with no duplicates. These facts prove
injectivity and monotonicity of birthdates.

For surjectivity, suppose a vertex `x` were never selected. Every selected
vertex would then have birthdate at most `birth x`, because `x` would remain
available at every stage. If `L` is a finite list covering that sublevel, the
first `L.length + 1` choices would be distinct members of `L`. The proved
finite-list cardinal inequality makes this impossible. Thus no vertex is
missed.

The resulting enumeration is **noncomputable**: it is an existence theorem
using `Classical.choice`, not an effective algorithm from arbitrary real
birthdates or an unspecified vertex presentation.

## Tied dates and strict edge order

Different vertices may have equal birthdates. Finite sublevels already force
each tied-date group to be finite, and choosing one member at a time resolves
these groups without identifying vertices.

For an enumeration `e`, `e.index x` is its proved inverse. The identities
`e.toFun_index x` and `e.index_toFun n` establish both inverse directions.
When the time type additionally has `LT Time` and `Std.LawfulOrderLT Time`,
`e.index_strict` proves:

```text
birth x < birth y  ->  e.index x < e.index y.
```

`e.edges_increase` consequently transfers any edge relation whose parents have
strictly earlier dates to one with strictly increasing natural indices. For a
labelled relation, use the proposition that some labelled edge is present.
Labels and adjacency are preserved by the bijection; the proof does not
replace the graph with a different construction.

## Finite roots and children

Finite root and child sets are not needed to construct the enumeration. They
are separate population assumptions, and the module provides their transfer:

- `e.pullback_cover` maps a finite vertex cover `xs` to the explicit index cover
  `xs.map e.index`, whose list length is unchanged.
- `e.finiteCover_pullback_iff` proves that a vertex set is finite exactly when
  its set of indices is finite.
- `e.finiteCover_pullback_bound` supplies a natural bound beyond every index
  in a given finite vertex set.

Apply the last lemma to the root predicate for a global root-support bound,
and separately to each vertex's child predicate for its child-support bound.
Together with `edges_increase`, these are the ordering and support ingredients
needed by `PopulationCounting.InfiniteLabeledPopulation`. This module does not
silently assert a uniform child cap from mere finiteness; a uniform cap remains
a separate hypothesis of the subcritical degree theorem.

## Strict sublevels and actual real numbers

The core endpoint uses finite sublevels `birth x <= r`. The theorem
`finiteSublevels_of_strict` proves that finite strict sublevels suffice whenever
every time has a strictly larger time. For real times, `r + 1` is such a larger
bound. This handles the strict-sublevel convention without assuming that tied
birthdates are absent.

The installed standard library provides `Std.IsLinearPreorder` and the finite
list machinery used here, but no `Real` type. Accordingly this core module
does **not** rename an abstract ordered type as the reals, construct a real
field, or claim that its own successful build verifies a literal `Real`
instantiation. The coordinating task owns the optional `real/` subproject,
with Mathlib pinned for the same Lean version. Its adapter must provide the
standard real-order instances and translate ordinary finite-sublevel and
infinite-type hypotheses into the displayed list-cover predicates. The
substantive enumeration, tie handling, inverse, and edge-order argument are
already checked here and need no new enumeration premise in that adapter.

Any report claiming a literal real-date theorem must cite the optional
subproject's actual statement and successful build as well as this core
module. Neither the real dependency nor its compiler receipt is implied by
the core build alone.

## Verification

From the repository root:

```powershell
$env:ELAN_HOME = 'C:\Users\Owner\.elan'
& 'C:\Users\Owner\.elan\bin\lake.exe' build SamuelAlexanderResearch.BirthOrder
```

This command was verified with exit code `0` under Lean `4.33.1`. The eleven
`#print axioms` checks cover the minimum construction, injectivity,
surjectivity, monotonicity, ordered enumeration, inverse, finite-set transport,
strict index and edge transfer, and strict-sublevel conversion. Dependencies
are subsets of `propext`, `Classical.choice`, and `Quot.sound`; the strict
sublevel conversion uses no axioms. There are no project axioms, `sorry`,
`admit`, or `native_decide` proofs.
