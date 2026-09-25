# Exact fixed-source-gender child-cap threshold

The threshold is **two**. The Lean endpoint
`CapTwo.avoiding_population_exists_iff cap s` proves

```math
\begin{split}
&\exists E,S,g,\quad
  \operatorname{FixedGenderPopulation}(E,S,g,\mathrm{cap})
  \ \land\ \neg\operatorname{RealizesOn}(E,S,g,s)\\
&\hspace{3em}\Longleftrightarrow\quad
  2\le\mathrm{cap}\ \land\ \neg\operatorname{EventuallyPeriodic}(s).
\end{split}
```

This uses the existing actual population and path predicates. It is not a
finite-search observation, a degree-inequality premise, or a conditional
compactness statement. No experiment was needed.

## Construction: vertices are original edges

Start with the already formalized edge-labelled avoiding population `P_s`.
Its vertices are natural numbers, its roots are 0 and 1, and its actual edges
into each `w >= 2` are

- `w-1 -> w`, with label `row s w`;
- `w-2 -> w`, with label `!(row s w)`.

Make each original edge a new vertex, give it the permanent gender equal to
its original edge label, and join two new vertices exactly when the original
edges are consecutive. This is the directed line graph. Different original
edges with the same source remain distinct vertices, even if their genders
agree; this is what removes the older gender-copy construction's three-child
bottleneck.

The explicit natural-number encoding uses positive ports `x >= 1`:

```math
\operatorname{source}(x)=\lfloor x/2\rfloor,
\qquad
\operatorname{target}(x)=\lfloor x/2\rfloor+1+(x\bmod2).
```

An even port represents the original one-step edge and an odd port represents
the original two-step edge. Port 0 would represent `0 -> 1`, which is not an
edge of `P_s`, so it is excluded from the retained vertex set. A new edge
`Arc x y` requires both ports to be retained and
`source y = target x`.

The gender of `x` is `row s (target x)` for an even port and its Boolean
complement for an odd port. This is a fixed property of `x`, independent of
which child is chosen. The underlying graph and retained set are the same
for every target; only these permanent genders depend on `s`.

## Checked population data

`CapTwo.fixedGenderPopulation` proves every field of the existing
`FixedGenderLift.FixedGenderPopulation` definition:

- infinitely many retained vertices;
- strictly increasing natural birthdates along edges;
- finitely many vertices born before each natural date;
- finitely many actual induced roots;
- an actual finite child cover of length at most two;
- a parent of each Boolean gender at every actual nonroot.

There are exactly **three** roots, the ports 1, 2, and 3 representing
`0 -> 2`, `1 -> 2`, and `1 -> 3`. `roots_exactly` states the iff for retained
vertices and actual induced roothood; excluded port 0 is never counted as a
population vertex.

Every vertex has exactly two distinct children, not merely at most two.
For a port with target `v`, those children are ports `2*v` and `2*v+1`.
The fact `v >= 2` guarantees that both are actual retained ports.
`children_exactly` and `exactly_two_children` prove this exact geometry.

At a nonroot port with source `u >= 2`, its only parents are ports `2*u-2`
and `2*u-3`, representing `(u-1) -> u` and `(u-2) -> u`.
`parents_exactly` proves the edge iff; `incoming_gender` derives both
required genders from the original graph's proved incoming-label theorem.
Consequently there are no terminal vertices and no infinite collection of
degree defects hidden in this construction.

## Exact preservation of words

`port_edge` proves that every retained port is an actual original edge with
the declared label. `edge_port` proves the converse representation.

For every pair of Boolean words `s` and `word`, `realizes_iff` proves

```math
\operatorname{RealizesOn}(\mathrm{Arc},\mathrm{Vertices},g_s,\mathrm{word})
\quad\Longleftrightarrow\quad
\operatorname{Realizes}(P_s,\mathrm{word}).
```

Projection sends a new path `x(k)` to `source(x(k))`. Lifting sends an
original path to its successive original edges. Both directions preserve
the target word and step index exactly: there is no reversal, discarded
initial letter, or time shift.

`avoids_aperiodic` therefore applies the existing checked avoidance theorem
for `P_s`. `cap_two_avoider` packages the actual cap-two population, exact
two-child property, exact three-root set, and avoidance. The old cap-three
construction remains valid, but is no longer the best uniform child bound.

## Lower bound and complete threshold

`CapTwo.presented` translates any population in the existing retained
fixed-gender model into a `PopulationReindex.PresentedPopulation` on the
actual retained subtype. It assigns a functional numeric edge label equal
to the source gender, preserves actual roothood in both directions, and
transfers the original child-cover list without increasing its length.
The enumeration and aggregate counts are derived by the previously checked
transport and counting modules.

`fixedGender_subcritical_impossible` invokes the proved subcritical graph
count for every `cap < 2`. In particular, `fixedGender_cap_one_impossible`
rules out an infinite population satisfying these binary-parent axioms with
a one-child cap, independently of the target word.

The positive direction for eventually periodic words comes from the existing
unconditional `FixedGenderReindex.eventuallyPeriodic_realized` theorem.
Together these facts prove `avoiding_population_exists_iff` above and
`fixedGender_cap_two_classification`, which states that a word is realized
in every actual cap-two fixed-gender population iff it is eventually
periodic. The universal statement below cap two is vacuous because no such
population exists.

## Boundaries

The explicit witness uses three roots. This module does not claim that three
is the smallest root count for avoidance at cap two. It does not export a
specieslike or inspecies theorem internally; the separate
[CapTwoSpecies module](CAP-TWO-SPECIES.md) now proves both for this same witness.
A general abstract line-graph conversion theorem and a crossing-count
computation are not exported here. The exact
two-parent/two-child geometry and three roots imply crossing width six after
the roots by the already established conservation principle; this explanatory
deduction is not an additional endpoint of this module. In particular, the
construction is consistent with the proved unavoidability at minimum binary
crossing width three.

The source avoiding population and its row formula are attributed to the
[September 2026 classification manuscript, Section 2](https://github.com/avg-netizen/biological-unavoidability/blob/3d6175e3e23f67bd68e7be591b5a9a6d04e496a3/paper.md#2-an-explicit-binary-avoiding-population).
The directed-line-graph deduction is established here without a claim of
novelty in the wider literature.

## Verification

From the repository root, with `ELAN_HOME=C:/Users/Owner/.elan`:

```text
lake env lean lean/SamuelAlexanderResearch/CapTwo.lean
lake build SamuelAlexanderResearch.CapTwo
```

Both checks pass. The printed endpoints use only the standard axioms
`propext`, `Classical.choice`, and `Quot.sound` (some use a subset). The module
contains no `sorry`, `admit`, custom `axiom`, or `native_decide`.
