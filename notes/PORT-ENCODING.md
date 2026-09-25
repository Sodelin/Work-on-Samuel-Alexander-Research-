# Actual critical populations as finite port schedules

The implementation is in [`real/PortEncoding.lean`](../real/PortEncoding.lean),
in the optional Mathlib project. It imports the unchanged core definitions of
`PopulationCounting.InfiniteLabeledPopulation` and `PortDynamics.Schedule`,
`Legal`, `Fair`, `run`, and `DecodedEdge`.

The input is an actual `InfiniteLabeledPopulation k k`: naturally ordered
vertices, a functional `Option Nat` edge label, strict chronological edges,
finite root support, every required label below `k` at every nonroot, and
finite child supports with cap `k`. There is no supplied enumeration of
crossing edges, port assignment, regular tail, fairness condition, or
aggregate conservation premise. Mathlib is used for finite cardinalities and
finite type bijections; the population and decoder models remain the existing
core models.

## Construction

`InfiniteConservation.eventual_structure` supplies a root-free tail on which
every full indegree and full outdegree is exactly `k`. Label coverage maps
`Fin k` into the actual incoming parents. Functionality of edge labels makes
that map injective; equality of finite cardinalities makes it surjective.
Consequently every actual incoming edge at a tail vertex has a label below
`k`, including an edge whose source precedes the tail base. This step is
necessary because the input population structure does not separately forbid
extra labels.

A cut immediately before birth `b` consists of actual pairs `(u,v)` satisfying
`u < b ≤ v` and having an edge. It is finite: there are finitely many sources
below `b`, and each has a finite child support. The slots at the initial cut
are `Fin C`, where `C` is that actual cut's cardinality.

At each birth, an equivalence between the `k` incoming edges and `k` outgoing
edges replaces the consumed edges in their existing slots. All other slots
keep exactly their actual edge. Recursion gives a bijection between the same
`Fin C` and every subsequent actual cut. A slot is selected precisely when
its stored edge targets the current birth. Its replacement label is the label
of its new actual edge. The initial token records the source and label of its
initial actual edge.

The decoder's token evolution is proved equal to the source and label of
these stored actual edges. Thus the legal input map is obtained from the
unique incoming edge of each label. Simplicity follows because two selected
edges with the same source and current target are the same edge and hence the
same slot. Fairness follows from the finite target of any currently stored
edge: it stays in its slot until that target is born, when the slot is
selected.

## Exact scope

Exact decoding is asserted for all edges whose **target** is at or beyond the
chosen base; the source may be earlier. This includes the initial crossing
edges. The decoder has no births before the base, so no claim identifies it
with the complete pre-base graph.

The construction works for every natural `k`, including the empty-label
case. It does not establish that an arbitrary resulting schedule is periodic,
nor that arbitrary critical populations are universal. Any application of
the existing periodic-schedule universality theorem must establish its
periodicity hypothesis separately. Choosing finite bijections is classical;
this is an existence theorem, not an effective algorithm from an oracle for
an infinite graph.

This is a formal model adapter, with no novelty or priority claim.

## Verification

The main endpoint is `PortEncoding.eventual_encoding`. Its only population
argument is `p : InfiniteLabeledPopulation k k`. It returns a base at or beyond
the root support, the actual initial cut cardinality `C`, a schedule `S`, and
initial tokens, with:

- a constructed value of `PortDynamics.Legal S base init` (the theorem records
  its existence using `Nonempty`, since `Legal` carries an input map and is a
  data structure);
- `PortDynamics.Fair S`;
- the exact edge equivalence for every target `v ≥ base` and every `a : Fin k`;
- validity below `k` of every actual natural-number label on that target tail.

The construction-level endpoints are `encoding_legal`, `encoding_fair`,
`encoding_exact`, `tail_label_lt`, and `cut_width_constant`. Their `Regular`
argument packages the exact root-free degrees needed to construct a schedule;
`eventual_encoding` discharges that argument from the original population
using `eventual_structure`. `cut_width_constant` also states directly that the
actual finite cuts on this tail all have the same cardinality.

`encoded_periodic_realizes` transports the existing periodic-schedule theorem
to strict paths of actual edges, starting within one period of the periodic
tail. Its hypothesis that the constructed schedule is periodic is explicit;
the unconditional encoder does not establish it.

On 2026-09-25, the development check passed, followed by a fresh standalone
Lean compilation with no snapshot loading. From `real/`, the final command was:

```powershell
$env:ELAN_HOME='C:\Users\Owner\.elan'
& 'C:\Users\Owner\.elan\bin\lake.exe' env lean `
  -o .lake/build/lib/lean/PortEncoding.olean `
  -i .lake/build/lib/lean/PortEncoding.ilean PortEncoding.lean
```

It exited with code 0 and no warnings. Axiom prints for `eventual_encoding`,
`encoding_exact`, `encoding_fair`, and `encoded_periodic_realizes` contain only
`propext`, `Classical.choice`, and `Quot.sound`. The source contains no `sorry`,
custom axiom declaration, or `native_decide`. The emitted module is available
to the optional project's integration and independent audit; this lane did
not change the existing library configuration or aggregate audit files.
