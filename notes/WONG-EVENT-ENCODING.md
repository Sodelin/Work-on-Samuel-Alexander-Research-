# Ordered event edges encoded as genome intervals

This module formalizes the deterministic event-edge conversion described in
Wong et al. (2024), **Event ARGs, printed journal pp. 2–3**, and
**Ancestral material and sample resolution, pp. 3–4**.
[Published source](https://www.pure.ed.ac.uk/ws/portalfiles/portal/458588307/iyae100.pdf);
[DOI](https://doi.org/10.1093/genetics/iyae100).

**Status:** [WongEventEncoding.lean](../real/WongEventEncoding.lean) passed the
root task's serialized Lean compiler check on 25 September 2026: exit code 0,
all 10 selected endpoints printed, and only permitted standard axioms reported.
The corrected source SHA-256 is
6FDDE306BBDAB6F5E349127D634251988CD81E977B0ECA63F114F187CE7ECB87.
An independent project-agent mathematical/API review also passed. These are
standalone checks; final aggregate audit and public-commit CI are separate
integration evidence. This is an attributed formalization of the paper's
conversion, not a newly solved open problem.

## Input and construction

The input is a finite acyclic graph whose node specification is one of:

| Specification | Encoded inheritance |
|---|---|
| Root | No parent edge. |
| Single parent p | One record carrying the full coordinate interval from lo, inclusive, to hi, exclusive. |
| Ordered crossover with parents a and b and cut | Parent a supplies the left interval from lo to cut; parent b supplies the right interval from cut to hi. |

The common coordinate type can be any linear order. The genome span is
nonempty, and crossover points satisfy strict lo < cut < hi. Thus the left
branch has the witness lo and the right branch has the witness cut.
The first crossover parent always supplies the left interval. The source
explicitly needs this convention or equivalent metadata; a breakpoint alone
does not decide which parent to follow.

The module builds actual finite interval records and a
WongGARG.GARG value, carrying an arbitrary supplied sample subset unchanged.
Acyclicity follows from exact topology correspondence with the input.
The encoded local relation has at most one parent at each position, even
though the whole graph may have two parents at a crossover.

The graph edges are ancestor-to-descendant. The parent-routing function is
followed in the reverse direction when reading a history rootwards. The
formal path equivalence compares the same ancestor-to-descendant relation
on both sides, so it does not silently reverse reachability.

## Exact exported statements

| Declaration | Conclusion |
|---|---|
| ParentSpec.parent_iff_exists_at | An event parent appears at some genomic position, and every position-specific parent is an event parent. Strict interior cut assumptions prevent invisible empty branches. |
| EventGraph.encoded_topology | The constructed gARG has exactly the event-parent topology. |
| EventGraph.encoded_atLocus | Its inheritance at every position is exactly the full-span or ordered half-interval specification. |
| EventGraph.encoded_nonempty_annotations | Every generated record contains a nonempty, proper interval. |
| EventGraph.encoded_unique_parent | The constructed gARG has unique local parenthood at every coordinate. |
| EventGraph.encoded_route | At an in-domain position, an encoded edge exists exactly when the event's routing function selects that parent. |
| EventGraph.encoded_path_iff | Every finite path at a fixed in-domain locus agrees in the interval graph and the ordered routing relation, in both directions. |
| EventGraph.erased_encoded_topology | Erasing interval positions recovers exactly the original event-parent topology. |
| EventGraph.encoded_parent_pointer | The existing WongGARG localParent representation selects exactly the same parents as the event routing rule. |
| ParentSpec.crossover_cut_identified | With fixed ordered **distinct** parents and the same span, equality of the full in-span local relation forces equality of the two interior crossover cutoffs. |

The routing function's name routeInside makes its domain convention visible.
Route theorems require a position in the half-open genome span. Encoded
inheritance itself is empty outside that span. The representation is
noncomputable because the generic coordinate and finite-set interface uses
classical decisions; no practical parser, evaluator or runtime complexity
claim follows from these statements.

## Boundaries that matter to source fidelity

SingleParent describes only a node's parent relation. It may stand for a
sample, a pass-through node or a common-ancestor event. The module does not
enforce two children for each coalescence node or one child for each
recombination node. Classical binary event ARGs fit this parent specification
when their additional child-arity conditions hold; the accepted input class
is broader.

The two crossover parents are not required to be distinct in this permissive
interface. With equal parent identities the encoding still satisfies its
semantics, but it can produce two adjacent records for the same parent-child
pair. No CanonicalRecords theorem or interval-normalization theorem is
claimed. A stricter classical-event adapter can add distinct parenthood and
the binary child-arity conditions.

The equivalence is exact for topology, local interval inheritance and
routing paths. One bounded identifiability result is also proved in the source:
if the ordered parent identities are fixed and distinct, the full local
relation determines the interior crossover cutoff. If two cutoffs differed,
at the smaller cutoff one description would already select the right parent
while the other still selected the left. The distinctness hypothesis is
essential; when the parents coincide the local relation can hide the cutoff.

These restricted identifiability conditions do not supply a general decoder.
The encoding is **not** a proof that arbitrary serialized gARG records
decode to a unique event history. Event kinds, event times and interval
segmentation metadata are not recovered. Any claimed storage round trip
needs an explicit retained event datatype, canonical serialization and
decoding function.

This conversion precedes sample restriction and simplification. It neither
removes unsupported ancestral material nor suppresses unary nodes or
diamonds. A sample need not reach every raw edge. The
[ancestral-restriction note](WONG-ALEXANDER-BRIDGE-STATUS.md) states the exact
support condition for later sample-based recovery.

Nothing here formalizes stochastic coalescent rates, likelihoods, event-count
asymptotics, ARG inference from DNA data, or a biological owner assignment.
Those require the additional models identified in the
[source coverage audit](WONG-ALEXANDER-BRIDGE-STATUS.md).
