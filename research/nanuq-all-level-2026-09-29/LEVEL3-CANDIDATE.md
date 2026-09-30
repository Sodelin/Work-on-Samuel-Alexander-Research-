# Level-three NANUQ: candidate computer-assisted proof

Date: 29 September 2026. Status: candidate argument awaiting independent
structural review; no Lean theorem, external review, publication or priority
claim. The exact program has finished. Source coverage is the remaining review
target, rather than an assumption silently supplied by the program.

## External target

Holtgrefe et al., *Distinguishing Phylogenetic Level-2 Networks with Quartets
and Inter-Taxon Quartet Distances*, Bulletin of Mathematical Biology 87:168
(2025), Section 6, explicitly conjecture circular decomposability for
outer-labeled planar, galled, level-3 bloblet networks.
https://doi.org/10.1007/s11538-025-01549-4

This note targets precisely that statement for the binary semi-directed LSA
class and at least four taxa. It does not assert a level-three canonical-form
classification, statistical consistency, or an arbitrary-level theorem.

## Proposed reduction to two families

Take a strictly level-three bloblet and its nontrivial blob. Remove its pendant
taxon edges and suppress vertices of degree two. The resulting multigraph H
is connected, bridgeless and cubic, and has cycle rank three. Writing V,E for
its vertex and edge counts gives 3V=2E and E-V+1=3; hence V=4 and E=6.
Loops cannot occur: a cubic vertex with a loop has only one other incident
edge, which would be a bridge in a connected graph with other vertices.

A loopless connected bridgeless cubic multigraph on four vertices is either
K4 or a four-cycle with two opposite edges doubled. To see completeness,
if it is simple it must be K4. If uv is doubled, u and v each have one unused
incidence. Their remaining neighbors cannot both be the same third vertex
without creating a bridge or violating the fourth vertex's degree. They must
therefore meet different remaining vertices, whose other two incidences form
the second doubled edge. A triple edge would disconnect the remaining two
vertices. `core_inventory` independently enumerates all edge multiplicities
and obtains exactly these two isomorphism classes.

In a binary galled bloblet, each hybrid has a pendant taxon child. It therefore
occurs as a degree-two vertex on a side of H before suppression. No side can
contain two hybrids: any cycle through the two incoming edges of either one
would have to follow the whole degree-two path and include the other hybrid's
edges, contradicting the galled condition. Thus the three hybrids mark three
distinct sides. All marked sides must belong to the outer face, because their
pendant taxa belong to that face. Ordinary taxon attachments likewise occur
only on sides incident to the outer face.

Deleting the hybrid nodes and their incoming edges leaves the root skeleton
tree, with ordinary taxon branches. After suppressing those branches, the
unmarked sides of H must form a spanning tree on its four vertices. This is
also necessary for a rooted partner: each remaining tree node must be reached
from the root without descending through a hybrid, since each hybrid's only
descendant in a bloblet is its pendant taxon.

For K4 every face is triangular. All three sides of the chosen outer face
are marked, and the unmarked sides form the three spokes to the fourth vertex.
The hybrid vertices divide the outer boundary into six ordinary-leaf segments.

For the doubled four-cycle, the faces are two bigons and two quadrilaterals.
A bigon cannot contain three distinct marked sides, so the outer face is a
quadrilateral. Of its four sides, exactly three are marked. The unmarked outer
side must be a single connecting side: leaving an outer member of a doubled
pair unmarked would leave that pair as a cycle and the unmarked subgraph
disconnected. Up to symmetry there is one choice. The outer boundary has six
segments incident to hybrids and one unmarked segment, for seven ordinary-leaf
segments in total.

The two constructors implement these six- and seven-segment families. Every
generated example passes explicit checks for binary degrees, a rooted acyclic
partner, root LSA, a planar rotation system with all taxa on one face, three
hybrids in the blob, and the galled condition. The above argument, rather than
these example checks, is what must establish completeness.

## Six-witness compression

Use the same anchor matrix M^{pq} as the level-two argument: its diagonal is
zero; an off-diagonal entry is zero for the pair {p,q}, one when exactly one
endpoint is an anchor, and otherwise twice the uniform distinct-quartet
cherry-separation score on its two endpoints and the two anchors.

One boundary coefficient of M^{pq} uses at most six named taxa: two anchors
and four labels adjacent to the circular split boundaries. Retain these taxa
and all three hybrid taxa. Delete all other ordinary pendant taxa and suppress
their now-degree-two parent vertices along the seven or six boundary segments.
The reduced object is in the same family and has at most six ordinary taxa,
plus the three hybrid taxa, hence at most nine total taxa.

For each of the eight hybrid switchings, shortening an ordinary segment
preserves the displayed tree restricted to retained taxa. Consequently it
preserves the SET of distinct quartets used by the coefficient. It also
preserves the two boundary adjacencies, because both endpoints of each original
boundary gap were retained. The anchor identities and all four matrix entries
therefore agree before and after compression. The tested coefficient agrees.

The zero-ordinary-leaf cases have three taxa. They are included as residual
anchor cases; the conjecture itself requires at least four taxa.

## Exact certificate and assembly

`level3-screen-6.json` records:

| Family | Templates | Unit-distance coefficients | Anchor coefficients |
|---|---:|---:|---:|
| K4 core, six segments | 924 | 27,423 | 866,811 |
| Doubled four-cycle, seven segments | 1,716 | 52,195 | 1,674,283 |
| Total | 2,640 | 79,618 | 2,541,094 |

Every checked coefficient is nonnegative. All unit-distance supports in this
finite list also match displayed-tree support, but no universal support
theorem is claimed here from those finite support comparisons alone.

For arbitrary size in either family, six-witness compression transfers every
anchor coefficient to a checked one. The identity

    d_N = sum_{unordered anchor pairs {p,q}} M^{pq}

holds entrywise: anchor pairs containing exactly one of x,y contribute 2n-4,
and anchor pairs disjoint from x,y contribute the NANUQ quartet sum. Circular
coefficients are linear, so all coefficients of d_N are nonnegative. The
circular reconstruction identity gives a nonnegative split decomposition.
Moreover d_N(x,y) >= 2n-4 > 0 for distinct taxa, and the decomposition gives
the triangle inequality. Lower-level bloblets are covered by the existing
level-at-most-two theorem and the level-one weighted-tree argument.

If the structural classification and compression above survive independent
review, this is a computer-assisted proof of the stated level-three bloblet
conjecture. At present that review is pending; the computational certificate
uses Python exact rationals, not a Lean kernel certificate.

## Scope and next decision

The finite checker is a local research copy of the existing exact backend,
with the level admission limit changed from two to three. Its source hash and
the parent hash are recorded. Thus this run is not an independent implementation.
It must not be marketed as multiple independent confirmations.

The immediate next action is one adversarial review of the two-family coverage
and the finite reduction. Full Lean implementation and an extension to multiple
blobs should follow only if that review accepts the mathematical argument.
No all-level claim follows automatically.
