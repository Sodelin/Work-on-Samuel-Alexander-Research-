# A uniform finite certificate for NANUQ circularity

Date: 29 September 2026. Status: the structural reduction, finite certificate,
original-NANUQ composition, exact split-support transfer, and symbolic parameter domain have passed separate
internal audits. Two different implementations checked the finite calculation.
This is a computer-assisted mathematical proof package, not a complete Lean
formalization or an externally peer-reviewed result. Historical priority has
not been established by an exhaustive literature search.

## Precise claim

**Theorem A (original NANUQ, arbitrary level and multiple blobs).** For every
finite binary semi-directed LSA phylogenetic network that is outer-labeled
planar and galled, with at least four taxa, its original NANUQ distance is
circular decomposable in the order induced by any chosen outer-labeled planar
embedding, with support exactly the union of the split sets of its displayed
trees. There is no upper bound on its reticulation level or number of blobs.

**Theorem B (local parameter family).** On bloblets in the same class, define
the displayed-quartet score extension in Section 6. Every score vector

    (c,s,a,o) with s=o=1, 1/2 <= a <= 1, and 0 <= c <= a

gives a circular decomposable distance at every finite level. Every two-anchor
matrix has nonnegative circular coefficients, so arbitrary nonnegative sums of
these anchor matrices, including positive port-mass weightings, are circular
as well. The displayed domain is exact for this universal anchor-positivity
criterion on adjacent-copy plane trees. Necessity for unweighted source-network
distances is not claimed.

Theorem A answers and strengthens the explicit level-three bloblet circularity
question in Section 6 of Holtgrefe et al., DOI 10.1007/s11538-025-01549-4.
Theorem B gives a concrete affirmative answer to that section's separate
parameter-family extension question. Theorem A proves the proposed extension
of Theorem 4.7 to multiple blobs, including its exact displayed-split support
claim, and removes the level bound within the same structural class. Neither
theorem asserts circularity for unrestricted networks or recovery of every
network from its distances.

## 1. Open pendant hybrids into paired tree tips

Fix an outer-labeled planar embedding. In a binary galled bloblet every hybrid
has a pendant taxon child. Remove that hybrid and its child, and replace the
two incoming incidences with two leaf tips carrying copies of that taxon's
label. Keep ordinary taxon leaves. Suppress a degree-two root if one is present.

The result T is a plane binary tree. Indeed, the remaining tree nodes are all
connected to the root through tree edges: a root-to-tree-node path cannot pass
through a hybrid whose only descendant is its pendant taxon. Their rooted
subgraph has no directed cycle and each non-root vertex has one incoming tree
edge, so its undirected graph is a tree. Adding opened tips preserves this.

**Paired-tip lemma.** The two tips carrying any duplicated label are adjacent
in T's cyclic leaf order.

Inside its nontrivial blob every hybrid
has degree two, lies on the outer face, and has its two blob edges incident to
exactly one bounded face. To justify facial cycles, a bridgeless graph of
maximum degree three has no cut vertex: two components at a cut vertex would
each need at least two incident edges to avoid a bridge, requiring degree at
least four. Thus a nontrivial binary blob is 2-connected, allowing bigons.
If there are k hybrids, Euler's formula gives k
bounded faces. Each bounded face contains a hybrid, since an all-tree-edge
boundary would be a cycle in the root-skeleton tree. Counting the k hybrid
incidences therefore shows that every bounded face contains exactly one hybrid.
After opening that hybrid, the bounded-face side gives a tree contour interval
between its two opened tips. It contains no ordinary taxon (all were outside)
and no other opened hybrid tip (the bounded face contained no other hybrid).
Thus these tips are consecutive. Tracing the original outer-face contour,
each hybrid-taxon excursion is replaced in place by these two tips and their
tip-free detour. Collapsing each pair therefore recovers the original taxon
order, up to rotation and reversal. Parallel edges and two-sided faces are
allowed; their opened tips can be a cherry in T.

This is an embedding statement, not a conclusion inferred from the finite
enumeration. The separate structural audit supplies the full contour and
connected-root-skeleton arguments. A tree bloblet is the zero-duplication case.

## 2. Switching semantics

Every hybrid switching keeps one of that hybrid's two incoming edges. On T,
this is exactly the operation of selecting one of the two copies of each
duplicated taxon, pruning the other copy, and suppressing vertices of degree
two. Choices for different labels are independent. Thus displayed quartets
are the union of the quartet topologies obtained by these copy selections.
We always deduplicate topologies; switching multiplicities do not enter rho.

For a fixed edge split A|B of T, a quartet ab|cd is displayed by some selection
if A contains a copy of each of a,b and B contains a copy of each of c,d, or
the reverse. These four choices are consistent because the labels are
distinct, and extend to all other labels arbitrarily. Conversely a displayed
quartet in a selected tree has an edge inducing it, inherited from T. This
proves the exact split-witness formula used by the finite enumeration.

## 3. Six taxa suffice, independent of k

For anchors p != q define M^{pq}(x,x)=0, and for distinct x,y define its entry
as 0 if {x,y}={p,q}, as 1 if exactly one endpoint is an anchor, and otherwise
as 2 rho(x,y;p,q). Here rho is the proportion of distinct displayed quartet
topologies that separate x and y.

A circular boundary coefficient has form

    M(a,c) + M(b,d) - M(a,d) - M(b,c),

where (a,b) and (c,d) are two boundary-adjacent pairs in the taxon order. It
therefore depends on at most six taxon labels, including the two anchors.
There are at least three distinct labels; the six can overlap.

Keep in T every copy of these retained labels and delete every other tip.
Take the spanning subtree and suppress degree-two vertices. The resulting
plane binary tree has at most six labels, each occurring once or twice, so
at most twelve tips. Each duplicated label is still adjacent to its mate.
The two original boundary gaps remain adjacent because both endpoints were
kept. Restriction of a tree is associative, so selecting copies and restricting
to a queried quartet commute with deleting the unused labels. The exact
displayed quartet sets, and hence all four entries of the coefficient, agree.

This caps the *retained labels*, not the original network level. A blob with
arbitrarily many hybrid taxa is reduced by deleting both copies of every
unneeded hybrid taxon. No requirement to retain all original hybrids remains.

## 4. Exhaustive finite certificate

For r in {3,4,5,6}, arrange labels 0,...,r-1 cyclically. For each of the 2^r
duplication masks, replace every doubled label by two adjacent tips. If there
are m expanded tips, all plane binary trees with this fixed order are the
Catalan(m-2) trees obtained by rooting at expanded tip zero and recursively
splitting the remaining interval into two nonempty consecutive intervals.

For each interval I, precompute its bitset of quartet topologies witnessed by
the associated tree edge, using the split-witness rule from Section 2. The
bitset of a tree is the bitwise union of its edge contributions. Dynamic
programming over every possible interval split enumerates these bitsets.
Keeping one representative of each bitset is exact: its future contribution
depends only on that bitset and the fixed parent interval. This does not
require all displayed quartets to occur in a single switching.

The current exact Python receipt `all-level-screen.json` reports:

| Retained taxa | Duplication masks | Plane trees represented | Distinct quartet systems | Anchor coefficients |
|---|---:|---:|---:|---:|
| 3 | 8 | 36 | 1 | 9 |
| 4 | 16 | 406 | 3 | 108 |
| 5 | 32 | 5,390 | 16 | 1,600 |
| 6 | 64 | 78,244 | 102 | 22,950 |
| Total | 120 | 84,076 | 122 | 24,667 |

All coefficients are nonnegative. For each quartet the only observed topology
codes are the first circular split, the second circular split, or both. Thus
rho is in {0,1/2,1}, anchor entries are integers, and the implemented division
is exact. The independent verifier confirms both coverage and arithmetic: it
explicitly generates every ordered plane tree, builds its graph, and classifies
11,848,859 physical-copy quartets by the tree four-point condition. It recovers
the same 122 systems and 24,667 nonnegative coefficients. Its methods and limits
are in `ALL-LEVEL-FINITE-AUDIT.md`; the structural proof is in
`ALL-LEVEL-STRUCTURAL-AUDIT.md`.
These are combinatorial tree/duplication instances, not 84,076 distinct
isomorphism classes of phylogenetic networks.

## 5. Deduction of the unbounded local theorem

By Sections 1-3, a negative anchor coefficient on any source bloblet, at any
level and any taxon count, would give a negative coefficient in Section 4.
The finite certificate excludes this. Therefore all anchor coefficients are
nonnegative in the circular order induced by the network embedding.

Entrywise, for distinct x,y,

    d_N(x,y) = sum_{unordered {p,q}} M^{pq}(x,y).

Pairs containing exactly one of x,y contribute 2n-4. Disjoint pairs contribute
the defining NANUQ quartet sum. Linearity of circular coefficients therefore
gives nonnegative coefficients for d_N. Circular reconstruction writes

    d_N = (1/2) sum_{circular gap pairs i<j} alpha_ij(d_N) delta_ij.

This identity holds for every symmetric zero-diagonal matrix, so no metric
assumption is being used to prove itself. All its split weights are nonnegative.
Since d_N(x,y) >= 2n-4 > 0 for
distinct taxa, it is a metric as well as circular decomposable.

More generally, for nonnegative port masses m,

    W_N(m) = sum_{unordered {p,q}} m(p)m(q) M^{pq}

is a nonnegative circular split sum. For positive masses and at least three
ports it separates distinct ports. A two-port local matrix is zero. This
weighted statement is what a multiple-blob composition proof needs.

## 6. The exact two-dimensional anchor-positivity domain

NANUQ+ (Allman et al., DOI 10.1186/s13015-025-00274-w, Definition 3.1)
introduces four scores (rho_c,rho_s,rho_a,rho_o) for a single displayed quartet
with the queried pair in a cherry or separated, and a two-topology quartet
with the queried pair adjacent or opposite in the circular order. We extend
this rule to the present class using its distinct displayed quartet sets.
It agrees with that definition on level-one networks.

Keep the exceptional anchor entries 0 and 1 from Section 3. For four distinct
labels, replace the entry by 2c, 2s, 2a, or 2o according to those four cases.
Each circular coefficient is an integer linear form in (1,c,s,a,o).
`parameter_domain.py` extracts every such form from the finite systems.
The independent symbolic checker uses the previously verified systems and a
different direct cyclic-adjacency classifier, without importing that program.

Across 24,667 coefficients, 9,931 are identically zero. Dividing each nonzero
coefficient by the positive greatest common divisor of its entries gives
exactly these 16 inequalities:

    o-1 >= 0, s-1 >= 0, a-c >= 0, s-c >= 0,
    o-s >= 0, 2a-s >= 0, a >= 0, s-a >= 0,
    s-o >= 0, s >= 0, c >= 0, 1-c >= 0,
    1-s >= 0, 1-a >= 0, 1-o >= 0, 1 >= 0.

The first pair and their upper bounds force s=o=1. The remaining necessary
bounds reduce to 1/2 <= a <= 1 and 0 <= c <= a. Conversely those bounds make
all 16 expressions nonnegative. Each row has an explicit verified witness;
all row types already occur with at most five labels. Six labels remain the
proved structural bound for an arbitrary coefficient.

The six-label reduction is independent of score values. Thus these inequalities
are necessary and sufficient for anchor positivity on adjacent-copy plane
trees of every finite size. They are sufficient on all source bloblets through
the representation lemma. Summing anchors proves Theorem B. The domain has
vertices (c,a)=(0,1/2), (1/2,1/2), (0,1), and (1,1).

The original score (0,1,1/2,1) and Modified NANUQ score (1/2,1,1/2,1) are
included. The independent finite checker also directly evaluates both endpoints,
with 24,667 nonnegative coefficients each. The symbolic result covers the
entire domain, rather than just a line joining the two published variants.

This exactness concerns the stronger anchor-positivity criterion with the
anchor-sharing entry normalized to 1. A negative individual anchor coefficient
outside the domain could be offset by other anchors in an unweighted distance.
We therefore do not claim that this is the maximal circularity domain for
unweighted source-network distances. Nor does circularity imply identifiability:
at c=a=s=o=1, the distance is the same constant (n-1)(n-2) on every distinct
taxon pair, and all information about network structure is lost.

The symbolic receipt and independent equivalence proof are recorded in
`PARAMETER-DOMAIN-AUDIT.md` and `independent-parameter-domain-check.json`.

## 7. Exact composition proves Theorem A for multiple blobs

The existing computer-assisted level-two package supplies an exact composition
argument in `ordinal/COMPOSITION-PROOF.md`, Sections 1-3. Its arbitrary-level
version is proved in full in `ALL-LEVEL-COMPOSITION-AUDIT.md`:

    d_N(x,y) = sum_B W_{L_B}(m_B)(pi_B(x), pi_B(y)).

The sum includes ordinary trivalent vertices. Each port mass counts the taxa
in the attached component. The proof first decomposes a switching-weighted
tree distance through endpoint contributions and then corrects to the uniform
distinct-quartet distance. The correction is zero when a cut edge resolves
the quartet, and otherwise localizes at the unique central blob of the
contracted blob tree. This uses a set equality of displayed quartet topologies
and independence of local switchings, not equal multiplicities of topologies.

The separate audit proves the following steps without a level bound.

1. Every cut edge has taxa on both sides. An empty rootward side would violate
   the LSA property. Consequently all port masses are positive.
2. Capping a blob preserves binary degrees, galledness, and outer-labeled
   planarity. A blob containing the root inherits its rooted LSA partner.
   Otherwise, subdividing the rootward port edge by a new root explicitly
   supplies a rooted LSA partner. Two-port local matrices are zero; three-port
   matrices are positive star metrics and need no quartet argument.
3. Both incoming edges of every hybrid belong to one blob. Choices in the
   different blobs are a Cartesian product. Endpoint contributions of each
   displayed tree group exactly into weighted local tree distances.
4. If a cut edge resolves a quartet, its distinct-topology and switching
   averages agree. Otherwise the four taxa occupy four different ports of
   one central blob. Both the distinct quartet set and the switching marginal
   agree with that local blob's quantities. Counting choices of the other two
   taxa gives precisely the factors m_B(c)m_B(d).
5. In the chosen global embedding, each port component occupies a contiguous
   interval of taxon leaves. Every local circular split therefore lifts to a
   split in the same global circular order.

The composition identity and the positive weighted local theorem from Section 5
now give a nonnegative circular split decomposition of the full distance.
The bound d_N(x,y) >= 2n-4 supplies strict separation. This proves the
circularity part of Theorem A.
The audited composition identity is for the original NANUQ scoring rule;
Theorem B is not silently extended to multiple blobs by the same formula.
Section 8 supplies exact support equality. Canonical identification at arbitrary
level and statistical consistency remain additional mathematical statements.

## 8. Exact displayed-split support at every level

For a nontrivial circular split S, write its boundary gaps as (a,b) and (c,d),
where b,c are in one side and a,d in the other. All four labels are distinct.
In any tree circular in the full taxon order,

    S is displayed if and only if the boundary quartet bc|ad is displayed.

The forward implication is restriction. For the reverse, an edge on the
central path of that quartet induces a circular split separating b,c from
a,d. Such a split changes membership at both consecutive pairs (a,b) and
(c,d). These are already its two boundary gaps, so it equals S on all taxa.
Every displayed tree of the source network respects the chosen circular
order. Every displayed quartet extends to such a global tree. This proves
the same equivalence for the network's union of displayed splits.

If bc|ad is displayed, the anchor pair {a,d} has

    alpha_S(M^{ad}) = 2 - 2 rho(b,c;a,d) > 0.

Indeed one of the distinct quartet topologies makes b,c a cherry, and every
other topology separates them. In the planar case the coefficient is 1 or 2.
Every other anchor coefficient is nonnegative, so a positive mass assignment
cannot cancel it. For a singleton split {b}, anchors consisting of its two
neighbors a,d give alpha=2 directly. All singleton splits are displayed.

It remains to exclude extra metric splits. The independent finite support
check evaluates every nonadjacent gap pair in the saved 122 systems. Among
1,004 such system/gap cases, the boundary quartet is absent in 428. All 6,252
anchor coefficients in those absent cases are exactly zero. The receipt is
`independent-support-check.json`, the standalone checker is
`independent_support_check.py`, and its audit is
`ALL-LEVEL-SUPPORT-FINITE-AUDIT.md`.

For an absent split of an arbitrarily large source bloblet, retain its four
boundary labels and an arbitrary anchor pair. The six-label restriction
preserves both the absence of the boundary quartet and the anchor coefficient.
The finite zero certificate therefore forces that coefficient to be zero.
This holds for every anchor pair, so the whole weighted coefficient vanishes.
Thus for every local bloblet with at least three ports and every strictly
positive mass assignment,

    support(W_L(m)) = union_{T displayed by L} Split(T).

The two-port case is excluded from this local support identity: its W is zero.

For the global network, composition expresses the distance as a nonnegative
sum of lifted local split metrics in one common order. Every local displayed
split lifts to a global displayed split by extending its switching and
replacing each port by its nonempty taxon component.

Conversely, take an edge of a reduced global displayed binary tree. It has a
degree-three endpoint because the tree has at least four leaves. That endpoint
is an original tree vertex in one blob B; its three nonempty branches imply
that B has at least three ports. The corresponding edge of the local selected
tree gives the port split lifting to the global edge split. If the global edge
traverses bridges or a chain of two-port blobs, use its branching endpoint:
the intervening degree-two pieces change no bipartition. Consequently every
global displayed split receives a positive local contribution.

Nonnegative contributions cannot cancel. This proves the support assertion of
Theorem A. The complete transfer, including the two-port issue, is audited in
`ALL-LEVEL-SUPPORT-STRUCTURAL-AUDIT.md`. No analogous exact-support theorem is
asserted for the whole parameter region of Theorem B.

**A useful conditional algorithmic corollary.** Given a correct circular order
and an exact oracle for displayed quartets, the displayed split set can be
recovered by one boundary-quartet membership query for each nontrivial circular
split, plus all singleton splits. There are n(n-3)/2 such queries. This follows
from the boundary lemma; it is not a claimed first-in-literature algorithm,
does not find the circular order, and does not provide an estimator from noisy
gene trees. It identifies a concrete remaining bridge to sparse-query inference.

## Sources and attribution

The checked subsequent refinements are in `FIVE-TAXON-THRESHOLD.md`,
`CONTIGUOUS-MULTICOPY-EXTENSION.md`, and `ADDITIONAL-COROLLARIES.md`.
They respectively give the sharp parameter-test cutoff, an abstract extension
to arbitrary contiguous occurrence multiplicities, and quantitative support
margins with an explicit non-outer-labeled counterexample. Their claims and
evidence boundaries are stated separately so that none is silently imported
as a biological identifiability theorem.

- Holtgrefe et al. (2025), DOI 10.1007/s11538-025-01549-4: network class,
  NANUQ definition, circular reconstruction, and the explicit conjectures.
- Allman, Ane, Banos and Rhodes (2025), *Beyond Level-1*, DOI
  10.1007/s11538-025-01545-8, Section 3: root-skeleton structure and broader
  galled-network context. Their additional tree-child hypotheses must not be
  imported into this proof unnoticed; Section 1 supplies the needed argument
  for binary galled bloblets directly.
- Allman, Banos, Rhodes and Wicke (2025), *NANUQ+: A divide-and-conquer approach
  to network estimation*, DOI 10.1186/s13015-025-00274-w, Definitions 3.1,
  3.6 and 3.11: the parameter family and the two named specializations.
- The existing NANUQ research package supplies the two-anchor construction and
  the multiple-blob composition route. The adjacent-pair representation,
  uniform six-taxon verification, and exact symbolic anchor domain are the
  extensions developed here. Historical novelty has not been established by
  an exhaustive search. Separate internal audits are not external peer review.
