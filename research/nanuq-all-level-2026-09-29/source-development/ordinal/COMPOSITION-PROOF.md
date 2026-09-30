# Exact blob composition for the NANUQ metric

2026-09-29. Computer-assisted mathematical argument. The composition identity below is proved symbolically; the final conjecture conclusion uses the independently checked finite anchor-positivity lemma and its audited reduction. The accompanying source and combined reviews record the verification scope. This document is not a Lean kernel certificate. It does not modify the earlier frozen reports.

## Statement and notation

Let N be a binary semi-directed LSA phylogenetic network with finite leaf set X, |X|=n>=4. Assume N is outer-labeled planar, galled, and of level at most 2, exactly as in the class N2 of Holtgrefe et al. For a quartet Q and x,y in Q, rho_N,Q(x,y) is the uniform average of the cherry-separation indicator over the DISTINCT quartet trees displayed by N|Q. Thus it is 0 on a cherry in a displayed tree and 1 otherwise. The source metric is

  d_N(x,y) = 2 sum_{ {z,w} subset X\{x,y} } rho_N,{x,y,z,w}(x,y) + 2n-4,

for x!=y, with zero diagonal. All sums over pairs in this note are unordered. No substitution or coalescent model is assumed.

Delete all cut edges of N. The resulting components are the blobs, including single vertices. In the sum below retain all non-leaf blobs: in particular, an isolated trivalent tree vertex is a blob and MUST be included. A leaf singleton contributes nothing.

For a blob B, replace every component incident through a cut edge by a pendant leaf marking that port. Write P_B for these port labels and L_B for the resulting local network. For each port a let X_B(a) be the original taxa in the component outside B attached there, and set m_B(a)=|X_B(a)|. These sets partition X, and define pi_B:X->P_B. All m_B(a) are positive. Indeed, every descendant-side component of a cut edge contains a leaf; an empty rootward component would put all taxa below that edge and contradict the rooted LSA condition. Local networks inherit the outer-labeled planar, galled and level bounds. For at least four ports they are bloblets in B2.

For any local network L with port set P and any positive masses m:P->R, define the weighted local matrix W_L(m), with zero diagonal, by

  W_L(m)(a,b) =
    2 sum_{ {c,d} subset P\{a,b} } m(c)m(d) rho_L,{a,b,c,d}(a,b)
    + (m(a)+m(b)) sum_{c in P\{a,b}} m(c).

For fewer than four ports the quartet sum is empty. The definition is meaningful for two or three ports without invoking a source theorem formulated only for four or more leaves. When m is identically 1 and |P|>=4, W_L(m) is exactly the source NANUQ metric.

THE COMPOSITION IDENTITY is

  d_N(x,y) = sum_{B non-leaf blob} W_{L_B}(m_B)(pi_B(x),pi_B(y)).       (C)

In particular the argument does not replace the source metric by a multiplicity-weighted metric. A switching average is used only as an intermediate identity, and its discrepancy from the source metric is accounted for exactly.

## 1. A weighted tree identity

Let T be a binary unrooted tree with terminal set P and terminal masses m. For an internal edge whose adjacent branches contain terminal sets P1,P2 on one end and P3,P4 on the other, assign length

  m(P1)m(P2)+m(P3)m(P4),

where m(A)=sum_{a in A}m(a). For a pendant edge at a, the two other branches at its internal endpoint give length m(P1)m(P2). Let D_T(m) be the resulting path metric.

Then D_T(m)=W_T(m). One direct proof compares the coefficient of each monomial m(c)m(d). These polynomials have no squared-mass terms, because every edge contribution multiplies masses in disjoint branches.

- If {c,d}={a,b}, its coefficient in the a-b distance is 0.
- If exactly one of c,d equals a or b, its coefficient is 1. It is contributed at the unique branch vertex of the minimal subtree connecting the three distinct terminals.
- If a,b,c,d are all distinct, its coefficient is 0 when a,b form a cherry in T restricted to those four terminals and 2 otherwise. In the latter case the two branch vertices of the four-terminal subtree each contribute one unit along the a-b path.

These are precisely the coefficients in the displayed formula for W_T. This proves the weighted tree identity. For |P|=3 it gives a star with pendant length m(b)m(c) at a. For |P|=2 every assigned length is zero and D_T=W_T=0.

It is useful to view each tree edge length as a sum of endpoint contributions. At an internal vertex v, the contribution to the edge entering one branch is the product of the masses in the other two branches. A pendant leaf endpoint makes no contribution.

## 2. Switching-tree composition

Fix a rooted partner of N. Independently retain one of the two incoming hybrid edges at each hybrid node, then delete irrelevant unlabeled leaves and suppress degree-two vertices. This gives a displayed unrooted tree T_sigma on X. The auxiliary switching distribution assigns equal probability to every hybrid-edge choice, so a displayed topology is weighted by its switching multiplicity.

For a fixed global switching sigma, its restriction sigma_B to each blob yields the corresponding local displayed tree T_B,sigma_B on P_B. Conversely, local choices extend independently to global choices. Ports are retained because each incident outside component contains a taxon. The galled condition also ensures the local construction is the usual bloblet switching construction.

Apply the source quartet metrization to T_sigma with unit masses at X. Group its endpoint contributions from Section 1 by the original blob containing the corresponding internal vertex. Suppression of degree-two vertices creates no new branching vertices: each internal vertex of T_sigma came from a unique original blob. Its three taxon-branch sizes are exactly the sums of the terminal masses m_B in the three branches of the local displayed tree. Hence its contribution is identical to that in D_{T_B,sigma_B}(m_B).

If x,y are in the same pendant component at B, their path does not enter B, and the local contribution is zero. Otherwise it is the local path distance between their two port labels. Thus, for every switching,

  d_{T_sigma}(x,y)
    = sum_B D_{T_B,sigma_B}(m_B)(pi_B(x),pi_B(y)).             (T)

Average (T) over all global switchings. Since each local switching is uniform under that average, the result is the sum of the local weighted switching-average tree metrics. The endpoint argument includes trivial trivalent blobs; omitting them would make (T) false even for an ordinary tree.

## 3. The source/switching discrepancy localizes at one blob

For each quartet Q, write rho_sw,N,Q for the switching average of its cherry-separation indicator. The source metric differs from the switching-average tree metric by

  E_N(x,y)=2 sum_{ {z,w} subset X\{x,y} }
                 (rho_N,Q(x,y)-rho_sw,N,Q(x,y)),

where Q={x,y,z,w}. The constant 2n-4 cancels in this comparison, exactly as in the paper's Lemma 4.2.

Consider the tree obtained by contracting every blob of N. Its minimal subtree on four selected taxa, after suppressing degree-two vertices, is either a resolved quartet or a star.

If it is resolved, some cut edge of N separates Q as two taxa versus two taxa. This split occurs in every displayed tree, so N displays only that quartet topology. The source and switching averages agree, and this quartet contributes zero discrepancy.

If it is a star, it has a unique central vertex. This vertex represents a unique blob B, and the four taxa lie in four DISTINCT pendant components at B. Any other blob sees at most three occupied ports, so it cannot independently change the quartet topology. Restricting any global switching tree to Q gives exactly the quartet obtained by restricting the local switching at B to those four port labels. Conversely, each local switching extends globally. It follows both that the sets of distinct displayed quartets agree and that their switching-average indicators agree. This includes the case where the local set happens to contain only one quartet, yielding zero discrepancy.

Therefore every possibly nonzero source/switching discrepancy belongs to exactly one blob B. For fixed x,y in distinct B-ports a,b, every unordered pair of other distinct ports c,d supplies exactly m_B(c)m_B(d) choices of z,w. The local discrepancy is consequently

  E_B(m_B)(a,b)=2 sum_{ {c,d} subset P_B\{a,b} } m_B(c)m_B(d)
       (rho_LB,{a,b,c,d}(a,b)-rho_sw,LB,{a,b,c,d}(a,b)).

It is zero when pi_B(x)=pi_B(y). Summing the localized terms gives E_N=sum_B E_B(m_B) pulled back by pi_B.

By the weighted tree identity, the local switching-average metric plus E_B(m_B) is exactly W_LB(m_B). Adding this discrepancy identity to the averaged equation (T) proves (C).

## 4. Reduction of arbitrary positive masses to two-anchor matrices

For distinct anchors c,d in P, define M_L^{cd} with zero diagonal as follows:

  M(c,d)=0;
  M(c,a)=M(d,a)=1 for a outside {c,d};
  M(a,b)=2 rho_L,{a,b,c,d}(a,b) for a,b outside {c,d}, a!=b.

Coefficient comparison directly gives

  W_L(m) = sum_{ {c,d} subset P } m(c)m(d) M_L^{cd}.          (A)

For a fixed circular order C, every circular split coefficient alpha is linear in the distance matrix. The circular reconstruction identity writes any symmetric zero-diagonal matrix as one half of the sum of its alpha coefficients times the corresponding circular split metrics (the identity used in the proof of source Proposition 2.8). Thus nonnegative coefficients themselves supply a split-metric decomposition; no unproved triangle-inequality assumption on an anchor matrix is needed. If alpha(M_L^{cd})>=0 for every anchor pair and every circular split, (A) makes W_L(m) circular decomposable for all positive m.

More is true: because every coefficient m(c)m(d) is strictly positive, alpha(W_L(m)) vanishes exactly when all alpha(M_L^{cd}) vanish. In particular its support is independent of the positive masses and agrees with the support at m=1. For |P|>=4, the published Theorem 4.7 identifies that latter support as Split(T(L)). Hence local anchor NONNEGATIVITY, not an independent exact-support theorem for each anchor matrix, is sufficient.

The standard coefficient is alpha_ij(d)=d(i,j)+d(i+1,j+1)-d(i,j+1)-d(i+1,j), with cyclic indices and the usual identification of a circular split by its two boundary gaps. Actual split weights are alpha/2. This factor does not affect nonnegativity or support.

## 5. Local lemma and finite verification boundary

The local lemma used for the final conclusion is: every two-anchor matrix of every outer-labeled planar galled level-at-most-two bloblet is circular decomposable in its induced circular order.

For a strict level-two bloblet, the canonical form has two junctions u,v joined by a central edge, four arms A1,B1,A2,B2, and hybrid terminal leaves C1,C2. The four switchings move Ci between the tips of Ai and Bi. Fix an anchor pair and a split coefficient. That coefficient refers to at most six named leaves: two anchors and the at-most-four leaves adjacent to the split boundaries. Delete every other ordinary arm leaf, suppress its degree-two arm vertex, and retain BOTH hybrid leaves. This leaves at most six ordinary leaves plus the two hybrid leaves. Each of the four restricted switching quartet topologies is preserved, so distinct-quartet sets and the tested coefficient are preserved. The named adjacent boundary leaves remain adjacent in the reduced circular order. This is the finite-compression step requiring independent audit.

The parent implementation exhausts all 209 nonnegative arm-length tuples with ordinary-leaf sum from 1 through 6, evaluates every anchor pair and every circular split coefficient with exact arithmetic, and finds no negative value. The all-zero tuple has only two hybrid leaves; its sole anchor matrix is identically zero. Three-leaf residual templates are also included because anchor and boundary labels can overlap. The level-at-most-one cases have a direct weighted proof. A level-one bloblet has only two hybrid switchings. On each quartet they either display the same topology, giving a point mass, or two different topologies with equal probability. Hence its uniform-distinct-quartet and switching averages agree exactly. Its W is therefore the average of the two weighted tree metrics from Section 1. Their splits are compatible with the same circular order, every tree edge has positive weight for positive terminal masses and at least three ports, and the support of the average is their union. A tree blob is even more immediate. Thus no inference from an unweighted theorem and no extra level-one finite search is required.

The level-one anchor lemma itself also follows directly: each weighted tree-edge length in Section 1 is a polynomial with nonnegative coefficients in the monomials m(c)m(d). Taking one such coefficient gives a tree split metric with nonnegative edge weights. A level-one anchor matrix is the average of its two tree anchors. This proves the stated anchor lemma as well as the weighted conclusion in that case.

Current receipts outside this folder are maintained by the parent: exact_networks.py and six-witness-search.json. The completed parent sweep has 209 templates and 100,823 anchor checks. The independent audit implementation reproduces those counts using four-point tree distances; the source implementation checks the 205 cases with at least four leaves, plus a separate analytic/direct check of the four three-leaf cases. No coefficient is negative. Additional actual-network admission, composition and direct restriction controls are recorded separately. These computations, together with the proved compression, establish the local lemma; they are not Lean certification.

## 6. Small-port blobs and compatibility of lifted metrics

A blob with two ports contributes W=0. Such a blob may affect the graph presentation, but not the quartet term or the endpoint-based metric contribution. Its zero contribution is necessary and is not an omission.

For three ports a,b,c, all local displayed unrooted trees are the same three-leaf star. The weighted formula is

  W(a,b)=(m(a)+m(b))m(c).

It is the star metric with three positive pendant weights m(b)m(c), m(a)m(c), m(a)m(b). It therefore has exactly the three local trivial splits as support, without needing a four-leaf theorem.

Choose a planar embedding of N with all leaves on the outer face and let C_X be its induced circular leaf order. For any blob B, its pendant components occur as contiguous blocks in C_X. Collapsing these blocks gives an induced circular order on P_B. A circular local split of ports lifts under pi_B to a circular split of X; its split metric pulls back to exactly the split metric of this lifted split. Thus all local nonnegative decompositions in (C) use splits compatible with the SAME global circular order. Their sum is circular decomposable.

## 7. Exact global support

For every blob with at least three ports, the local metric has support exactly the splits of its displayed local trees: Section 4 and the local lemma for at least four ports, and the explicit star calculation for three ports.

First, every split of a local displayed tree lifts to a split of some global displayed tree. Choose the local switching realizing it and extend those choices arbitrarily to all other blobs. The corresponding local edge extends through the cut-edge attachments; suppressing degree-two vertices preserves the induced taxon bipartition. All port masses are nonzero, so neither side of a nonempty local split disappears.

Conversely, let S be a split of a global displayed tree T_sigma. Since |X|>=4, the edge inducing S has at least one internal degree-three endpoint v. That vertex belongs to a unique original blob B and remains a branching vertex in the local displayed tree at B. The local edge leaving v in the direction of the global edge gives exactly S when its port split is lifted to X. Such a blob necessarily has at least three ports. This argument covers a split represented by a chain of two-port blobs: an endpoint branching blob supplies its positive local weight.

Therefore the union of lifted local supports over blobs with at least three ports is EXACTLY Split(T(N)). In (C), every local split weight is nonnegative; there can be no cancellation. Every split in that union receives at least one strictly positive contribution, so the support of d_N is exactly Split(T(N)). Together with circular decomposability and the computer-assisted local lemma established above, this proves precisely the B2-to-N2 extension of Theorem 4.7.

## Audit gates and source correspondence

The proof's two reusable mathematical results are the exact composition identity (C) and the positive-mass support invariance derived from anchor decomposition (A). A complete computer-assisted theorem package must include: a proof of the local finite-compression lemma; exact exhaustive certificates including the level-one and small-port cases; an audit of graph/source definitions and the switching restriction property; and independent checking of the global composition and support arguments. No empirical coalescent, finite-data consistency, or biological identifiability conclusion is asserted by this purely combinatorial theorem.

Source: Holtgrefe et al., Distinguishing Phylogenetic Level-2 Networks with Quartets and Inter-Taxon Quartet Distances, Bulletin of Mathematical Biology87:168 (2025), corrected publisher article https://link.springer.com/article/10.1007/s11538-025-01549-4 . Relevant locations: Definitions2.1-2.4; quartet metrization equations(6)-(7) and Theorem2.12; Lemma4.2; Definition4.1; Theorem4.7; Section6. The 2026 correction only restores omitted Figure12b. This draft preserves the uniform average over distinct quartet topologies throughout the final metric.
