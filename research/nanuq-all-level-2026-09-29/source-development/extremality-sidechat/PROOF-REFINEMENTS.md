# NANUQ proof refinements and sharpness certificates

Date: 2026-09-29.

## Verification contract

This package supplies written mathematics and executable exact finite computations. It does **not** claim that these arguments have been compiled in Lean. The JavaScript verifier has been executed in the available JavaScript runtime. The same source is provided as a standalone Node script; a separate Node shell run was not available in this side conversation.

The unbounded results use the source-class representation, restriction, anchor positivity, and original-NANUQ composition lemmas already audited in the main research thread. Those dependencies are explicit below. The finite verifier does not by itself prove that every arbitrary graph belongs to its representation domain.

Source: Holtgrefe et al., *Distinguishing Phylogenetic Level-2 Networks with Quartets and Inter-Taxon Quartet Distances*, [DOI 10.1007/s11538-025-01549-4](https://doi.org/10.1007/s11538-025-01549-4), Definitions 2.1–2.5, Proposition 2.8/2.9, Lemma 3.2, Definition 4.1, Theorem 4.7, and Section 6. The paper's explicit extension questions must be distinguished from the new internal audit targets in this package.

## 1. Exact theorem and dependencies

Let N be a finite binary semidirected LSA, outer-labeled planar, galled network on n>=4 distinct taxa. There is no bound on its finite reticulation level or its finite number of blobs. Let C be an outer-face taxon order. For distinct x,y the original, unnormalized NANUQ distance is

\[
d_N(x,y)=2\sum_{\{z,w\}\subseteq X\setminus\{x,y\}}
 \rho_{xy}(N|_{\{x,y,z,w\}})+2n-4,
\qquad d_N(x,x)=0.
\]

The averaging in rho is uniform over **distinct displayed quartet topologies**. It is not uniform over network switchings.

The main theorem is circular decomposability of d_N, with positive split support exactly the union of splits of all displayed trees.

Dependencies accepted in the main thread:

1. Opening each hybrid leaf gives one or two adjacent occurrences per label in a plane binary tree.
2. Keeping all occurrences of retained labels, taking the minimal connecting subtree, and suppressing degree-two nodes preserves all relevant restrictions and selection extensions.
3. Every circular anchor coefficient reduces to at most six labels.
4. Exact finite enumeration proves anchor nonnegativity throughout that representation domain.
5. Original NANUQ composes over capped blobs with positive integer port masses in a shared circular order.

The correct restriction in item 2 includes recursive pruning. A one-pass deletion of unwanted tips followed only by degree-two suppression is insufficient.

## 2. Definitions for formalization

For consecutive boundary gaps (a,b) and (c,d) of a circular split S, define

\[
\alpha_S(D)=D(a,c)+D(b,d)-D(a,d)-D(b,c).
\]

The split weight is omega_S=alpha_S/2.

For distinct anchors p,q, set M^{pq}(u,u)=0. Off diagonal, its value is zero for the anchor pair itself, one if exactly one query endpoint is an anchor, and 2rho_uv on the quartet {u,v,p,q} otherwise. For positive port masses,

\[
W(m)=\sum_{\{p,q\}}m_pm_q M^{pq},
\qquad
\alpha_S(W(m))=\sum_{\{p,q\}}m_pm_q\alpha_S(M^{pq}).
\]

Every anchor coefficient is nonnegative by the accepted coverage theorem and finite certificate.

A split is treated as an unordered bipartition. Circular order is considered up to rotation and reversal. The coefficient formula fixes a representative order; formalization must prove all representation invariances it uses.

## 3. Boundary-split lemma

Let both sides of S contain at least two taxa, and let (a,b),(c,d) be its boundary gaps, with b,c inside and a,d outside. For every tree T with splits circular in C,

\[
S\in\Sigma(T)\quad\Longleftrightarrow\quad T|_{\{a,b,c,d\}}=bc|ad.
\]

Forward: the edge for S still separates two retained taxa from the other two.

Reverse: the quartet's internal edge is inherited from an edge of T. Its split R is circular and puts b,c together against a,d. Therefore membership changes across both original adjacent gaps a,b and c,d. A circular split has exactly two boundary gaps, so these must be the boundaries of R. Thus R=S.

This is an exact lifting argument. An arbitrary restricted split need not lift to an arbitrarily prescribed full split when the boundary taxa are omitted.

## 4. Analytic no-loss proof

Only ab|cd and ad|bc can occur on the four boundary taxa; ac|bd crosses the fixed circular order. Let tau be 0, 1, or 2 according as the boundary topology ad|bc is absent, is one of two displayed topologies, or is the only topology.

Direct substitution gives

\[
\alpha_S(M^{ad})=\alpha_S(M^{bc})=\tau,
\]

and the other four anchor pairs drawn from {a,b,c,d} have coefficient zero. For example,

\[
\alpha_S(M^{ad})=1+1-0-2\rho_{bc}=2(1-\rho_{bc}).
\]

If S is displayed, tau>=1 by the boundary lemma. Since all other coefficients are nonnegative,

\[
\alpha_S(W(m))\ge
\tau(m_a m_d+m_b m_c)>0.
\]

For a singleton S={b}, let a,d be its two immediate neighbors. Directly,

\[
\alpha_b(M^{ad})=2,
\qquad
\alpha_b(W(m))\ge 2m_a m_d>0.
\]

Thus **no-loss support is analytic** once anchor nonnegativity is available. It does not need a finite exact-support lookup.

## 5. No-false-split proof

Suppose alpha_S(W(m))>0 for a nontrivial S. Some anchor p,q has positive coefficient. Retain the four boundary labels and p,q, at most six labels in total. The same anchor coefficient survives restriction.

The finite certificate says that an absent boundary quartet forces every reduced anchor coefficient to vanish. Therefore the boundary quartet must be displayed in the retained representation. Extend that occurrence choice to all labels, then use the boundary lemma to obtain S in the full selected tree.

The finite certificate's irreducible role is therefore nonnegativity plus the no-false-split vanishing property. Its finite exact-support equality also verifies these properties. The analytic no-loss argument separates these dependencies and makes the proof easier to audit.

This is not a reduction of every coefficient to four labels. Six labels remain the established structural query bound.

## 6. Multiple blobs, including degenerate local sizes

For every non-leaf blob B, include its capped local port network L_B, map pi_B, and positive mass vector m_B. Include ordinary singleton trivalent blobs. The accepted original-NANUQ identity is

\[
d_N(x,y)=\sum_B W_{L_B}(m_B)(\pi_B(x),\pi_B(y)).
\]

It follows by grouping selected-tree endpoint contributions by blob, averaging over the product of local switching choices, and then localizing the discrepancy between switching-weighted and uniform-distinct quartet averages to the unique central blob.

Local nonnegative split decompositions pull back to the same global circular order. Coincident splits add weights, so support is a union with no cancellation.

A positive local split extends to a displayed global split by extending its local switching.

Conversely, take an edge in a displayed global binary tree. It has a degree-three endpoint v when n>=4. This is an original tree vertex in a unique blob B. Its three nonempty taxon branches correspond to nonempty sets of ports, so v persists as a branching vertex in a local selected tree with at least three ports. The incident local edge toward the global edge gives the desired lifted bipartition. Bridges or intervening two-port blobs do not alter that split.

A two-port local matrix is zero. It is incorrect to assert exact local support for it. The branching-endpoint argument is how global completeness survives this case. A three-port matrix is the weighted star with pendant lengths m_b*m_c, m_a*m_c, m_a*m_b.

## 7. Quantitative singleton and positive-support bounds

For singleton b with neighbors a,d and any other taxon t,

\[
\alpha_b(M^{a,t})=2\rho_{bd},\qquad
\alpha_b(M^{d,t})=2\rho_{ab}.
\]

In cyclic order a,b,d,t, the two possible quartet topologies are ab|dt and at|bd. On either topology the separation indicators for ab and bd sum to one. Hence the two coefficients above are nonnegative and sum to two.

Discarding other nonnegative terms gives

\[
\alpha_b(W(m))\ge
2m_a m_d+
2\min(m_a,m_d)\sum_{t\notin\{a,b,d\}}m_t.
\]

For unit local masses on r ports this yields alpha_b>=2(r-2).

For a port representing one global taxon, m_b=1, total mass is n, and all masses are positive integers. Use m_a*m_d>=m_a+m_d-1 and min(m_a,m_d)>=1 to obtain alpha_b>=2(n-2). The global singleton weight is therefore at least n-2.

For every displayed nontrivial local split with integer masses, Section 4 gives alpha>=2, hence omega>=1. Singleton local weights are at least one. Global weights add lifted nonnegative contributions, so every positive global split weight is at least one.

Sharpness:

- A four-taxon cycle displaying the two planar quartets has nontrivial weights exactly one.
- A binary tree with the chosen taxon in a cherry has that singleton weight exactly n-2: its two other endpoint branches have masses 1 and n-2.

There is no uniform positive lower bound for arbitrary positive real masses without normalization: W(lambda*m)=lambda^2*W(m).

## 8. Optimal universal baseline and residual pseudometric

Subtract n-2 from every singleton split weight. Section 7 shows that all remaining weights are nonnegative. Since two singleton split metrics contribute to each off-diagonal pair, this gives

\[
q_N(x,y)=d_N(x,y)-(2n-4)\quad(x\ne y),
\qquad q_N(x,x)=0.
\]

Thus q_N is circular decomposable and is a pseudometric. It need not separate distinct taxa.

The universal pendant subtraction n-2 is optimal for each n: a cherry taxon in an admitted tree attains equality. A larger universal subtraction would make its singleton coefficient negative. No claim is made that every individual network cannot permit a larger subtraction.

## 9. A newly closed extremum: exact raw-noise radius 1/2

Every displayed quartet set in this class has one or two topologies. Therefore rho belongs to {0,1/2,1}, so every raw d_N entry is an integer.

If an observed symmetric matrix Dhat satisfies

\[
\|Dhat-d_N\|_\infty<1/2,
\]

rounding each entry to its nearest integer recovers the exact source matrix. With a correct circular order supplied, compute the exact coefficients and recover exact split support. This improves the earlier sufficient direct-threshold radius 1/4.

The strict universal radius 1/2 is sharp. In order a,b,c,d compare the admitted tree displaying ab|cd and the admitted four-cycle displaying ab|cd and ad|bc:

\[
D_T=\begin{pmatrix}
0&4&6&6\\4&0&6&6\\6&6&0&4\\6&6&4&0
\end{pmatrix},
\qquad
D_C=\begin{pmatrix}
0&5&6&5\\5&0&5&6\\6&5&0&5\\5&6&5&0
\end{pmatrix}.
\]

Their entrywise sup-norm difference is one. Their midpoint is within 1/2 of each and cannot identify which true support generated it. The supports differ even though they have the same valid circular order. Thus no universally correct method can guarantee exact support recovery from arbitrary entrywise errors of size 1/2.

Admission of the cycle: attach one taxon to each of its four vertices, designate the d vertex as hybrid, and root on the b pendant edge. The b-side root branch is taxon b; the other root branch divides toward a and c, which feed the hybrid d. This is binary, galled, LSA, outer-labeled planar, level 1. Choosing the a-parent or c-parent of d gives ad|bc or ab|cd.

Limits:

- This is a source-promise theorem for the original, unnormalized distance.
- The radius rescales if the distances are normalized.
- Noisy estimates of a different population quantity need not lie near this integer lattice.
- The result is deterministic, not a statistical sample-complexity theorem.
- Rounding recovers d without an order, but the support-extraction procedure stated here assumes the correct order. A verified order-finding algorithm is a separate task.
- The four-cycle witness makes 1/2 optimal universally; it does not claim every fixed network has exactly the same local robustness radius.

## 10. A second exact extremum: minimum split-support cardinality

Every admitted network displays at least one binary n-leaf tree. Such a tree has 2n-3 edges and distinct edge splits. The union of displayed-tree splits therefore has cardinality at least 2n-3. Exact support transfers this bound to the metric's positive splits.

A source network that is itself a binary tree attains equality. Thus the minimum total support size is exactly 2n-3, or n-3 nontrivial splits after removing n singleton splits. This does not determine the maximum attainable support size or uniqueness of a network achieving the minimum.

## 11. Five versus six: exactly what is settled

The program computes the normalized nonzero symbolic coefficient rows in coordinates (constant,c,s,a,o). Division is by a positive gcd, so inequality direction is preserved.

Observed catalogues:

| Labels | Distinct quartet systems | Nonzero normalized row types |
|---:|---:|---:|
| 3 | 1 | 1 |
| 4 | 3 | 10 |
| 5 | 16 | 16 |
| 6 | 102 | 16 |

The five- and six-label row sets agree exactly. Four labels miss six rows. Therefore **five is the minimum label size generating this complete normalized row catalogue**, using the established six-label coverage theorem.

A concrete parameter vector (c,s,a,o)=(0,1,1/4,1) passes every four-label row and fails the five-label row 2a-s. Its saved witness has packed quartet pattern 7021, anchors [2,3], and gaps [0,4]. The receipt specifies the encoding through the verifier.

What remains open: a uniform structural procedure replacing every six-label coefficient query by a five-label one, or by a proved combination of five-label queries. Finite equality of row catalogues is not such a structural reduction. It does permit certificate compression after the six-label catalogue has been exhaustively established.

## 12. Why outer-labeled planarity cannot be dropped from exact support

Take tree vertices u,v,w,z with skeleton path w-v-u-z. Attach ordinary a at u and b at v. Add hybrids h_c and h_d, each with parents w,z, and child taxa c,d respectively.

Edges:

- u-v, v-w, u-z, u-a, v-b;
- w-h_c, z-h_c, h_c-c;
- w-h_d, z-h_d, h_d-d.

Root on the a pendant edge, orient the skeleton away from that root, and direct the four parent edges into the hybrids. All internal vertices have the required binary degrees. Each hybrid gall consists of its two incoming edges plus the skeleton path w-v-u-z and contains no other hybrid edge. The network is galled, LSA, and level 2.

The four retained-parent choices for (c,d) give:

| Parents | Quartet |
|---|---|
| w,w | ab\|cd |
| w,z | ad\|bc |
| z,w | ac\|bd |
| z,z | ab\|cd |

Thus all three quartet topologies are displayed. Uniform-distinct averaging gives rho_xy=2/3 for every pair and d_N(x,y)=16/3 off diagonal. This is a star metric with no nontrivial circular coefficient, whereas the displayed split union has all three nontrivial quartet splits.

The graph is a theta whose three arms each have attached taxa; it cannot have all taxa on a single outer face. It preserves the other stated hypotheses and demonstrates failure of exact support when outer-labeled planarity is omitted.

Its distance is still circular. This counterexample does **not** establish that outer-labeled planarity is necessary for circularity alone, or that every other hypothesis is individually necessary.

## 13. What the executable certificate proves

The program enumerates all fixed-order plane binary occurrence trees with one or two adjacent occurrences of each label, for three through six labels. It selects an actual occurrence for every label, projects every tree edge to a taxon split, and derives quartet support from these displayed edge splits.

It checks:

1. 84,076 ordered occurrence-tree configurations.
2. 2,525,210 complete occurrence selections.
3. 122 distinct quartet/split systems across the four sizes.
4. 24,667 anchor/split coefficient tests, with zero negative coefficients.
5. Exact equality of positive coefficient support and displayed support.
6. Boundary-quartet characterization.
7. Singleton and nontrivial unit-mass coefficient margins.
8. Five/six symbolic row equality and a four-label parameter-test counterexample.
9. The 18 explicit four-boundary anchor identities.
10. The exact tree/cycle noise endpoint matrices.
11. The four occurrence selections and metric of the non-outer counterexample.

Source-class admission, arbitrary-size transfer, weighted inequalities, and the graph composition proof remain written mathematical arguments. The program does not pretend to verify arbitrary network topology through these finite cases alone.

The scalar calculations use exact integers or exactly representable halves and quarters; the 16/3 counterexample is stored after multiplying the matrix by three. Packed quartet patterns use BigInt. There are no approximate tolerances, external dependencies, random trials, or imports.

## 14. Run and interpret

Run:

```text
node verify_nanuq.js
```

The JSON output should match verification-results.json. A thrown exception means failure. A successful process is a finite computational certificate, not a Lean kernel receipt. The source-to-finite and source-to-composition obligations remain separate and are enumerated in THEOREM-EXTREMALITY-REGISTER.md.

