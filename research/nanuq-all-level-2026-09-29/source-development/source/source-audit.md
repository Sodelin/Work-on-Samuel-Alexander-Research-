# NANUQ source-to-implementation audit

Date: 2026-09-29. Bounded audit of the corrected Holtgrefe et al. paper and the task's canonical theta implementation. No literature-wide novelty claim. Computation is exact rational arithmetic, not floating-point sampling.

## Source boundary

Primary source: [Holtgrefe et al., Bulletin of Mathematical Biology 87:168 (2025)](https://link.springer.com/article/10.1007/s11538-025-01549-4), with page numbers from the [author-hosted published PDF](https://ueaeprints.uea.ac.uk/id/eprint/100829/7/Holtgrefe_etal_2025_BullMathBiol.pdf). Definitions 2.1–2.5 are on pp. 4–6; quartet indicator and metric on pp. 9–10; NANUQ Definition 4.1 on p. 14; Figure 5 and error formula on pp. 15–17; Lemmas 4.5–4.6 on pp. 19–22.

The [14 January 2026 correction](https://link.springer.com/article/10.1007/s11538-025-01564-5) supplies the omitted Figure 12b and states that results are unaffected. It does not enlarge Theorem 4.7 beyond bloblets.

The source assumes binary rooted LSA partners; the semi-directed graph suppresses the root and retains only arrows entering hybrids. Its classes require outer-labeled planarity and galledness. NANUQ averages distinct displayed quartet topologies, whereas the displayed-quartet metric averages switching multiplicities. Lemma 4.5 establishes zero coefficients outside displayed splits; Lemma 4.6 establishes positivity inside. Both concern single non-leaf blobs. The proposed extension to general networks remains separate from these published statements.

## Explicit canonical specimen

Let the six labels be `(a1,c1,b1,b2,c2,a2)`. Use root `r`, tree vertices `u,v,pA1,pA2,pB1,pB2`, and hybrids `h1,h2`. Directed edges are:

```text
r -> u,v
u -> pA1,pA2
v -> pB1,pB2
pA1 -> a1,h1      pB1 -> b1,h1
pA2 -> a2,h2      pB2 -> b2,h2
h1 -> c1         h2 -> c2
```

This construction satisfies the source's assumptions for the following explicit reasons.

- All non-root internal tree vertices have degrees `(in,out)=(1,2)`, both hybrids have `(2,1)`, and the root has `(0,2)`. The displayed level order is topological, so the digraph is acyclic.
- The unique paths to `a1` and `b1` diverge immediately at `r`. Their only common dominator is `r`, which establishes the LSA requirement for the whole leaf set.
- On suppressing `r`, the non-leaf core consists of edge `u–v` and paths `u–pA1–h1–pB1–v` and `u–pA2–h2–pB2–v`. It is one bridgeless component with two hybrids. All other edges are pendant bridges. Thus the semi-directed graph is a strictly level-2 bloblet.
- The cycle using the first path and `u–v` contains exactly the two hybrid edges entering `h1`; the other analogous cycle contains exactly those entering `h2`. This certifies galledness directly.
- Place `u=(-2,0), v=(2,0), r=(0,0), pA1=(-1,1), pB1=(1,1), h1=(0,2), pA2=(-1,-1), pB2=(1,-1), h2=(0,-2)`, and the leaves at `(-2,2),(0,3),(2,2),(2,-2),(0,-3),(-2,-2)` in the stated order. Straight edges give a planar embedding with all labels on the outer face.

Here the four ordinary canonical sets each contain their correspondingly named leaf and `Ci={ci}`. The four switchings keep the A or B incoming edge into `h1`, then into `h2`. Their nontrivial splits are:

| Switching | Nontrivial split sides; complements implicit |
|---|---|
| AA | `{a1,c1}`, `{a2,c2}`, `{b1,b2}` |
| AB | `{a1,c1}`, `{b2,c2}`, `{a1,a2,c1}` |
| BA | `{b1,c1}`, `{a2,c2}`, `{a1,a2,c2}` |
| BB | `{b1,c1}`, `{b2,c2}`, `{a1,a2}` |

The complete 15-by-4 quartet table and distance matrix are in [six-leaf-fixture.md](six-leaf-fixture.md); machine-readable data are in [six-leaf-fixture.json](six-leaf-fixture.json). An especially useful regression is `{a1,a2,c1,c2}`: AA, AB, and BA give `a1c1|a2c2`, while BB gives `a1a2|c1c2`. NANUQ uses a 1:1 average over these two distinct outcomes, not a 3:1 average. For the full specimen, `d(a1,c1)=14`, but the multiplicity-averaged distance is 13.

All 15 distance pairs and all 90 quartet-pair rho values match the parent `exact_networks.py` after relabeling. The independent extraction uses shortest path lengths and the four-point quartet test; the parent uses restricted edge splits. The metric has 14 positive circular coefficients and one zero coefficient; the zero split is `{a1,b1,c1}|{a2,b2,c2}`. Coefficients in the actual split decomposition are half the reported alpha values.

## What the original positivity argument does and does not give for weights

Directly replacing leaf counts in the original inequalities is insufficient. Its hybrid leaves are singletons, so an error contribution counted once can become `m(c1)m(c2)` after cluster expansion. The useful feature is instead the local dependence on a four-leaf displayed-quartet set. The task's anchor decomposition isolates that dependence.

For distinct anchors `p,q`, define a symmetric zero-diagonal function

```text
k_pq(p,q) = 0;
k_pq(x,y) = 1                         if {x,y} meets {p,q} in one element;
k_pq(x,y) = 2 rho_xy(N|xypq)          if {x,y} is disjoint from {p,q}.
```

For positive masses `m_x`, set `R_xy=sum_{z not in {x,y}} m_z` and

```text
d_m(x,y) = 2 sum_{z<w; z,w not in {x,y}} m_z m_w rho_xy(N|xyzw)
           + (m_x+m_y) R_xy,      x != y;
d_m(x,x) = 0.
```

Partitioning anchor pairs by whether they contain an endpoint gives the exact identity

```text
d_m = sum_{p<q} m_p m_q k_pq.
```

At unit masses this is precisely the source metric, including the `2n-4` term. Consequently, if each anchor has nonnegative circular coefficients, the weighted metric has them too. Strictly positive masses give the same support as unit masses, since a positive linear combination of nonnegative numbers is zero exactly when all summands are zero. This algebra works for positive real masses; integrality is not required for this auxiliary weighted metric.

## Independent finite reduction audit

For a fixed anchor and circular coefficient, let `Y` consist of its three or four boundary leaves together with the two anchors. Thus `|Y|<=6`. Retain `Y` and both hybrid leaves in a canonical theta, delete every other ordinary arm leaf, and suppress the vacated degree-2 arm vertices.

This reduction preserves the coefficient exactly:

1. Each of the four choices of incoming hybrid edges is still present, because both hybrid leaves were retained.
2. In each switching, deleting other pendant leaves and suppressing degree-2 vertices commutes with restriction to any quartet in `Y`. Thus every switching's quartet topology is preserved, and therefore its distinct-topology set is preserved too.
3. Both adjacent boundary pairs stay adjacent in the reduced circular order. They were adjacent before deletion, so retaining additional anchors or hybrids cannot put a new label between them.
4. Each term of the coefficient is either 0, 1, or twice one of those preserved rho values. Coincidences among boundary leaves are preserved as well.

If this leaves fewer than four labels, retain one additional original label. A coefficient has at least three boundary labels, so one is enough, and the ordinary-arm bound remains six. The reduced network therefore has at most eight leaves, with four nonnegative arm counts totaling between two and six. There are `binom(10,4)-5=205` ordered templates. Arm order must be preserved; arbitrary regrouping of retained leaves is not permitted.

The independent [anchor_audit.py](anchor_audit.py) checks exactly those 205 templates, using graph distances instead of the parent's edge-split extraction. Its [receipt](anchor-audit.json) records:

| Check | Exact result |
|---|---:|
| Reduced templates | 205 |
| Anchor pairs | 4,313 |
| Circular coefficients | 100,787 |
| Coefficients equal to 0 | 77,287 |
| Coefficients equal to 1 | 19,440 |
| Coefficients equal to 2 | 4,060 |
| Negative coefficients | 0 |

For each finite template, every positive anchor split is displayed by some switching, and the union of anchor supports equals the displayed-split union. The reduction above establishes the route from the finite nonnegativity check to all canonical theta bloblets. For the general support conclusion, combine nonnegativity with the published unit-mass support theorem and the positive-weight identity; do not assume that a full-network split is determined merely by one restricted split.

This is an exact computational certificate plus a mathematical reduction argument. The reduction and evaluator have not been formalized in Lean in this lane. Its scope is the canonical single level-2 blob; it is not by itself the whole multi-blob conjecture.

## Exact bridge from masses to pendant clusters

There is a direct connection between the auxiliary weighted metric and real taxon multiplicities. Let each core leaf `x` be replaced across its pendant cut edge by a cluster `C_x` of `m_x>=1` leaves; the clusters may contain additional network structure, provided they attach through one cut edge and the resulting network is valid. Choose one representative `r_x` in each cluster and put `M=sum_x m_x`.

Define

```text
H_x = 2 sum_{z<w in C_x\{r_x}} rho_{r_x,t}(N|r_x,z,w,t),
```

where `t` is any leaf outside `C_x`. The displayed quartet set depends only on the attachment port and the three leaves within the cluster, so `H_x` is independent of the chosen outside leaf. Also `H_x>=0`.

For different core leaves `x,y`, partition the two witness leaves into six kinds:

| Witness locations | Contribution to d(r_x,r_y), excluding the constant |
|---|---|
| Distinct clusters z,w, neither x nor y | `2 m_z m_w rho_xy(core|xyzw)` |
| One in each endpoint cluster | `2(m_x-1)(m_y-1)` |
| One in an endpoint cluster, one in a third cluster | `2(m_x+m_y-2) R_xy` |
| Two in one third cluster | `0` |
| Two in C_x | `H_x` |
| Two in C_y | `H_y` |

The fixed topologies in the middle rows follow from the cluster cut edges. Adding `2M-4` and simplifying yields the identity

```text
d_expanded(r_x,r_y) = d_m(x,y) + P_x + P_y,
P_x = (m_x-1)(M-m_x+1) + H_x >= 0.
```

Thus representative distances differ from the weighted core metric only by nonnegative pendant terms. Nontrivial circular coefficients on the representatives are identical; the pendant terms contribute to trivial coefficients. This is a structural counting identity, not an assumption that weighted leaf counts automatically equal the full expanded metric.

[cluster_bridge_check.py](cluster_bridge_check.py) independently tests this identity on three actual expanded trees of clusters with 7, 8, and 10 total taxa, including a three-leaf hybrid-descendant cluster with `H_x=2`. All 45 representative distance comparisons pass; the [receipt](cluster-bridge-check.json) also records the parent comparison.

The remaining whole-network obligation is a gluing argument that accounts for all leaves within clusters, their internal splits, and cut-edge splits. The representative identity supplies a useful local ingredient but does not establish that entire step by itself.

## Acquisition limits

The publisher HTML and alphaXiv's exact-URL PDF text supplied the substantive definitions and proofs. The browser fetch of the university PDF was restricted, the publisher PDF click errored, and an attempted Figure 5 image retrieval returned an HTML response rather than image bytes. That response is preserved as `publisher-figure5-response.html`. No visual inspection of Figure 5 is claimed. The explicit specimen above is justified by its graph, embedding coordinates, and the canonical partition/switching description in the readable primary text.
