**Independent mathematical audit of the NANUQ attachment argument — 29 September 2026**

The proposed weighted-local reduction and global blob identity pass this audit, with the explicit support and small-port arguments below. An independent integer checker verifies all 100,823 anchor coefficients needed by the finite-compression argument, across 209 canonical theta templates. This is a mathematical argument with exact computational certificates, not a Lean kernel check or a publication/priority claim. The coordinator's final proof still needs to include the reduction, the local-to-global identity and exact support; a successful table alone is insufficient.

Primary correspondence: [Holtgrefe et al., arXiv2507.17308v2](https://arxiv.org/html/2507.17308v2), Definitions 2.1–2.5, Proposition 2.8, Lemma 3.2, Definition 4.1 and Section 4.1. The hypotheses are binary, semi-directed, LSA-rootable, outer-labeled planar and galled, with at most two hybrids per blob. The metric averages uniformly over distinct displayed quartets. Uniformly averaging distinct whole displayed trees is a different operation. The source's one-blob theorem supplies unit-mass positive support; it does not itself justify arbitrary terminal replication.

**1. Exact cherry identity, and why a generic shortcut fails.** Let v be a leaf of an n-leaf network and replace it by a cherry (v,v*). For ordinary a,b distinct from v, restriction of a quartet using v* but not v equals restriction using v. A quartet using both copies and a,b has the unique split vv*|ab. Consequently

    d'(a,b) = d(a,b) + 2 + 2 sum_{z not in {a,b,v}} rho_ab(abvz),
    d'(a,v) = d'(a,v*) = d(a,v) + 2n - 2,
    d'(v,v*) = 2n - 2.

These identities use distinct-quartet normalization, including deduplication. They require no multiplication by hybrid-switching multiplicities.

The artificial circular tree family on order 0,1,2,3,4,5 with internal split sides

    T1: 01, 015, 0125;
    T2: 012, 0123, 0345;
    T3: 0123, 045, 0145

has a uniform-distinct-quartet metric whose positive support is exactly the union of those trees' splits. For the displayed split 23|0145 its coefficient is 1. Cloning leaf0 once makes the lifted coefficient zero; cloning it twice makes it -1. Direct quartet recomputation independently verifies the sequence 1,0,-1. Thus circular decomposability and exact support of the original unit metric alone do not imply attachment closure.

This is not an admitted counterexample to the published conjecture. The family is an overapproximation of possible network-displayed families, and no admissible galled level-2 realization is supplied. Our restricted canonical anchor certificate instead passes. The broad-family control checked all nonempty circular-tree families through six leaves: 3, 31 and 16,383 families at n=4,5,6. Its counts and witness are in [circular-family-search.json](circular-family-search.json). This search's role is to falsify the generic shortcut, not to count admissible networks.

**2. The correct weighted local object.** For positive terminal masses m_x, define W on the ports of a blob by zero diagonal and

    W_m(x,y) = 2 sum_{p<q, p,q outside {x,y}} m_p m_q rho_xy(xypq)
               + (m_x+m_y) sum_{p outside {x,y}} m_p.

For distinct anchors p,q let M^{pq}(x,x)=0, and off the diagonal set M^{pq}(p,q)=0, M^{pq}(x,y)=1 when {x,y} meets {p,q} in exactly one point, and M^{pq}(x,y)=2 rho_xy(xypq) when all four labels differ. Expanding by anchor type gives the exact identity

    W_m = sum_{p<q} m_p m_q M^{pq}.

It follows that alpha(W_m)=sum m_p m_q alpha(M^{pq}). If every anchor coefficient is nonnegative, positive masses preserve exactly the support of W_1: a sum is zero precisely when all its nonnegative summands are zero. Hence the existing unit-support theorem supplies exact weighted support after anchor positivity is established. This works for arbitrary strictly positive real masses, and in particular for positive integer leaf counts.

W_m is not by itself the matrix of distances between chosen representatives after leaf cloning. For a single clone, the core mass m_v=2 changes W(a,v) by n-2, while the additional ordinary three-port tree vertex contributes n; together they give the correct 2n-2. Omitting tree-vertex blobs would break the literal global distance identity.

**3. Finite-compression proof and independent certificate.** In a canonical strict level-2 bloblet, each alpha(M^{pq}) refers to at most the six labels a,b,c,d,p,q, where a,b and c,d are the two tested circular adjacencies. Retain those labels and the two hybrid leaves C1,C2. Delete all other ordinary arm leaves and suppress the resulting degree-two arm vertices.

This preserves the order of retained leaves on each arm. In each of the four choices of hybrid incoming edges, restricting to any queried quartet before or after suppression gives the same quartet tree. Thus the distinct quartet sets, their cardinalities and all four matrix entries in the tested coefficient are unchanged. Original adjacent retained pairs remain adjacent in the restricted circular order. Retaining both hybrid leaves ensures the remaining object is still a canonical theta with at most six ordinary leaves. No assertion about multiplicity-free means over whole trees is used.

There are 209 arm-count tuples with 1<=a1+b1+a2+b2<=6. Include the four three-leaf cases, or handle them analytically as stars. Counting only the n>=4 cases gives 205 and misses those four cases in a literal exhaustive checker. A coefficient needs at least three distinct endpoint labels, so the zero-arm, two-port theta is not required by this compression; its weighted metric is separately zero.

[Independent checker](independent_anchor_check.py) builds the four switched trees directly. It determines every quartet from graph distances using the four-point test, without importing the coordinator's checker or using its tree simplification/split extraction. All arithmetic for anchor coefficients is integer arithmetic. It verified:

- 209 canonical templates, with three through eight leaves;
- 100,823 anchor/split coefficients;
- zero negative coefficients;
- coefficient histogram 0:77,311; 1:19,440; 2:4,072;
- the weighted anchor expansion at a nonuniform positive integer mass vector for every template;
- the artificial clone witness by direct, rather than formula-based, recomputation.

Receipt: [independent-anchor-check.json](independent-anchor-check.json). Checker SHA256: `5f663e6be7acacdb7183dfc89950302b6999ccc252d2ff19cb7a106ce05da225`. This verifies the finite table. The preceding suppression argument is what turns the table into a general canonical-theta statement.

**4. Why the global identity holds.** Include every non-leaf bridge-free component B, including isolated ordinary tree vertices. Each incident cut edge determines a port and a nonempty external leaf block. These blocks partition the global leaf set. Let m_B be their cardinalities and pi_B map a global leaf to its port. The candidate identity is

    d_N(x,y) = sum_B W_{B,m_B}(pi_B(x), pi_B(y)).

The tree part has a short direct proof. In a displayed binary tree T, fix x,y. The offshoot subtrees along their path have sizes c_1,...,c_k and partition the n-2 remaining leaves. A quartet separates x,y exactly when its other two leaves lie in different offshoots. Therefore

    d_T(x,y) = 2 sum_{i<j} c_i c_j + 2(n-2)
             = sum_i c_i(n-c_i).

The final expression is a sum over the path's internal vertices. Its weighted-port version gives the displayed-tree W_m formula. Each surviving internal vertex comes from a unique original blob. Grouping those vertices by blob, and then averaging uniformly over all hybrid switchings, yields the global identity for the multiplicity-weighted quartet metric. Suppressed degree-two vertices contribute zero. Local choices extend independently to global choices, so averaging outside a blob adds only a constant multiplicity factor.

For the NANUQ correction, inspect the tree of blobs restricted to a quartet. If a cut edge separates its leaves 2+2, every displayed quartet has that same split, so the distinct-quartet and switching-weighted values agree. Otherwise its reduced blob tree is a four-leaf star with a unique central blob, and the four leaves use four distinct ports there. All topology and normalization relevant to the correction then comes from that blob. Summing over the other two leaf blocks contributes exactly m_p m_q. Corrections vanish at all other blobs for that quartet. Summing them gives the stated identity.

This argument needs nonempty port blocks, a genuine tree of blobs, and the restriction/extension correspondence for switchings. They follow in the source's LSA binary network class but should be stated, not inferred merely from drawing two reticulate pieces. The correction step is essential: averaging distinct global displayed trees would not prove this identity.

**5. Exact global support, including small-port components.** Port blocks occur consecutively in the global outer-face circular order. Therefore a positive local circular split lifts to a positive circular split of global leaves. Every local displayed tree choice extends to a global switching, so every lifted local displayed split is globally displayed.

For the converse take any edge split of a global displayed binary tree T. Since n>=4, that edge has an internal endpoint u. This surviving degree-three vertex belongs to a unique original blob B. In the switched local tree on B's ports it still has degree three, so B has at least three ports. The local incident edge or suppressed path induces exactly the original global split when port blocks replace port labels. Thus every globally displayed split occurs among the lifted displayed splits of blobs with at least three ports.

A two-port blob has W=0 and does not invalidate this converse. Its cut split is represented by a local edge at a surviving adjacent branching vertex, rather than receiving a positive contribution from the two-port blob itself. An isolated degree-three tree vertex is a three-port star and must be included; its weighted pendant split coefficients are positive products of the other two masses.

Level-1 blobs also satisfy weighted positivity without new finite search. Their distinct-quartet mean equals the uniform switching mean, so their W is an average of weighted tree metrics. For a tree and fixed anchors p,q, M^{pq} is the sum of split metrics of the offshoot leaf blocks along the p-to-q path. This directly proves nonnegative anchor coefficients. Every displayed tree edge split occurs in some such anchor metric; positive masses retain all displayed splits. Two-cycles and three-port cases are handled by the same zero/star conventions. The Python simple-graph enumeration does not itself represent parallel edges; the mathematical small-port argument is required for those source-permitted cases.

Consequently local nonnegative coefficients, the weighted exact-support step, and the global identity together give exactly the union of global displayed splits, with no cancellations and no spurious support. This is the required support argument, rather than nonnegativity alone.

**6. Audit of the coordinator's implementation.** I inspected `exact_networks.py`, including the added `local_decomposition`. No central mathematical defect was found. The rotation-system/Euler/outer-face checks certify the supplied combinatorial embedding; rooted degrees, acyclicity, dominators and hybrid articulation test correspond to the stated class. Quartets are deduplicated after restriction, and rational division uses the number of distinct quartet splits. The mass formula expands exactly into the anchor matrices. The local decomposition includes isolated non-leaf vertices and explicitly verifies nonempty port blocks and the leaf partition.

A reporting hardening is advisable before issuing a proof-certificate receipt: `main` can break after an anchor failure while still writing `PASS_UNIT_METRICS`. That status is accurate only for unit metrics already checked. A certificate for the finite reduction must additionally require all 209 templates, all 100,823 anchor tests, and zero negative anchor counts. Freeze the source hashes after edits. No claim about full class coverage should be based solely on the 221 example count, which includes 12 attachment controls.

This audit supports the proposed full proof route. It does not substitute finite tests for the compression and gluing lemmas, prove consistency from finite genomic observations, or certify worldwide priority. The independent certificate and the written reductions should remain separately identifiable in the final result.
