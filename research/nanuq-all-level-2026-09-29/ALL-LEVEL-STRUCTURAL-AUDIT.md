# All-level structural audit: paired-tip representation and six-taxon reduction

Date: 29 September 2026.

**Verdict: accept the structural reduction for finite binary, semi-directed LSA, outer-labeled planar, galled bloblets.** No bound on the number of hybrids is used in the proof below. One deletion instruction must be repaired: take the minimal subtree spanning the retained tip occurrences, or recursively prune unlabeled leaves, before suppressing degree-two vertices. One-pass deletion followed only by degree-two suppression is not sufficient as a graph construction.

This is a focused mathematical audit of the source-to-representation bridge. It does not certify a fresh execution of the Python program, establish an all-level displayed-split support theorem, classify canonical forms, or prove a result for arbitrary networks with multiple blobs. The finite screen is used only after the structural reduction, not as evidence for its validity.

## 1. Exact scope and source locators

The source class is the binary class in Holtgrefe et al., *Distinguishing Phylogenetic Level-2 Networks with Quartets and Inter-Taxon Quartet Distances*, Bulletin of Mathematical Biology 87:168 (2025), DOI [10.1007/s11538-025-01549-4](https://link.springer.com/article/10.1007/s11538-025-01549-4). Relevant locators are Definitions 2.1-2.4 (rooted LSA, semi-directed, galled, bloblet, outer-labeled planar, and level), the displayed-tree definition immediately after Definition 2.5, Lemma 3.2 and its multiplicity identity, and Section 4 Equation (10) and Definition 4.1. The last paragraph of Section 6 poses the level-three bloblet conjecture. The January 2026 correction restores Figure 12b and states that results are unaffected.

The second source is Allman et al., *Beyond Level-1: Identifiability of a Class of Galled Tree-Child Networks*, Bulletin of Mathematical Biology 87:166 (2025), DOI [10.1007/s11538-025-01545-8](https://link.springer.com/article/10.1007/s11538-025-01545-8). Use Section 2.3 Definition 1 and Lemma 2.1, and the **paragraph before Figure 4 in Section 3**. The latter gives root-skeleton connectivity for galled bloblets without a tree-child assumption. Lemma 3.1 adds tree-child to exclude unlabeled skeleton leaves; that additional conclusion is unnecessary here.

The proof below assumes at least three taxa; this includes every original network in the conjecture, which has at least four. The compressed coefficient witnesses may have three taxa. A trivial internal blob is handled directly as a tree. For a nontrivial internal blob, all the face arguments below apply. Parallel edges, where applicable, are counted as separate incidences and a facial bigon as a cycle.

No assertion that every enumerated paired-tip tree arises from a bloblet is required. The needed direction is that every source network has an enumerated representation after restriction.

## 2. Representation theorem

Let N be a network in the stated class, with taxon set X and k hybrid vertices. Fix an outer-labeled planar embedding. For each hybrid h with child taxon x, replace the two incoming edges u-h and v-h by two pendant edges u-x^(0) and v-x^(1), retaining their incidence positions in the plane rotation system. Remove h and its pendant taxon edge. Keep each non-hybrid taxon as one tip.

Call the resulting plane graph T and regard x^(0), x^(1) as distinct **occurrences** carrying the same taxon label x. Then:

1. T is a plane binary tree, with one occurrence of each ordinary label and two occurrences of each hybrid label.
2. The two occurrences of every hybrid label are consecutive in T's cyclic tip order.
3. Collapsing each adjacent pair to its taxon label gives the circular taxon order of the chosen embedding of N, up to rotation and reversal.
4. The trees displayed by N are exactly the trees obtained from T by choosing one occurrence of each hybrid label, keeping each ordinary tip, taking the connecting subtree, suppressing degree-two vertices, and forgetting occurrence superscripts.

### 2.1 Why the remaining graph is a tree

Let B be the single non-leaf blob. Every hybrid is a boundary vertex of B: this is the binary galled property. Its two incoming edges lie in B, and its child edge is a cut edge. As N has no other non-leaf blob, the child is a taxon. Thus different hybrids have different child taxa, and no hybrid is ancestral to another hybrid.

Delete each hybrid together with its child taxon and all three incident edges. The remaining graph R contains all the tree nodes and all ordinary taxon leaves. It is connected and acyclic. This is precisely the unreduced root-skeleton statement in Allman et al., Section 3; it also follows directly in any rooted partner: every remaining vertex is reached from the root by a directed path that cannot pass through a hybrid, since a hybrid's only descendant is its taxon. The remaining non-root vertices have at most one incoming edge, so these paths form a tree. Suppression of the former degree-two root does not create a cycle or disconnect this remaining component.

R may have unlabeled leaves or vertices of degree two. Do not claim that R alone is a phylogenetic tree, and do not invoke the stronger tree-child conclusion of Allman et al.'s Lemma 3.1. Appending the two new tips for each removed hybrid restores exactly the deleted incidence at every parent. Therefore every original tree node has degree three in T, every retained taxon and new occurrence has degree one, and T is connected and acyclic. This proves assertion 1 even if R had zero or one ordinary taxon.

### 2.2 One bounded face per hybrid

Work in B, with pendant taxon edges removed but their original attachment corners remembered. A nontrivial bridgeless graph of maximum degree three cannot have a cut vertex: each component at such a cut vertex would require at least two incident edges to avoid a bridge, demanding degree at least four. Thus B is 2-connected. Its face boundaries are cycles, including possible bigons.

The cyclomatic number of N, and hence of B, is k. For example, in a rooted partner every non-root non-hybrid vertex contributes one to its indegree and every hybrid contributes two, giving E-V+1=k; root suppression and pendant-edge removal preserve this number. Euler's formula therefore gives exactly k bounded faces of B.

Each hybrid h has degree two inside B. The pendant edge to its taxon occupied an outer-face corner, because the taxon was on the unbounded face of N. Consequently h is incident to the outer face of B. Since B has no bridges, its two incident edges separate two distinct faces. At its degree-two vertex there are exactly two incident face sectors, so h is incident to **exactly one** bounded face, denoted F_h.

Every bounded face of B contains at least one hybrid. Otherwise its facial cycle would consist entirely of edges and vertices of R, contradicting that R is a tree. Counting incidences now finishes the argument: there are k hybrids, each incident to precisely one bounded face, and k bounded faces, each incident to at least one hybrid. Therefore every bounded face contains exactly one hybrid, and h -> F_h is a bijection.

It is not enough merely to observe that there are k bounded faces. The facts that each hybrid has exactly one bounded-face incidence and that every bounded face has one are both necessary.

### 2.3 The contour argument, including taxon order

The boundary of F_h consists of the two incoming edges at h and a tree path P_h joining their parents. No other hybrid lies on this boundary, by the preceding count. No ordinary taxon edge is attached into a corner of F_h: such a pendant edge would place that taxon in a bounded face of N, contrary to the chosen outer-labeled embedding.

After h is opened into two tip occurrences, trace the contour from x^(0) towards its parent, along the old F_h side of P_h, and out to x^(1). At every intermediate vertex the next contour edge is the next edge of the old face boundary. There is no pendant taxon in one of these corners, and no other opened hybrid is encountered. Replacing edges of other hybrids by stubs retains their original incidences and does not alter these face-side turns. Hence this contour segment contains **no other tip**. The two occurrences of x are consecutive.

For the order statement, trace the original outer-face boundary of B, with its pendant taxon excursions. At an ordinary taxon the excursion is unchanged. At a hybrid taxon x, opening h replaces the former excursion to x by a detour through x^(0), the tip-free F_h boundary path, and x^(1). Every bounded face is inserted exactly once, since the faces F_h exhaust the bounded faces. No further tip is inserted in any such detour. Thus each former hybrid label is replaced in place by its adjacent pair, and all other labels retain their cyclic order. This proves assertions 2 and 3. It is a face/rotation-system argument, not an inference from pictures of low-level examples.

### 2.4 Switchings are occurrence selections

Fix a switching: at every hybrid retain exactly one incoming edge and delete the other. Since its child is a taxon, the retained parent-h-taxon path becomes a pendant taxon edge after h is suppressed. This is exactly what choosing the corresponding occurrence in T does. The unused occurrence is deleted. Any remaining unlabeled dangling branches are pruned and degree-two nodes suppressed in either construction. Both constructions yield the same labeled tree.

Conversely, every independent choice of one occurrence for every hybrid label specifies one incoming edge to retain at each hybrid, hence a switching of N. There is no compatibility condition coupling choices at different hybrids. Distinct choices may produce the same tree; this is why the output is a set of distinct trees when multiplicities are ignored.

For every four-label set Q, this correspondence also gives equality of displayed quartet **sets**. Restricting a switched tree to Q commutes with its tree pruning and suppression. That the source's induced quarnet definition has this same support is explicitly contained in the multiplicity identity in the proof of Holtgrefe et al., Lemma 3.2: a quartet has positive multiplicity in N|Q exactly when it is the restriction of a displayed tree of N. The identity is used for support here, not to replace the source's unweighted average with a multiplicity-weighted average.

## 3. Correct deletion lemma

Let Y be any retained taxon subset with |Y| >= 3. In T keep the unique occurrence of every ordinary taxon in Y and **both** occurrences of every hybrid taxon in Y. Remove every occurrence of a taxon outside Y. Define T_Y to be the minimal subtree connecting the retained occurrences, with all degree-two vertices suppressed.

This definition includes recursive pruning of newly unlabeled degree-one vertices. It cannot be replaced literally by one-pass removal of unwanted labeled tips and degree-two suppression: deleting both leaves of a cherry leaves its former parent as an unlabeled degree-one vertex. This is a wording/construction repair, not a counterexample to the restriction theorem.

T_Y is a plane binary tree with at most 2|Y| tips. Its cyclic occurrence order is obtained from that of T simply by deleting the unwanted occurrences. Suppressing degree-two vertices does not change contour order. Adjacent retained pairs stay adjacent, and the taxon order obtained by collapsing them is the restriction of N's original circular order to Y.

Write T[s] for the reduced tree selected by a global occurrence choice s. For any choice t on retained hybrid taxa, every extension s to all hybrid taxa satisfies

    T[s] restricted to Y  =  T_Y[t].

The equality is up to the natural labeled tree isomorphism. One way to see it is that in a tree the minimal subtree connecting a set of leaves is the union of the unique paths between those leaves. Removing leaves outside that set, before or after a larger restriction, cannot change these paths. Suppression only replaces path segments by single edges.

Every t extends to an s, so the sets of trees obtained on Y agree exactly. In particular every displayed quartet on Y is preserved. Taxa deleted outside Y cannot affect which of the retained quartet topologies exist. This is the precise reason the construction may discard **all** unused hybrid taxa, even if the original reticulation level was arbitrarily large.

The object T_Y is a representation. It need not correspond to a bloblet after gluing its pairs; deletion is not claimed to preserve the original network class. The screen ranges over all paired-tip trees, so this causes no coverage gap.

## 4. Six-taxon coefficient coverage

For fixed distinct anchors p,q, the matrix entry M^(pq)(u,v) depends only on:

- whether u=v or {u,v}={p,q};
- whether exactly one of u,v is an anchor; or
- the set of displayed quartets on {u,v,p,q}, when those four labels are distinct.

A circular boundary coefficient uses four such entries, at the two boundary gaps (a,b) and (c,d):

    alpha = M(a,c) + M(b,d) - M(a,d) - M(b,c).

Take Y={p,q,a,b,c,d}. Then |Y| <= 6, and |Y| >= 3 for two distinct gaps in an original circular order of size at least four. All displayed quartet sets used in the four entries are preserved by Section 3, as are the anchor identities and repeated-label cases.

Both ordered gaps remain gaps in the restricted circular order: if a and b were consecutive originally and both are kept, deleting other taxa cannot insert a label between them. The same holds for c,d. The two gaps remain distinct. Hence the same coefficient occurs on T_Y, with precisely the same value, and T_Y has at most twelve tips arranged in single-label or adjacent-double-label blocks.

This proves the source-to-finite-representation implication for **every** finite k. It does not require a bound on k, a classification of level-k cores, or retaining the k hybrid taxa. The larger nine-taxon level-three compression in LEVEL3-CANDIDATE.md is therefore unnecessary for this representation-based route.

## 5. Match to the program's representation domain

The source code read in this audit has the appropriate combinatorial domain:

- `systems(n, duplicated)` creates every choice of singleton/doubleton blocks for 3 <= n <= 6.
- Fixing tip occurrence 0 as the distinguished pendant root leaves an ordered full binary tree on occurrences 1 through m-1. The recursion over every `mid` enumerates its interval bipartitions; this represents every plane binary tree on the m fixed cyclic occurrences. Cutting immediately before label 0's block avoids splitting a doubleton across the linear endpoints.
- For an edge split, `contribution` records a quartet topology precisely when occurrences of its first two distinct labels can be chosen on one side and occurrences of its other two labels on the other. Those four choices are independent and extend to a selection on all other labels. Conversely every selected-tree quartet split comes from an edge of the original tree.
- OR across the tree's edge contributions therefore records the set of all possible quartet topologies, not a single joint selection or a multiset. Deduplication by this OR-pattern at a fixed interval is compositionally valid: outside contributions depend on the interval and its label occurrences, not on which representative subtree realizes the same OR-pattern.

These observations connect the mathematical reduction to the intended computation. They are a source-code reading, not an independently implemented or freshly executed certificate. The supplied JSON records 102 distinct six-label systems and 22,950 anchor coefficients for that row, with no negative coefficient. Lower rows record 1, 3, and 16 systems for three, four, and five labels. In total it records 24,667 coefficient checks over 84,076 represented plane trees. Those counts describe the file read, not an independent rerun.

## 6. Remaining obligations and precise conclusion

The adjacent-pair lemma, circular-order correspondence, switching support equality, and six-taxon deletion reduction have complete arguments above. The sole necessary repair to the proposed structural wording is explicit minimal-subtree restriction / recursive pruning.

To assemble a computer-assisted all-level NANUQ theorem, the integration lane must still own verification that the exact program execution and coefficient convention match the supplied source and certificate, and that the nonnegative anchor coefficients are summed using the correct entrywise distance identity and circular reconstruction formula. No fresh run or independent implementation was performed in this focused audit. Software/kernel certification, publication priority, biological inference, canonical-form recovery, and an all-level equality of decomposition support with displayed splits are not proved by this note.

**Conditional handoff:** if the finite paired-tip coefficient assertion computed in `all_level_screen.py` is accepted as an exact certificate, Sections 2-4 transfer it to every anchor coefficient of every network in the stated binary galled outer-labeled planar bloblet class at every finite reticulation level. The transfer is proved structurally and does not extrapolate from finitely many network examples.

## 7. Inputs and access record

Read-only inputs, SHA256:

- `all_level_screen.py`: `504f8985247d12914a26fcae9eaab2d160dcc037ec26de97ac406cc2f2432d18`
- `all-level-screen.json`: `fa60e8d87b20ce5b9be21c0681d15b89ad026c519e0cadd2736c5ebcf5a513c5`
- `LEVEL3-CANDIDATE.md`: `8da95943c86d6bae5f02829cd500b83c170f17d06b27cf7d383d0c44d5aa1af6`

Only this audit file was written. No proof source, JSON result, Git state, or external site was changed. The screen was not executed.

Source access on 2026-09-29: initial DOI opens failed; PMC direct access returned a browser-check page; an institutional PDF open failed. Indexed source passages identified the definitions, and the two Springer article pages subsequently opened successfully. The final mathematical source checks used their explicit section/definition/lemma locators listed above. The correction notice was checked only for its effect on the stated target. No broader literature search was undertaken. No verbatim source passage is reproduced.

## 8. Comparison with the integration proof, Sections 1-3

I subsequently read `ALL-LEVEL-PROOF.md`, Sections 1-3, after the integration lane requested a bounded comparison. Those sections match the accepted reduction above. Section 3 now explicitly takes the spanning subtree, so it incorporates the recursive-pruning repair.

For a self-contained final version, Section 1 should retain or cite the two details supplied by this audit: (i) the single binary nontrivial blob is 2-connected, which licenses the facial-cycle argument and unique bounded-face incidence at a hybrid; (ii) replacing each hybrid's original outer-face excursion by the paired-tip detour preserves the original taxon order after each pair is collapsed. Pair adjacency alone should not silently substitute for that taxon-order correspondence. Section 2's word 'pruning' is understood recursively, as in the source definition of a displayed tree; taking the connecting subtree is an unambiguous equivalent.

The root-skeleton citation is the paragraph before Figure 4 in Allman et al., Section 3. It applies to galled bloblets generally. The stronger Lemma 3.1 assumes tree-child in order to assert that the root skeleton itself has no unlabeled leaves. This proof does not need that additional assertion.

Sections 4-6 of the integration proof were outside the requested structural sign-off. The local structural acceptance therefore does not independently certify those computational and assembly sections or the proposed multi-blob extension.
