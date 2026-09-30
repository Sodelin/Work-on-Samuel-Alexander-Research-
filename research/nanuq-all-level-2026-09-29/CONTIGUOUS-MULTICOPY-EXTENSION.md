# Contiguous multicopy blocks reduce to their extreme occurrences

Date: 29 September 2026.

**Status: proved.** In a finite plane binary tree whose occurrences of each taxon form one nonempty contiguous block in the cyclic tip order, retaining only the first and last occurrence of every block preserves the entire system of distinct displayed quartets. It also preserves the union of displayed splits. It need not preserve the family of full displayed trees or any occurrence-weighted probability distribution.

This is an abstract plane-tree theorem. No biological network with higher hybrid indegree is automatically admitted by it. Such an application would first require a separate source-to-contiguous-block representation proof.

## 1. Exact statement

Let T be a finite unrooted plane binary tree. Partition its physical tips into nonempty taxon blocks B_x, indexed by a taxon set X with |X|>=4. Each block is contiguous in the cyclic tip order, and different blocks carry different labels. Fix either orientation of that cyclic order. For each x retain the two extreme occurrences of B_x, retaining just one occurrence if its block is a singleton. Let E be the set of retained occurrences, and let T_ext be the minimal subtree connecting E, with degree-two vertices suppressed.

A displayed tree on X is obtained by selecting one physical occurrence from every block, restricting to those selected tips, suppressing degree-two vertices, and replacing occurrence names by taxon labels. For a four-label set Q, let Q_T(Q) be the set of quartet topologies obtainable by such selections; choices for labels outside Q are immaterial.

Then, for every four-label set Q,

    Q_T(Q) = Q_T_ext(Q).                                      (1)

The selected extreme occurrences are still adjacent pairs or singletons in the induced cyclic order of T_ext. Thus T_ext lies in the paired-tip representation class already checked in this project, and has at most 2|X| physical tips.

The operation is independent of cyclic starting point. Reversing the order exchanges first and last within each block and does not change E. Statements with fewer than four labels have no quartet content; ordinary tree restriction and the small-label conventions still apply.

## 2. The one-block lemma

Fix three physical tips a,b,c belonging to three labels other than x. Their unique median v in the binary tree T has degree three. Deleting v gives three components A,B,C, containing a,b,c respectively.

The physical leaf sets of A,B,C are three disjoint cyclic intervals partitioning the tip circle. This follows directly from the plane embedding: each of the three incident edges cuts off one contiguous contour interval.

The block B_x avoids a,b,c. Because B_x is contiguous, it is contained in one of the three open circular arcs between these selected tips. Along such an arc, at most one boundary between A,B,C occurs: for example, the arc from a to b that avoids c consists of a terminal part of A followed by an initial part of B. Therefore B_x meets at most two median components. If it meets two, its first and last occurrences lie in the two different components; if it meets one, both extremes lie in that component.

For any selected occurrence u in B_x, the quartet on {u,a,b,c} is determined solely by the median component containing u. If u lies in A, the edge from v into A separates u,a from b,c, so the restricted quartet is ua|bc. The other components give ub|ac and uc|ab, respectively. The preceding interval argument shows that one of the two extreme occurrences of B_x is in the same component as u. Replacing u by that extreme consequently preserves the quartet topology after its taxon label is restored.

This proves the one-block lemma. It uses binary degree at the median and contiguous blocks; it does not infer a general statement from finite examples.

## 3. Successive replacement proves (1)

Take an arbitrary quartet topology in Q_T(Q), witnessed by four selected physical tips with four distinct taxon labels. Apply the one-block lemma to the first label, holding the other three selected tips fixed, and replace its occurrence by an extreme of its block without changing the quartet topology.

Repeat for each of the other three labels. Previously replaced occurrences remain fixed when applying the next lemma; they still belong to other blocks, so all hypotheses continue to hold. After four steps the same quartet topology is witnessed entirely by tips in E. Restriction of a tree is associative, so restricting T to those four tips is the same as first constructing T_ext and then restricting to them. This proves Q_T(Q) is contained in Q_T_ext(Q).

The reverse containment is immediate because E consists of original tips. Thus (1) holds for every quartet simultaneously as an equality of sets. The endpoint choices used to witness one quartet need not be the same choices used for another quartet. No claim of one globally preserving selection is made.

## 4. Consequences for the original distance and its support

Both representations induce the same circular taxon order C, obtained by replacing each nonempty occurrence block by its label. Every selected full tree is circular in this order.

Define rho_T,Q(x,y) to be the uniform average of the cherry-separation indicator over the DISTINCT topologies in Q_T(Q). Equation (1) preserves every such rho exactly. Therefore it preserves the original abstract NANUQ distance

    d_T(x,y) = 2 sum_{{z,w} subset X minus {x,y}} rho_T,{x,y,z,w}(x,y)
               + 2|X|-4,

with zero diagonal. The number in the constant is the number of taxon labels, which is unchanged, not the number of physical occurrences.

It also preserves every two-anchor matrix and every positively port-weighted local matrix built from these rho values. Consequently the already established circularity theorem for adjacent singleton/doubleton representations extends to arbitrary finite contiguous multiplicities.

For support, use the structural boundary-quartet criterion in `ALL-LEVEL-SUPPORT-STRUCTURAL-AUDIT.md`. A nontrivial circular split with boundary gaps (a,b),(c,d) belongs to the union of displayed-tree splits if and only if bc|ad belongs to the corresponding quartet set. Those sets agree by (1); trivial splits are present in every displayed full tree. Hence

    union of splits of all trees selected from T
      = union of splits of all trees selected from T_ext.      (2)

Together with equality of the original distance, the accepted exact-support theorem for the paired-tip class extends to the contiguous-multicopy class. This support statement concerns the union of splits, not equality of the full tree families.

## 5. Transfer of a score-parameter domain

Any quartet-based score formula determined only by Q_T(Q), the common circular taxon order, and taxon-level masses takes exactly the same values before and after this reduction. This includes the quartet score parameters considered in the other lane of this project.

For each fixed label set and circular order, the collection of complete distinct-quartet systems realizable by arbitrary nonempty contiguous blocks is therefore **exactly** the collection realizable with blocks of size at most two: equation (1) proves one inclusion, and the paired-tip class is already a subclass of the multicopy class.

Thus a universal admissible parameter domain for such score formulas is identical for the two abstract representation classes. Any parameter theorem already proved for the paired-tip class transfers, and any paired-tip counterexample remains a counterexample in the larger class. This note does not supply numerical parameter bounds or independently certify the other lane's parameter calculations. It establishes the reduction on which their transfer rests.

## 6. The full tree family can shrink: an explicit small example

Consider the five-vertex backbone

    v0 -- v1 -- v2 -- v3 -- v4.

Attach physical tips a,x0 at v0; c at v1; x1 at v2; d at v3; and b,x2 at v4. This is a binary caterpillar with seven physical tips. It has a plane embedding with cyclic order

    (a, x0, x1, x2, b, d, c),

so x0,x1,x2 form one contiguous three-occurrence taxon block x; the four other labels are singletons. Keep x0,x2 and delete the middle occurrence x1.

The two nontrivial splits of the five-label selected tree are:

| Selected occurrence of x | Nontrivial splits |
|---|---|
| x0 | $`ax\mid bcd`$; $`acx\mid bd`$ |
| x1 | $`ac\mid bdx`$; $`acx\mid bd`$ |
| x2 | $`ac\mid bdx`$; $`acd\mid bx`$ |

Here each vertical bar inside the displayed split notation denotes a bipartition. The middle-copy tree is different from both extreme-copy trees, so it disappears from the full tree family. Each of its splits is nevertheless supplied by an extreme-copy tree. All five four-label subsets retain the same quartet sets.

A direct exact check of this one caterpillar confirmed the three split lists, the lost middle tree, equality of the split unions, and equality of all five quartet sets. It used at most five labels and three copies of one label, generated no other trees, and wrote no program or receipt files. The general result is the proof in Sections 2-3, not this check.

## 7. Limits and final verdict

The reduction preserves distinct quartet sets, the common taxon order, their quartet-based distances and anchor matrices, and the union of displayed splits. It does not preserve all full displayed trees, the numbers of occurrence selections giving a topology, or probability distributions weighted by those selections.

The present proof assumes a plane binary tree and one contiguous block per taxon. It makes no assertion for interleaved blocks, nonbinary median vertices, infinite trees, or choices constrained across taxa. A higher-indegree biological model is covered only after separately proving that its displayed-quartet semantics admit this independent contiguous-block representation.

**The requested lemma is complete, with no unresolved mathematical gap in its stated scope.** Only `CONTIGUOUS-MULTICOPY-EXTENSION.md` was written. Existing checks, proof sources, Git state, and external publication records were left untouched. No new agents or literature searches were used.
