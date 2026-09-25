# Maximal specieslike clusters: source and theorem audit

Date: 2026-09-25. Mode: pinpoint primary-source audit and independent mathematical analysis. Status: handwritten proofs reviewed here; no new Lean certification is claimed by this note.

## Finding

The proposed descendant-closure theorem is correct for a cluster maximal **among all specieslike clusters**. It is false for the constrained maximal sets used in Alexander's main existence theorem. The distinction must appear in the theorem name, assumptions, and explanatory prose.

The general descendant-closure statement was not located explicitly in the inspected paper. It is a short structural consequence of the definitions, with a special-case enlargement argument already present in the paper. A suitable attribution is **a derived lemma about Alexander's specieslike-cluster definition**, accompanied by the exact scope below. This audit does not establish global novelty.

## Primary-source locations

Samuel Allen Alexander, *Specieslike clusters based on identical ancestor points*, arXiv:2602.05274v1, 2026-02-05. [Versioned full text](https://arxiv.org/html/2602.05274v1), [versioned PDF](https://arxiv.org/pdf/2602.05274v1). Page numbers below are printed pages, equal to one-based PDF pages.

| Location | Relevant source content |
|---|---|
| Definitions 1–2, p. 4 | Finite birthdate sublevels; IAP permits finitely many descendants or finitely many non-descendants within the set. |
| Definition 3, p. 8 | Convexity includes every organism between two members in the ancestry order. |
| Definition 4, p. 9 | Specieslike clusters are connected, convex, and satisfy IAP. |
| Remark 3 and footnote 5, p. 9 | Unrestricted maximality; a two-branch example has no maximal cluster containing its root. The argument enlarges a finite branch segment by one vertex. |
| Definitions 8–9, p. 12 | Common ancestor and reflection properties. |
| Definition 11, p. 15; Theorem 13, pp. 16–17 | Maximality within IAP, convexity, common ancestry, and reflection; every vertex belongs to such a constrained maximum. |
| Example 14(2), p. 17 | Two-way splitting gives constrained maxima containing a branch and the shared past. |

## Exact mathematical conventions for this audit

Let $`G=(V,E)`$ be a directed acyclic graph. Write $`u\prec v`$ when a nonempty finite directed path leads from $`u`$ to $`v`$. Connectivity means connectivity in the underlying undirected graph induced by the set.

For a set $`S\subseteq V`$, use the following working predicates:

```math
\begin{aligned}
D_S(v)&=\{w\in S:v\prec w\},\\
\operatorname{IAP}(S)&\iff
  \forall v\in S,\quad
  D_S(v)\text{ is finite}\ \lor\ S\setminus D_S(v)\text{ is finite},\\
\operatorname{Conv}(S)&\iff
  \forall a,c\in S\ \forall b\in V,\quad
  a\prec b\prec c\Longrightarrow b\in S.
\end{aligned}
```

The term **unrestricted maximal** here means that $`S`$ is a specieslike cluster and every specieslike cluster $`T\supseteq S`$ equals $`S`$. In particular, the entire ambient vertex set is an allowed competitor when it is a specieslike cluster. The word “proper” must modify *superset*, not *ambient subset*.

## Independent proof A: finite enlargement

**Lemma.** Suppose every vertex has finitely many ancestors. If $`S`$ is a specieslike cluster and $`y\notin S`$ has an ancestor in $`S`$, then there is a specieslike cluster properly containing $`S`$, differing from it by finitely many vertices, and containing $`y`$.

Define the finite connecting region

```math
F=\{y\}\cup
\{z\in V:z\prec y\ \land\ \exists s\in S,\ s\prec z\},
\qquad T=S\cup F.
```

The word “connecting” matters: adjoining all ancestors of $`y`$ indiscriminately may add vertices without an ancestor in $`S`$ and needlessly break IAP.

1. **Finiteness.** Every member of $`F\setminus\{y\}`$ is an ancestor of $`y`$.

2. **New vertices have no descendants in the old cluster.** Every $`z\in F\setminus S`$ has an ancestor in $`S`$. If it also had a descendant in $`S`$, convexity of $`S`$ would force $`z\in S`$.

3. **Connectivity.** For each new vertex, choose a directed path from an ancestor in $`S`$ to that vertex. Its intermediate vertices belong to $`S\cup F`$. Every addition is therefore connected to $`S`$ inside $`T`$.

4. **Convexity.** Consider $`a\prec b\prec c`$ with $`a,c\in T`$. If $`c\in S`$, then $`a`$ cannot be new by step 2, so old convexity gives $`b\in S`$. Otherwise $`c`$ is new and is at or below $`y`$. The point $`a`$ either belongs to $`S`$ or has an ancestor there. Thus $`b`$ has an ancestor in $`S`$ and is an ancestor of $`y`$, so $`b\in F`$.

5. **IAP.** For each old vertex, whichever side of its descendant partition was finite remains finite after a finite addition. For each new vertex, step 2 puts all its descendants in $`T`$ inside the finite set $`F`$.

Since $`y\in T\setminus S`$, the enlargement is proper. This proves the lemma.

**Corollary.** Every unrestricted maximal specieslike cluster is descendant-closed:

```math
\forall x\in S\ \forall y\in V,\qquad
x\prec y\Longrightarrow y\in S.
```

This proof uses neither finite outdegree, countability, a finite root set, nor an infinite ambient graph. Finite past suffices. In the biosphere model, the ancestor set of $`y`$ lies in the finite birthdate sublevel below $`t(y)`$.

## Independent proof B: a broader well-founded formulation

Finite past can be weakened further. Suppose the strict ancestry relation is well-founded: every nonempty vertex set has a member with no ancestor in that set. No claim of a globally weakest possible assumption is intended.

Assume an unrestricted maximal specieslike cluster $`S`$ omits a descendant. Set

```math
A=\{y\in V\setminus S:\exists s\in S,\ s\prec y\}.
```

Choose an ancestry-minimal $`y\in A`$. Then $`T=S\cup\{y\}`$ is a specieslike cluster:

- On a path from $`S`$ to $`y`$, every vertex before $`y`$ lies in $`S`$ by minimality. Thus $`y`$ has a parent in $`S`$, establishing connectivity.
- A point between an old member and $`y`$ belongs to $`S`$ by minimality. The reverse endpoint case cannot arise: any descendant of $`y`$ in $`S`$ would put $`y`$ in $`S`$ by old convexity. Old endpoint pairs are handled by old convexity.
- IAP for old vertices survives the singleton addition. The new vertex has no descendants in $`S`$ and no self-descendant, so its descendant side in $`T`$ is empty.

This contradicts maximality. Thus well-founded ancestry already implies the corollary. A strict natural-number birth ranking supplies this hypothesis immediately, as does the finite-past assumption of proof A.

This is a useful Lean simplification: in a natural-number presentation, choose the least omitted descendant, then enlarge by one vertex. It avoids constructing the full finite convex hull.

**Stable extra assumption.** If the original cluster has a common ancestor inside itself, either enlargement retains that same common ancestor: every new vertex is descended from an old member. Consequently the descendant-closure conclusion also holds for maxima restricted only by the common ancestor property. Reflection is the obstruction in the counterexample below. More generally, one may add any constraint proved preserved by the particular enlargement; this preservation must be an explicit hypothesis, not inferred merely from the word “maximal.”

## Why the constrained theorem is false

The following fully specified graph is a specialization of the splitting configuration in Example 14(2), cited above. The verification here is explicit.

Let

```math
V=\{r\}\cup\{a_n:n\in\mathbb N\}\cup\{b_n:n\in\mathbb N\}
```

with only these edges:

```math
r\to a_0,\qquad r\to b_0,\qquad
a_n\to a_{n+1},\qquad b_n\to b_{n+1}.
```

Use birth ranks $`t(r)=0`$, $`t(a_n)=2n+1`$, and $`t(b_n)=2n+2`$. Every finite birth sublevel is finite, every vertex has at most two children, and the graph is infinite.

Take $`S=\{r\}\cup\{a_n:n\in\mathbb N\}`$. It is connected and convex. For each member, all but finitely many members of $`S`$ are descendants. The root is a common ancestor, and every member with infinitely many ambient descendants has infinitely many descendants inside $`S`$.

Suppose a constrained competitor $`T\supsetneq S`$ exists. It contains some $`b_j`$. Reflection then forces infinitely many descendants of $`b_j`$ into $`T`$. But $`a_0\in T`$ has infinitely many descendants along the $`a`$ ray and infinitely many non-descendants along the added $`b`$ ray. This violates IAP. Hence $`S`$ is constrained-maximal.

Nevertheless $`r\in S`$ and its child $`b_0\notin S`$. So $`S`$ is not descendant-closed.

The unrestricted enlargement proof fails under reflection for a concrete reason: adding only finitely much of the other ray introduces a vertex whose ambient descendants are infinite but whose descendants in the enlarged cluster remain finite.

## Why “maximal proper subset” is also different

Take an infinite ray $`r\to a_0\to a_1\to\cdots`$ and add a terminal child $`z`$ of $`r`$. Let $`S=V\setminus\{z\}`$.

Both $`S`$ and $`V`$ are specieslike clusters. The set $`S`$ is maximal among clusters required to be proper subsets of $`V`$, since its only strict superset is $`V`$. Yet it omits the descendant $`z`$ of its member $`r`$. Therefore the unrestricted theorem must allow $`V`$ as a competing cluster.

## Interpretation and integration guidance

- The safe theorem label is “unrestricted maximal specieslike clusters are descendant-closed under well-founded ancestry.”
- The lemma is a conditional structural result. It does not establish existence of unrestricted maxima. The two-ray graph above in fact has no unrestricted maximal specieslike cluster containing $`r`$: any finite branch truncation can be enlarged, while both complete rays violate IAP.
- Descendant closure automatically gives reflection. It does not give the common ancestor property. These facts do not turn the lemma into an alternative proof of the constrained existence theorem.
- The relation to the source is close: the unrestricted theorem generalizes the enlargement reasoning in Remark 3, footnote 5. Presenting it as something Alexander's framework misses, or as a refutation of his main theorem, would be incorrect.
- The formal implementation should expose the quantification over **all specieslike supersets**. A generic maximality predicate parameterized by a family needs the family instantiated explicitly.
- Keep this source audit distinct from the Lean build receipt. The implementation owner must verify the actual statement, assumptions, compilation, and axiom output before calling a formal endpoint certified.

## Retrieval record and limits

Inspected on 2026-09-25: versioned arXiv HTML and PDF, including definitions, Remark 3, the maximality and genericity arguments in Sections 5–6, and Examples 14–15. PDF text locations were checked against printed page numbering. Direct retrieval used the known identifier `2602.05274v1`; in-document searches included `Definition 1.`, `Definition 2.`, `Definition 3.`, `Definition 4.`, `Remark 3.`, `Definition 11.`, `Example 14.`, and `descendant`.

This was a bounded audit of the proposed theorem against the named primary paper. It was not a survey of all graph-convexity or order-theory literature. The older infinitary-species paper was not needed to distinguish the two maximality notions here. No claim is made that the handwritten generalization has never appeared elsewhere.

Formatting check: all 97 mathematical expressions in this note compiled through local MathJax 3.2.2 with zero errors. Inline mathematics uses protected GitHub dollar-backtick delimiters; displays use fenced `math` blocks. This is a local syntax check, not a claim that this unpublished note has already been visually checked on GitHub.
