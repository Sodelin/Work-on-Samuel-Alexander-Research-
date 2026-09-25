# A bounded founding period as a replacement for common ancestry

Date: 2026-09-25. Status: new candidate theorem with a complete written proof; several supporting lemmas checked in Lean, but the full existence theorem has not been formalized or independently reviewed. This is a bounded response to the paper's stated open direction, not a claim of literature priority or a completed biological species definition.

## Source target and scope

Samuel Allen Alexander, *Specieslike clusters based on identical ancestor points*, [arXiv:2602.05274v1, Section 6](https://arxiv.org/html/2602.05274v1#S6), states after Theorem 13: “We would be particularly interested in a solution not requiring the CA property.” Informal Question 4 asks for biologically plausible extra constraints under which every organism belongs to a maximal specieslike cluster satisfying those constraints. Theorem 13 supplies common ancestry (CA) and reflection (REF). Example 15 already disproves plain deletion of CA; Proposition 11(b) supplies the corresponding failure of increasing-union closure.

The theorem below replaces CA with a bounded founding period. Maximality is **within the class satisfying the replacement constraint and REF**. It does not assert unrestricted maximality among all specieslike sets. The latter assertion is false in general by the paper's two-ray example.

## Definitions

Let $`G`$ be an infinite biosphere in the paper's sense: births are real-valued; every parent is older than its child; every strict birthdate sublevel is finite; and every organism has finitely many children. Write $`x\prec_G y`$ for strict ancestry and $`D(x)`$ for the strict descendants of $`x`$.

For nonempty $`S\subseteq V(G)`$, define its founder set

```math
F(S)=\{r\in S:\nexists a\in S\text{ such that }a\prec_G r\}.
```

These are minimal members of $`S`$ in the ambient ancestry order. They need not be parentless in $`G`$. For convex $`S`$, they are exactly the vertices with no parent inside $`S`$: an ancestral path from a member of $`S`$ to a member of $`S`$ lies inside $`S`$ by convexity.

Let $`m(S)`$ be the earliest birthdate represented in $`S`$. Existence is proved below. Fix a real duration $`\Delta\ge0`$, the same for every candidate cluster. Say that $`S`$ satisfies $`W_\Delta`$ if

```math
t(r)\le m(S)+\Delta\qquad\text{for every }r\in F(S).
```

This says that all founders appear during a fixed initial period of the cluster. It allows multiple unrelated founders. It imposes no upper bound on cluster duration and no universal upper bound on founding population size.

Let $`\mathcal K_\Delta`$ be the nonempty sets that are connected, convex, satisfy IAP, satisfy REF, and satisfy $`W_\Delta`$.

## Candidate theorem

**For every $`\Delta\ge0`$, every member $`S`$ of $`\mathcal K_\Delta`$ is contained in an inclusion-maximal member of $`\mathcal K_\Delta`$. Consequently every organism in every infinite biosphere belongs to a maximal member of $`\mathcal K_\Delta`$.**

The consequence uses Alexander's Theorem 13 only to supply an initial cluster containing the organism. That cluster has CA and therefore $`W_\Delta`$. The new argument proves extension to maximality in the larger class, whose competitors may have several founders and fail CA.

In fact $`\mathcal K_\Delta`$ is closed under all nonempty directed unions, a slightly stronger closure statement than chain-union closure.

## Proof, including the compactness points

### Lemma 1: earliest births and founder coverage

Every nonempty $`S`$ has an earliest birthdate. Choose $`x\in S`$. The set

```math
\{y\in S:t(y)<t(x)+1\}
```

is finite and nonempty, so one of its members $`e`$ has minimum birthdate. Every member outside this finite set has birthdate at least $`t(x)+1>t(e)`$. Thus $`t(e)=m(S)`$.

Every $`x\in S`$ is either a founder or a strict descendant of a founder. To prove this, consider $`x`$ together with its ancestors that belong to $`S`$. This set is finite and nonempty, because all ancestors are born before $`t(x)`$. Choose a member $`r`$ of minimum birthdate. If a member $`a`$ of $`S`$ were an ancestor of $`r`$, transitivity would put $`a`$ in the same finite set, contradicting minimality of $`t(r)`$. Thus $`r`$ is a founder and $`r=x\text{ or }r\prec_G x`$.

No convexity assumption is needed for this coverage claim. Convexity is needed later when turning ambient ancestral paths into paths inside $`S`$.

If $`W_\Delta`$ holds, $`F(S)`$ is finite: it is contained in the finite ambient sublevel $`t<m(S)+\Delta+1`$.

### Lemma 2: the founding period survives a directed union

Let $`(S_i)`$ be a nonempty family directed by inclusion, and suppose every $`S_i`$ satisfies $`W_\Delta`$. Write $`U=\bigcup_i S_i`$. Choose $`e\in U`$ with $`t(e)=m(U)`$; Lemma 1 permits this choice.

Take any $`r\in F(U)`$. Choose stages containing $`e`$ and $`r`$, and use directedness to choose a common stage $`S_k`$ containing both. A founder of $`U`$ is a founder in every subset of $`U`$ that contains it: an ancestor in that subset would also be an ancestor in $`U`$. Hence $`r\in F(S_k)`$.

Because $`S_k`$ contains $`e`$ and is contained in $`U`$, $`m(S_k)=m(U)`$. Applying $`W_\Delta`$ at stage $`k`$ gives

```math
t(r)\le m(S_k)+\Delta=m(U)+\Delta.
```

Thus $`U`$ satisfies $`W_\Delta`$ and has finitely many founders. In particular the earliest birth need not be obtained from a limit of birthdates: it is represented by an actual organism, and any stage containing that organism has the final earliest birthdate.

### Lemma 3: an infinite nondescendant region contains a ray

Suppose $`U`$ is convex and $`F(U)`$ is finite. If $`U`$ contains infinitely many nondescendants of $`v`$, then there is an infinite directed path

```math
r=w_0\longrightarrow w_1\longrightarrow w_2\longrightarrow\cdots
```

inside $`U`$, consisting of nondescendants of $`v`$, where $`r`$ is a founder of $`U`$.

By founder coverage, $`U`$ is covered by the finitely many sets $`\{r\}\cup D(r)`$, for $`r\in F(U)`$. Therefore some founder $`r`$ has infinitely many descendants in $`U`$ that are nondescendants of $`v`$.

For any $`a\in U`$ with infinitely many such descendants, every such descendant $`y`$ is reached through one of the finitely many children of $`a`$. Since $`a,y\in U`$ and $`U`$ is convex, the first child on any such path belongs to $`U`$. Finitely many children cannot each account for only finitely many such $`y`$, so one child has infinitely many descendants of the required kind. The child is itself a nondescendant of $`v`$, since otherwise all its descendants would descend from $`v`$.

Repeat this choice. Birthdates strictly increase along every edge, so the resulting vertices are distinct. The initial founder $`r`$ is also a nondescendant of $`v`$ for the same transitivity reason. Each $`w_n`$ has infinitely many ambient descendants, witnessed by the tail of the ray.

### Lemma 4: finite founders at the limit are enough for IAP closure

Let $`(S_i)`$ be a nonempty directed family, each member convex and satisfying IAP and REF. Suppose the union $`U`$ has finitely many founders. Then $`U`$ satisfies IAP.

First $`U`$ is convex: if $`a\prec_G b\prec_G c`$ and $`a,c\in U`$, directedness puts the endpoints in a common $`S_i`$; its convexity supplies $`b`$. Reflection also passes to $`U`$, since any vertex is already in a stage reflecting its infinitely many ambient descendants.

Suppose for contradiction that $`U`$ fails IAP. Then some $`v\in U`$ has infinitely many descendants and infinitely many nondescendants in $`U`$. Apply Lemma 3 to obtain a ray of nondescendants $`w_0,w_1,\ldots`$, with $`w_0`$ a founder of $`U`$.

Choose a stage $`A`$ containing both $`v`$ and $`w_0`$. The ray proves $`w_0`$ has infinitely many ambient descendants. REF for $`A`$ therefore implies that $`A`$ is infinite. REF for $`A`$ also ensures that $`v`$ has infinitely many descendants in $`A`$, since $`v`$ has infinitely many descendants in $`U`$ and hence in $`G`$.

We claim every $`w_n`$ belongs to $`A`$. The case $`n=0`$ is how $`A`$ was chosen. For $`n>0`$, choose a stage $`B`$ containing $`A`$ and $`w_n`$; directedness permits this. Since $`w_n`$ has infinitely many ambient descendants, REF for $`B`$ gives infinitely many descendants of $`w_n`$ in $`B`$. IAP for $`B`$ then forces $`B`$ to contain only finitely many nondescendants of $`w_n`$.

The infinite subset $`A`$ of $`B`$ must consequently contain some descendant $`z`$ of $`w_n`$. But $`w_0\in A`$ is an ancestor of $`w_n`$ and $`z\in A`$ is a descendant of $`w_n`$. Convexity of $`A`$ forces $`w_n\in A`$, proving the claim.

All the $`w_n`$ are distinct nondescendants of $`v`$ in $`A`$, while $`v`$ has infinitely many descendants in $`A`$. This violates IAP for $`A`$. The contradiction proves that $`U`$ has IAP.

This is the precise extension of the paper's argument: one does not need a single ancestor of the entire union; finitely many founders suffice to extract one nondescendant ray, and reflection plus convexity bring that ray back into one stage.

### Finish: maximality and coverage of every organism

For a directed family in $`\mathcal K_\Delta`$, Lemma 2 gives a finite founder set for the union. Lemma 4 gives IAP. Convexity and REF pass to the union as above. Connectivity also passes to a directed union: two vertices lie in a common stage, where an undirected connecting path already exists. The union is therefore in $`\mathcal K_\Delta`$.

Fix $`S\in\mathcal K_\Delta`$ and order all members of $`\mathcal K_\Delta`$ containing $`S`$ by inclusion. The poset is nonempty. Every nonempty chain has its union as an upper bound in the same poset; the empty chain has $`S`$ as an upper bound. Zorn's lemma produces a maximal member $`M`$. Any $`\mathcal K_\Delta`$ superset of $`M`$ also contains $`S`$, so maximality in this poset is maximality in $`\mathcal K_\Delta`$ itself.

Finally CA implies $`W_\Delta`$: if $`a`$ is the common ancestor, then $`a`$ is the unique ancestry-minimal member and has the earliest birthdate. Alexander's Theorem 13 supplies such a connected, convex IAP+REF cluster through each organism. Applying the extension result completes the proof.

## The constraint really permits failure of CA

Take two parentless organisms $`a`$ and $`b`$, both born at time 0. Give them a shared child $`c_0`$ at time 1, followed by the ray $`c_0\longrightarrow c_1\longrightarrow c_2\longrightarrow\cdots`$ with $`t(c_n)=n+1`$. The whole graph is connected and convex, every vertex has cofinite descendants, and REF holds. Its founder set is $`\{a,b\}`$, so $`W_0`$ holds, but CA fails.

The whole graph is maximal in $`\mathcal K_0`$ because it contains every vertex. Thus the new theorem is not just a relabeling of CA. For any $`\Delta>0`$, the founders may instead have distinct births 0 and $`\Delta/2`$, followed by the shared child after both births.

For each positive integer $`k`$, the same construction with $`k`$ coeval founders feeding a common future shows that a fixed founding period does not bound founding population size uniformly across biospheres. Conversely a fixed bound on founder number does not bound the time between their births. These are two different replacement constraints.

## A second corollary: a fixed finite founder count

For each fixed integer $`k\ge1`$, replace $`W_\Delta`$ by $`|F(S)|\le k`$. The resulting connected IAP+CONV+REF class has the same maximal-extension and every-organism existence theorem.

Indeed, if the union of a directed family had $`k+1`$ distinct founders, choose a common stage containing all of them. They are all still founders in that stage, contradicting its bound. Thus the union has at most $`k`$ founders and Lemma 4 applies. Initial clusters exist because CA supplies one founder. For $`k\ge2`$ the allowed class strictly contains examples failing CA.

## Sharp failure: finitely many founders without uniform control is insufficient

Use the paper's comb construction, with vertices $`v_n,w_n`$ for $`n\ge0`$ and edges

```math
v_n\longrightarrow v_{n+1},\qquad w_n\longrightarrow v_n.
```

Let $`t(w_n)=2n`$ and $`t(v_n)=2n+1`$. This is an infinite biosphere. Every vertex has infinitely many ambient descendants.

Consider any connected, convex IAP+REF cluster $`S`$ containing $`v_0`$. REF at $`v_0`$ forces infinitely many spine vertices into $`S`$. Convexity then forces the entire spine into $`S`$. IAP at $`v_0`$ forces $`S`$ to contain only finitely many $`w_n`$, because all $`w_n`$ are nondescendants of $`v_0`$. Thus $`S`$ consists of the full spine and a finite set of teeth $`w_n`$.

Choose an omitted $`w_j`$. Adding just $`w_j`$ preserves connectivity through its child $`v_j`$, convexity because all relevant spine vertices are already present, and REF because $`w_j`$ has infinitely many descendants on the spine. It preserves IAP: old vertices see only a finite addition; the new vertex's nondescendants comprise a finite spine prefix plus finitely many other teeth. The enlarged set still has finitely many founders.

Consequently no such $`S`$ is maximal even after imposing 'finitely many founders.' This proves actual nonexistence of constrained maxima through $`v_0`$, not merely failure of an increasing-union proof. Fixed temporal or cardinal bounds prevent this enlargement from continuing indefinitely inside their respective classes.

## Lean evidence and exact remaining work

The companion `FounderWindow.lean` imports the existing `SpeciesBridge` definitions and was checked with Lean 4.33.1 against the owner's already compiled base module, without modifying or rebuilding the owner checkout. It establishes:

- `founder_covers`: strict natural birth order makes every member a founder or a founder's descendant.
- `founder_restrict`: a founder of a larger set stays a founder in each smaller set containing it.
- `window_finite_founders`: a founding window gives finitely many founders.
- `commonAncestor_window`: CA implies every nonnegative natural founding window.
- `nonempty_has_minimum`: a nonempty subset of natural birth ranks has a least member.
- `window_directed_union`: the window property passes to every nonempty directed union.
- `directed_union_finite_founders`: the directed union has finitely many founders.

The successful compiler run returned exit code 0. Printed endpoint axioms were only `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` occurred. These are supporting lemmas, not a machine-checked existence proof. The formal model uses natural ranks and natural window widths. The written theorem above uses the paper's real birthdates, including the possibility of coeval founders.

The next substantial formal lemma is Lemma 4: IAP passes to a directed union of convex reflecting IAP sets provided the union has finitely many internal founders. Its proof needs a generalized finite-founder Koenig lemma, followed by the reflection/convexity capture argument. After that, Zorn and real-date transfer remain explicit gates.

Interpretation also remains open: whether a chosen founding duration is biologically plausible, and whether this parameterized broadening is 'qualitatively different' in the author's intended informal sense. The mathematical existence statement no longer assumes CA; the method deliberately extends the source's compactness proof. No targeted primary-source check establishes novelty beyond the inspected version of this paper.
