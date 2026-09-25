---
title: "Recurrent parenthood and finite/cofinite ancestry"
subtitle: "A conditional bridge to specieslike clusters, with a cultural-persistence counterexample"
date: "25 September 2026"
---

**Research draft.** Complete written arguments are given below. Formal verification status is recorded separately in the claim ledger and build receipt; an unverified extension must not inherit the status of a checked lemma. Originality and empirical applicability have not been established. This draft is intended for mathematical review, not as an accepted publication.

## Abstract

We study a discrete-generation pedigree partitioned into finitely many reproductive communities. Under finite generation prefixes, persistent occupancy, same-community parent coverage and finite-window dissemination of every lineage, we characterize Alexander's identical ancestor point axiom using the strongly connected components of the graph of recurring cross-community parenthood. An infinite organism set satisfies the axiom exactly when all but finitely many of its members occupy one such component. Sufficiently late component tails are connected, ancestrally convex and reflecting. A standard conditional Borel–Cantelli corollary permits history-dependent reproductive feedback, subject to the same strong structural assumptions. A separate elementary model illustrates why stable cultural differences do not by themselves force neutral genetic separation. The contribution investigated is the precise conditional connection between reproductive dynamics and the ancestry predicate, rather than a universal definition or empirical theory of speciation.

## 1. Question and prior work

DNA sequences, regulatory states and learned behaviour may influence reproduction. A genealogy records the resulting parenthood relationships. To connect a mechanistic model to a specieslike-cluster framework, one must prove something about that genealogy rather than identify phenotypic difference with species membership.

Alexander's IAP axiom requires each member of a set to have either finitely many descendants or finitely many non-descendants within that set. Connectivity and ancestry convexity are additional requirements for a specieslike cluster [1]. We ask which recurring reproductive contacts enforce this axiom under a declared local mixing hypothesis.

The motivating question is newly posed here as an application question. We do not attribute an unsolved conjecture with this exact formulation to Alexander. Structured random-pedigree work already shows that rare migration can connect ancestry [2,3]. In temporal-network theory, recurring edges support time-respecting reachability when information can be retained while waiting [4]. Those mechanisms are prior art. Our candidate contribution is the subset classification below and its faithful formal interface. A full novelty determination remains to be made.

The theorem excludes local lineage extinction. It therefore does not subsume the more realistic extinction-or-spread alternatives in random-pedigree models. It also does not derive biological species labels from DNA or identify the maximal clusters in Alexander's general framework.

## 2. Model and definitions

Let $`D`$ be a nonempty finite set of demes, meaning assigned reproductive communities. Demes are not assumed species. Let $`V`$ be the set of organisms, with generation $`g:V\to\mathbb N`$, deme map $`d:V\to D`$, and parenthood relation $`E`$. Strict ancestry $`u\prec v`$ means a nonempty directed $`E`$-path from $`u`$ to $`v`$.

Assume:

1. **Finite past.** For every $`n`$, the set $`\{v:g(v)<n\}`$ is finite.
2. **Continued occupancy.** Every cohort $`V_{n,a}=\{v:g(v)=n,\ d(v)=a\}`$ is nonempty.
3. **Generation step.** If $`E(u,v)`$, then $`g(v)=g(u)+1`$.
4. **Local parent coverage.** Every organism of positive generation has a parent in its own deme.
5. **Local dissemination.** There is $`L\geq1`$ such that every $`u\in V_{n,a}`$ is an ancestor of every member of $`V_{n+L,a}`$ through a path entirely in deme $`a`$.

The cohorts are finite. Every organism has finitely many children, and only generation-zero organisms can be parentless. These assumptions thus supply the elementary finiteness conditions of the pedigree model.

Assumption 5 is particularly restrictive. It ensures every organism's lineage persists and spreads locally. It rules out childlessness and local lineage extinction. It is stated as a condition on actual finite pedigree windows, not assumed IAP, but satisfying a finite list of observed windows cannot establish that it holds forever.

The restriction is severe even in a simple random model. In a fixed deme of N>=2 organisms, if each of N children independently selects two parents uniformly, a specified parent has probability r=(1-1/N)^(2N)>0 of having no child. Applying this to one specified organism in each generation with fresh independent draws gives probability (1-r)^k that all k selected organisms avoid childlessness. This tends to zero. Hence universal all-time dissemination has probability zero in that model. The stochastic corollary below cannot be presented as a direct application to ordinary Wright-Fisher reproduction.

For distinct $`a,b\in D`$, define the recurrent-parenthood relation
```math
R(a,b)\quad\Longleftrightarrow\quad
\forall t\ \exists u,v:\quad
g(u)\geq t,\ d(u)=a,\ E(u,v),\ d(v)=b.
```
Let $`R^*`$ denote reflexive transitive reachability. Demes belong to the same strongly connected component when each is $`R^*`$-reachable from the other.

For $`S\subseteq V`$, write $`\operatorname{IAP}(S)`$ when every $`v\in S`$ satisfies
```math
\bigl|\{w\in S:v\prec w\}\bigr|<\infty
\quad\text{or}\quad
\bigl|\{w\in S:v\not\prec w\}\bigr|<\infty.
```
This is Alexander's strict-ancestry convention. An organism is not automatically its own strict descendant.

## 3. Eventual ancestry and the classification theorem

**Theorem 1.** Under assumptions 1–5, the following hold.

(a) There is a generation $`T`$ such that for every $`v`$ born at or after $`T`$, there is $`N(v)`$ with
```math
g(w)\geq N(v)\quad\Longrightarrow\quad
\left(v\prec w\ \Longleftrightarrow\ R^*(d(v),d(w))\right).
```

(b) For every infinite $`S\subseteq V`$,
```math
\operatorname{IAP}(S)
\quad\Longleftrightarrow\quad
\exists C\text{ an }R\text{-component}:
\left|\{v\in S:d(v)\notin C\}\right|<\infty.
```
The component in (b) is unique.

(c) The entire pedigree satisfies IAP if and only if $`R`$ is strongly connected.

(d) For each component $`C`$, the tail
```math
S_C=\{v:g(v)\geq T,\ d(v)\in C\}
```
is infinite, connected in the underlying undirected induced pedigree, ancestrally convex, IAP and reflecting. Every member has infinitely many descendants in $`S_C`$. No maximality claim is made.

### Proof

**Persistence of local dissemination.** Fix $`u\in V_{n,a}`$. Assumption 5 gives ancestry to all of $`V_{n+L,a}`$. If $`u`$ is an ancestor of an entire later $`a`$-cohort, every member of the next cohort has a same-deme parent in it by assumptions 3 and 4. Appending that parenthood edge extends ancestry. Induction shows that $`u`$ is an ancestor of every member of every $`a`$-cohort from $`n+L`$ onward. Say that $`u`$ saturates $`a`$.

**Propagation through recurrent links.** Suppose $`u`$ saturates $`a`$ after time $`h`$ and $`R(a,b)`$. Choose an actual edge $`x\to y`$ of type $`a\to b`$ with $`g(x)\geq h`$. Then $`u\prec x\prec y`$. Local dissemination from $`y`$ implies that $`u`$ eventually saturates $`b`$. Repeating this argument along a finite $`R`$-path proves eventual saturation of any reachable deme. Since there are finitely many demes, there is one time beyond which all reachable demes are saturated. The proof can wait for links in the required order because saturated ancestry persists.

**Removal of transient edge types.** For each distinct ordered pair for which $`R(a,b)`$ fails, there is a time after which no edge of that type occurs. Take the maximum of these finitely many cutoffs, or zero when there are none, and call it $`T`$. An ancestry path starting at or after $`T`$ then projects to an $`R^*`$-path: each edge either remains in its deme or follows $`R`$. Combining this with eventual saturation proves (a).

**Sufficiency in (b).** Suppose $`S`$ has only finitely many members outside a component $`C`$. Fix $`v\in S`$, possibly born before $`T`$ or outside $`C`$. If $`v`$ has no strict descendant in the tail of $`C`$, its descendants in $`S`$ are confined to the finite outside-$`C`$ exception and the finite pre-$`T`$ prefix. Otherwise choose a strict descendant $`z`$ in the tail. From $`z`$, recurring reachability and local dissemination saturate every deme of $`C`$. Consequently $`v`$ has only finitely many non-descendants in $`S`$. This proves the required alternative, including early exceptional vertices.

**Necessity in (b).** Partition $`S`$ by its finitely many components. If no one component contains $`S`$ modulo a finite set, two distinct components $`C,C'`$ have infinite intersections with $`S`$. They cannot reach each other in both directions; relabel them so that $`C`$ cannot reach $`C'`$. Choose $`v\in S`$ in $`C`$ after $`T`$, possible because the past is finite. It eventually reaches every organism of $`C`$, so has infinitely many descendants in $`S\cap d^{-1}(C)`$. It reaches no organism of $`C'`$, so has infinitely many non-descendants in $`S\cap d^{-1}(C')`$. This contradicts IAP. Uniqueness follows because distinct components are disjoint and an infinite set cannot be contained modulo finite in both.

**Parts (c) and (d).** Continued occupancy gives infinitely many organisms in each component. Thus (b), applied to $`V`$, gives (c). If $`R`$ is strongly connected, the saturation argument actually gives cofinite descendants for every organism, including those before $`T`$.

For a component tail, saturation proves cofinite descendants, IAP and reflection. If $`u,w`$ lie in the tail and $`u\prec v\prec w`$, generation increases and the projected component path cannot leave $`C`$ and return to $`C`$ without placing the intermediate deme in that same component. Hence $`v`$ lies in the tail, proving convexity. For connectivity, two organisms in the tail have a sufficiently late common descendant in it. Convexity keeps both directed paths inside the tail; reversing one gives an undirected path between the organisms. Continued occupancy proves infinitude. This completes the proof.

## 4. A stochastic interpretation with feedback

This section is a written corollary using a standard probability theorem. It must not be described as Lean checked unless the probability adapter has a separate receipt.

Let $`\mathcal F_n`$ contain the history before reproduction from generation $`n`$ to $`n+1`$. Let $`A_n(a,b)`$ be the event that at least one actual parenthood edge of type $`a\to b`$ occurs, and set
```math
q_n(a,b)=\Pr(A_n(a,b)\mid\mathcal F_n).
```
The $`q_n`$ may depend on inherited traits, regulatory states, learned preferences and prior history. No independence of reproductive events is assumed. Assume the structural conditions of Theorem 1 hold almost surely.

**Corollary 2.** Almost surely, Theorem 1 holds with the graph
```math
Q(a,b)\quad\Longleftrightarrow\quad
a\neq b\ \text{ and }\ \sum_n q_n(a,b)=\infty
```
in place of $`R`$.

**Proof.** The conditional Borel–Cantelli theorem [5] identifies infinitely many occurrences of $`A_n(a,b)`$ with divergence of the corresponding conditional-probability sum, up to a null set. There are finitely many deme pairs. Outside the union of their null sets and the structural-model null set, $`Q=R`$ and the deterministic theorem applies. Its statement is then pathwise for every $`S`$; no uncountable intersection over $`S`$ is taken.

For two demes, divergence in both directions implies whole-population IAP under these assumptions. Divergence in only one direction need not. If all cross-deme sums are finite, only finitely many cross-deme events occur and sufficiently late deme tails separate.

A positive probability at every time is not enough: $`q_n=2^{-n-2}`$ is summable. A probability tending to zero need not be enough for separation: $`q_n=1/(n+2)`$ has a divergent sum. These are conditional probabilities of actual parenthood, not uncalibrated gene-frequency migration parameters.

## 5. Why the assumptions matter

**One-way reproduction.** Place one organism in each of two demes per generation. Include both vertical chains and every edge $`A_n\to B_{n+1}`$. Assumptions 1–5 hold with $`L=1`$. Every $`B_n`$ has infinitely many descendants in $`B`$ and infinitely many non-descendants in $`A`$, so global IAP fails. The underlying undirected graph is connected, but the recurrent graph has two components.

**Unmixed clans.** Place two persistent clans in each of two demes. Preserve each clan's vertical chain and allow reciprocal cross-deme edges only for clan zero. The recurrent deme graph is strongly connected. A clan-one individual nevertheless has infinitely many descendants only along its own chain and infinitely many non-descendants elsewhere. Assumption 5 fails. The contact graph cannot recover information that deme aggregation has discarded.

**Finite observation.** The recurring graph concerns arbitrarily late reproduction. A finite pedigree, genetic sample or observed mating frequency cannot establish the infinite-future premises without a model. This theorem is a model implication, not a finite-data species classifier.

## 6. Cultural persistence with neutral mixing

The following model is a separate boundary example, not an instantiation of the finite-pedigree assumptions above. It contains cultural frequency dynamics and neutral genetic exchange; it does not contain an epigenetic state or a complete reciprocal gene–culture feedback loop.

Let
```math
F(p)=3p^2-2p^3
```
be the probability that a majority of three independent cultural models have a trait when its frequency is $`p`$. Define
```math
x'=(1-m)F(x)+mF(y),\qquad
y'=mF(x)+(1-m)F(y).
```
The unit square is invariant. On $`y=1-x`$, put $`d=2x-1`$; then
```math
d'=(1-2m)(3d-d^3)/2.
```
A polarized fixed point has
```math
d^2=\frac{1-6m}{1-2m},\qquad x=(1+d)/2,\qquad y=(1-d)/2.
```

At such a point the two Jacobian eigenvalues are
```math
6m,\qquad \frac{6m}{1-2m}.
```
Thus $`0<m<1/8`$ gives strict contraction in both linearized modes; $`m<1/6`$ alone is insufficient for full two-dimensional stability. A direct local estimate supplies more than a linearized calculation. At either equilibrium coordinate $`p`$, let $`A=6p(1-p)=6m/(1-2m)`$. For $`|e|\leq r\leq1`$,
```math
F(p+e)-F(p)=Ae+(3-6p)e^2-2e^3,
\qquad |F(p+e)-F(p)|\leq(A+5r)|e|.
```
Here $`p\in[0,1]`$ gives $`|3-6p|\leq3`$. Choose $`r=(1-A)/10`$ and $`q=(1+A)/2<1`$. Nonnegative mixing weights sum to one, so the supremum-norm distance to the polarized equilibrium contracts by at most $`q`$ throughout this radius. Induction keeps every iterate within the radius and bounds its distance by $`q^t`$ times the initial distance. Since $`q^t\to0`$, this proves local attraction and Lyapunov stability in the full two-dimensional neighbourhood.

For an exact rational example, take $`m=7/78`$, $`d=3/4`$, $`x=7/8`$ and $`y=1/8`$. The fixed point is polarized and $`A=21/32<1`$.

To make exchange depend on the actual cultural difference, choose $`0<g\leq1/2`$, $`k\geq0`$ and
```math
\rho_t=\frac{g}{1+k(x_t-y_t)^2},
\qquad
u_{t+1}=(1-\rho_t)u_t+\rho_t v_t,\qquad
v_{t+1}=(1-\rho_t)v_t+\rho_t u_t.
```
The unit-square invariance ensures
```math
0<a:=\frac{g}{1+k}\leq\rho_t\leq g\leq1/2.
```
Subtracting the two genetic recursions gives
```math
|u_t-v_t|
\leq(1-2a)^t |u_0-v_0|\longrightarrow0.
```
Thus cultural difference can suppress exchange while a positive residual exchange still homogenizes this neutral marker. At the rational polarized equilibrium, culture remains distinct forever.

The coupling is one-way from culture to exchange. It is not a reciprocal gene–culture model and contains no epigenetic mechanism. Persistent cultural difference alone therefore does not imply zero exchange or separation of neutral allele frequencies. Whether a particular species concept permits gene flow is a further definitional question; this example does not classify real species.

## 7. Remaining questions with identifiable sources

The current result addresses the last part of the user's proposed chain: a specified reproduction process to an ancestry property. Three further questions would make that connection less restrictive.

1. **Allow local lineage extinction.** Derive a replacement for local dissemination from a stated random reproduction rule, tracking successful lineage transmission rather than raw crossing counts. Compare with Chang and Rohde–Olson–Chang rather than presenting extinction-or-spread as a new general idea.
2. **Finite-population epigenetic barriers.** Planidin et al. propose studying finite populations [6]. Specify their finite life cycle and a neutral migrant-marker outcome before asking whether population size amplifies the barrier. A proof must compare matched models and cannot interchange fixation probability with finite-horizon transmission.
3. **Nonvertical cultural learning.** Fogarty et al. leave the effect dependent on the transmission scheme [7]. Specify who learns from whom and at what life-cycle stage, then characterize its equilibria or association. This is a source-proposed direction, not a precise pre-existing conjecture already solved here.

The companion FOGARTY-GLOBAL-RATE.md proves a full-range equilibrium refinement and quantitative cultural fixation in Fogarty et al.'s affinity-bias model, permitting arbitrary admissible changes in the affinity parameters between generations. It is kept separate because it uses the published phenogenotype recursions rather than the pedigree model of Theorem 1. Both the recurrence-based convergence and an actual recursively defined evolution are Lean checked.

## 8. Reproducibility and status

The formal package uses Lean 4.33.1 and Mathlib commit 0df444a360eaa60ab8c11dca51a86af692955474. Its declaration mapping, build commands and precise verification coverage are in CLAIM-LEDGER.md and the verification receipt. Do not infer that every paragraph in this manuscript is formalized from a successful module build.

This research note and its proofs were developed with AI assistance, including parallel proof drafting and internal adversarial review. No independent external mathematical review or biological validation has yet been obtained. The intended next recipient is a reviewer who can assess statement faithfulness, interest and prior art. A proof assistant's acceptance establishes the encoded implication, not those other claims.

## References

1. Samuel Allen Alexander. *Specieslike clusters based on identical ancestor points*. 2026. [arXiv:2602.05274v1](https://arxiv.org/html/2602.05274v1); [journal DOI](https://doi.org/10.1007/s00285-026-02361-x).
2. Joseph T. Chang. *Recent common ancestors of all present-day individuals*. Advances in Applied Probability 31, 1002–1026 (1999). [DOI](https://doi.org/10.1239/aap/1029955256).
3. Douglas L. T. Rohde, Steve Olson and Joseph T. Chang. *Modelling the recent common ancestry of all living humans*. Nature 431, 562–566 (2004). [DOI](https://doi.org/10.1038/nature02842).
4. Arnaud Casteigts, Paola Flocchini, Walter Quattrociocchi and Nicola Santoro. *Time-Varying Graphs and Dynamic Networks*. [Author manuscript](https://arnaudcasteigts.net/files/CFQS11.pdf).
5. Conditional Borel–Cantelli theorem. [Berkeley STAT205A notes, Lemma 21.2](https://www.stat.berkeley.edu/~aldous/205A/sinho_chewi_notes.pdf); [Mathlib declaration and source](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Martingale/BorelCantelli.html).
6. Planidin et al. *Adaptive epigenetic divergence can facilitate ecological speciation*. Proceedings of the Royal Society B 292, 20251217 (2025). [DOI](https://doi.org/10.1098/rspb.2025.1217).
7. Laurel Fogarty, Stephen Zhang and Marcus W. Feldman. *Gene-culture association and coevolution*. Theoretical Population Biology 165, 62–71 (2025). [DOI](https://doi.org/10.1016/j.tpb.2025.08.003).
