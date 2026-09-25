# A precise ordinal characterization, its collapse, and the necessary phase restriction

Research date: 25 September 2026. The written theorem below covers Alexander's
population class. Its formal coverage has now expanded; all the checked results
listed here have successful local receipts. This note records local completion
before publication. The exact-commit hosted result is recorded in
[PR #6 and its checks](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/pull/6/checks).

- `GenericOrdinalCertificate.lean` proves avoidance iff a decreasing ordinal
  certificate exists on reachable states for arbitrary vertex and label types,
  without any finite-branching hypothesis.
- `GenericCertificate.lean` proves avoidance iff a decreasing natural certificate
  exists for arbitrary vertex and label types under finite branching for each
  fixed label, with a pointwise least attained certificate.
- The actual matching-history well-foundedness equivalence, Mathlib root rank
  $`\omega`$, and concrete pruning stages $`\omega`$ and $`\omega+1`$ are checked
  for every existing `BinaryNatPopulation`.
- Schmidt rank/kernel, the realizing-population pruning fixed point, and the
  full source-model generality of the explicit ordinal calculation remain
  written-only. Generic certificate coverage does not automatically extend
  the separate binary history modules.

See [the ordinal completion receipt](COMPLETION-RECEIPT.md) and
[the generic natural-certificate theorem](GENERIC-CERTIFICATE.md), and
[the generic ordinal-certificate source](GenericOrdinalCertificate.lean). No
priority claim is made.

## What Alexander actually asks

[Alexander, arXiv:1212.0186v2, Section 6, p. 9](https://arxiv.org/pdf/1212.0186v2)
asks for a characterization of the populations realizing a fixed, possibly
avoidable sequence, with particular interest in ordinal numbers analogous to
Schmidt's rayless-graph characterization. Section 6 supplies no ordinal rank
definition, no conjectured spectrum of countable ordinals, and no requirement
that the characterization assign different ranks to different avoiders.

The generic ordinal-certificate result gives a checked characterization with
weaker assumptions than the paper's population axioms. The ordinary
prefix-tree calculation has a written proof at the source's full generality
and a Lean proof for the existing binary natural-date model. That invariant
collapses completely. These answer precise interpretations of the question,
while leaving a richer structural classification of avoiders open.

## Definitions

Let $`P`$ be an Alexander population with finite alphabet $`A`$, and fix
$`s:\mathbb N\to A`$. Indices are zero-based and path length counts edges.
Write $`u\xrightarrow{a}v`$ for a directed edge of label $`a`$.

Let $`T(P,s)`$ consist of the empty history $`\varnothing`$ and all nonempty
finite vertex lists $`(v_0,\ldots,v_m)`$ such that
$`v_i\xrightarrow{s(i)}v_{i+1}`$ whenever $`i<m`$. The parent of a history
deletes its last vertex. Thus the empty history has one child $`(v)`$ for
every vertex $`v`$ of $`P`$. Every other node has finitely many children, by A2.

For each $`v`$, let $`T_v`$ denote the subtree rooted at $`(v)`$. For a
well-founded tree, use the rank convention

```math
\rho(t)=\sup\{\rho(t')+1:t'\text{ is a child of }t\},
\qquad \sup\varnothing=0.
```

For the transfinite leaf-pruning derivative, set $`D^0=T`$ and define

```math
\begin{aligned}
D^{\alpha+1}
  &=\{t\in D^\alpha:t\text{ has a child in }D^\alpha\},\\
D^\lambda
  &=\bigcap_{\alpha<\lambda}D^\alpha
    &&\text{for limit ordinals }\lambda.
\end{aligned}
```

These are definitions proposed in this note, not definitions from Alexander.

## Theorem 1: exact ordinal dichotomy

**Verification scope:** the proof below is written at the full source
generality. The actual history-tree equivalence, root rank, and displayed
first-limit pruning calculations are now Lean checked for
`BinaryNatPopulation`. The Schmidt-rank/kernel assertion and the realizing
fixed-point assertion remain written-only.

For every population $`P`$ satisfying Alexander's axioms and every target
$`s`$, the following are equivalent:

1. $`P`$ avoids $`s`$.
2. Every $`T_v`$ is finite.
3. $`T(P,s)`$ is well founded.
4. Its root rank is defined and is exactly $`\omega`$.
5. $`D^\omega=\{\varnothing\}`$ and $`D^{\omega+1}=\varnothing`$.
6. The underlying undirected tree $`T(P,s)`$ has Schmidt rank exactly $`1`$.

If $`P`$ realizes $`s`$, the nodes of a matching ray survive every pruning
stage. More precisely, $`D^\omega`$ is nonempty and is already a fixed point
of the pruning derivative.

### Proof

An infinite branch of $`T_v`$ is exactly an $`s`$-realizing path beginning
at $`v`$. Each $`T_v`$ is finitely branching. By König's lemma, $`T_v`$ has
no infinite branch if and only if it is finite. The same correspondence,
including the choice of first vertex immediately after the empty history,
proves $`1\Longleftrightarrow2\Longleftrightarrow3`$.

It remains essential to show that the global rank is exactly $`\omega`$,
rather than merely at most $`\omega`$. Every finite word occurs in $`P`$.
Here is the full argument, which uses the population axioms beyond finite
branching.

Let $`V_j`$ be the set reached from a root in at most $`j`$ edges. It is
finite by A1 and A2. For a word $`a_0,\ldots,a_{m-1}`$, choose a terminal
vertex $`w\notin V_{m-1}`$, possible because $`P`$ is infinite. Working
backwards, choose parents with labels $`a_{m-1},\ldots,a_0`$. Each required
parent exists by the incoming-label axiom: if the process encountered a root
before $`m`$ choices, it would give a root-to-$`w`$ path of length at most
$`m-1`$. This contradicts the choice of $`w`$. Reversing the choices gives
the required word. For $`m=0`$ there is nothing to prove. A3 ensures roots
and the reverse ancestry interpretation are valid.

In particular, the lengths of finite $`s`$-matches across all start vertices
are unbounded. Under avoidance, let $`h(v)`$ be the largest length of an
$`s`$-match from $`v`$. The finite tree $`T_v`$ has rank $`h(v)`$. Thus

```math
\rho(\varnothing)=\sup_{v\in V(P)}\bigl(h(v)+1\bigr)=\omega.
```

This proves $`3\Longrightarrow4`$, and $`4\Longrightarrow3`$ is part of the
rank's definition.

Every nonempty history has a finite subtree under avoidance, so disappears
after finitely many leaf deletions. The empty history survives every finite
stage, because $`h(v)`$ is unbounded. It is consequently the sole survivor
at $`\omega`$, and disappears at $`\omega+1`$. Conversely, an $`s`$-ray is
never deleted. This proves the equivalence with statement 5.

For the assertion about realizing populations, every nonempty node remaining
at $`\omega`$ has arbitrarily long extensions and hence an infinite extension
by finite branching. It therefore has a child which also remains at
$`\omega`$. Since at least one $`T_v`$ contains a ray, the empty history
also has such a child. Hence $`D^\omega`$ is a fixed point. For an avoider,
only the countably branching artificial root survives at $`\omega`$.

Schmidt rank $`0`$ means a finite graph; rank $`\alpha>0`$ means the least
such $`\alpha`$ for which deleting some finite vertex set leaves only
components of smaller rank. This is Definition 2 in
[Bonato, Bruhn, Diestel and Sprüssel, *Twins of rayless graphs*, p. 3](https://www.uni-ulm.de/fileadmin/website_uni_ulm/mawi.inst.081/Henning/raylesstwins.pdf).
Under avoidance, deleting the empty history leaves the finite components
$`T_v`$. The entire tree is infinite, so its Schmidt rank is exactly $`1`$.
Conversely, a graph assigned Schmidt rank is rayless, which rules out an
$`s`$-realization. This proves statement 6. Indeed its Schmidt kernel is
exactly $`\{\varnothing\}`$: a finite set which does not remove the empty
history leaves infinitely many singleton children in its connected component,
so cannot leave only finite components. $`\square`$

### What this settles and what it does not

There is no spectrum of larger countable ranks for this prefix-tree invariant
within Alexander's population class. Every avoiding population has ordinary
tree rank $`\omega`$ and Schmidt rank $`1`$. A spectrum claim involving
$`\omega+1`$ or larger root ranks must change either the tree construction or
the hypotheses. The ordinal $`\omega+1`$ above is an extinction stage, not a
root rank.

This is a complete membership characterization for a fixed $`s`$. It does
not give a structural hierarchy separating different avoiding populations:
all such populations have the same two ranks. Its canonical Schmidt kernel
is an artificial root, not a meaningful genealogical separator in $`P`$.

## Theorem 2: a certificate on reachable vertex-and-phase states

Define $`R_s`$ to be the pairs $`(v,k)`$ such that some matching history of
length $`k`$ ends at $`v`$. In particular, $`(v,0)`$ is reachable for every
$`v`$. Put an edge

```math
(v,k)\longrightarrow(w,k+1)
\quad\Longleftrightarrow\quad
v\xrightarrow{s(k)}w.
```

Under the population's finite-child assumption, restrict this phase graph
to $`R_s`$. The following are equivalent:

1. $`P`$ avoids $`s`$.
2. There is $`r:R_s\to\mathbb N`$ strictly decreasing on every phase edge.
3. There is $`r:R_s\to\operatorname{Ord}`$ strictly decreasing on every phase edge.

Write $`s^{(k)}(i)=s(k+i)`$ for the tail beginning at phase $`k`$. Under
avoidance, the pointwise least such natural certificate is

```math
r(v,k)=\max\{m\in\mathbb N:
  \text{an }s^{(k)}\text{-matching path of }m\text{ edges starts at }v\}.
```

It satisfies the exact recursion

```math
r(v,k)=\max\left(\{0\}\cup
  \{1+r(w,k+1):v\xrightarrow{s(k)}w\}\right),
```

and $`r(v,0)=h(v)`$. The phase-state description merges histories with the
same endpoint and phase without changing their ranks.

### Proof

Suppose $`P`$ avoids $`s`$ and $`(v,k)`$ is reachable. Fix a witnessing
prefix to $`v`$. An infinite continuation matching $`s^{(k)}`$ would
concatenate with that prefix to realize $`s`$. Hence no such continuation
exists. Its finitely branching tree is finite, so the displayed maximum
exists. Prefixing one edge to a child continuation proves the recursion and
strict decrease. Any other natural decreasing certificate bounds every
continuation length and therefore bounds this maximum; this proves pointwise
leastness. Natural numbers are ordinals, so statement 2 implies statement 3.
Any full realization gives an infinite descending ordinal sequence along its
reachable phase states, impossible. $`\square`$

For a natural certificate, the stronger finite bound is

```math
r(v_m,m)+m\le r(v_0,0)
```

for every $`s`$-matching prefix $`(v_0,\ldots,v_m)`$. This inequality and
exclusion of an infinite realization are checked in `OrdinalCertificates.lean`
without assuming finite branching. Finite branching is used for the converse
only.

The original `ReachableRankNecessity.lean` checks necessity, an attained
maximum, decrease, leastness, and equivalence using the repository's actual
`FinitePath` and `Realizes` for every `BinaryNatPopulation`.
`GenericCertificate.lean` now checks this natural-certificate result for
arbitrary vertex and label types with finitely many children for each fixed
vertex and label. No vertex enumeration or binary label encoding is used.

`GenericOrdinalCertificate.lean` separately proves the equivalence of
statements 1 and 3 for arbitrary vertex and label types **without finite
branching**. Its exact prefix-plus-tail representation identifies avoidance
with well-foundedness of reversed reachable-state transitions; Mathlib's
`Acc.rank` gives the forward certificate and ordinal well-foundedness gives
the converse. Finite branching is needed to guarantee natural-valued ranks,
not to obtain the generic ordinal certificate.

These proofs use classical choice and do not provide an executable evaluator
or a decision procedure from an arbitrary graph description. No continuation
bound, cofinality claim, or source-model adapter is assumed as an endpoint
premise. The generic result can use the source's existing vertex and label
types directly; the formalization still has to represent its edges faithfully.

## Counterexample: ranking every phase is wrong

Use the binary graph $`P_s`$ already defined in the classification manuscript
and formalized in `BinaryAvoidance.lean` at repository commit
`bcef6da64672310b314f2bc17c96f9535fcaaf5b`. Vertices are $`\mathbb N`$,
roots are $`0`$ and $`1`$, and destinations $`w\ge2`$ have the two incoming
edges $`w-1\to w`$ and $`w-2\to w`$. Let

```math
\operatorname{row}_s(2j)=s(j),
\qquad
\operatorname{row}_s(2j+1)=\neg s(j),
```

where $`\neg`$ denotes Boolean complementation. Label the $`+1`$ edge by
$`\operatorname{row}_s(w)`$ and the $`+2`$ edge by
$`\neg\operatorname{row}_s(w)`$.

For every binary $`s`$, the path

```math
1\longrightarrow3\longrightarrow5\longrightarrow7\longrightarrow\cdots
```

has edge labels $`s(1),s(2),s(3),\ldots`$, because the $`+2`$ edge to
$`2k+3`$ has label $`\neg\operatorname{row}_s(2k+3)=s(k+1)`$. Thus the
full phase graph $`V\times\mathbb N`$ has the infinite path

```math
(1,1)\longrightarrow(3,2)\longrightarrow(5,3)\longrightarrow\cdots.
```

For an aperiodic $`s`$, the already proved classification construction says
$`P_s`$ avoids $`s`$ itself. Every state on this displayed path is then
unreachable from phase zero: any reaching prefix would complete to an
$`s`$-realization. In particular, $`(1,1)`$ is unreachable because vertex
$`1`$ is a root.

Consequently a decreasing ordinal certificate on all of $`V\times\mathbb N`$
is too strong, even for these simplest bounded-degree avoiding populations.
The reachable restriction in Theorem 2 is mathematically necessary.
`odd_ray_realizes_tail` and `no_all_phase_natural_rank` are checked by Lean;
the impossibility for arbitrary ordinal ranks follows from the same infinite
descending-chain argument in the written proof.

## A descriptive consequence, without a completeness claim

Code a labelled graph on $`\mathbb N`$ by giving each vertex its complete
finite list of labelled children. Give the countable space of lists the
discrete topology and the graph-code space the product topology. For fixed
$`s`$, let $`C(v,m)`$ mean that an $`s`$-prefix of length $`m`$ can start
at $`v`$. A finite breadth-first traversal checks $`C(v,m)`$, reading only
finitely many lists; hence $`C(v,m)`$ is clopen.

Therefore, on the subspace of codes which satisfy the population axioms,

```math
\begin{aligned}
P\text{ realizes }s
  &\Longleftrightarrow \exists v\in\mathbb N\;\forall m\in\mathbb N\;C(v,m),\\
P\text{ avoids }s
  &\Longleftrightarrow \forall v\in\mathbb N\;\exists m\in\mathbb N\;\neg C(v,m).
\end{aligned}
```

Realization is consequently a $`\Sigma^0_2`$ set and avoidance a $`\Pi^0_2`$
set in this explicit coding. This is an upper bound only; no completeness
reduction is supplied. The finite-list coding matters: raw edge-indicator
coding does not provide the same finite local certificates automatically.

## Verification and remaining bottleneck

`OrdinalCertificates.lean` compiled successfully with the installed Lean
4.33.1 binary, exit code 0. Its four printed theorem endpoints depend only
on `propext` and `Quot.sound`; no `sorry` was used. The definitions of `row`
and `Edge` match the displayed definitions in the existing formalization.
This checks certificate soundness, the explicit odd-ray match, and failure
of the all-phase natural certificate.

`ReachableRankNecessity.lean` subsequently compiled successfully with the
same installed Lean 4.33.1 binary and cached repository imports, exit code 0.
Its six printed endpoints are `reachable_endpoints_bounded`,
`reachable_maximum_exists`, `rank_isCertificate`, `rank_is_least`,
`avoids_iff_has_natural_certificate`, and
`aperiodic_Ps_has_natural_certificate`. They depend only on `propext`,
`Classical.choice`, and `Quot.sound`; no `sorryAx` appears. The exact receipt
and proof-file hash are recorded in `NECESSITY-FORMALIZATION.md`.

The formerly missing ordinal steps now have checked modules:
`HistoryWellFounded`, `OrdinalHistoryRank`, `HistoryPruning`, and `HistoryConverse`.
They connect actual population axioms and actual realizations to well-foundedness,
attained finite ranks, root rank $`\omega`$, and the first limit/successor pruning
stages. They do not require an external unbounded-height premise. Their scope
is the existing binary natural-date model.

`GenericCertificate` separately removes the Bool/Nat restriction for the
natural-certificate equivalence, including leastness and attainment, with
eight checked endpoints. Finitely many children for each fixed vertex and
label suffice; the alphabet itself need not be finite.
`GenericOrdinalCertificate` has three checked endpoints and removes even the
finite-branching requirement for the ordinal-certificate equivalence. All
printed dependencies are among `propext`, `Classical.choice`, and `Quot.sound`.
These are classical finite-branching and well-founded-rank arguments in a
general formal interface; no novelty of those methods is claimed.

The actual binary history-rank and pruning modules contribute eleven checked
endpoints alongside six from their prior necessity module. Their local
receipts are complete and the combined standalone audit passed locally with
52 endpoints across 11 files at 10:56:58 UTC on 25 September 2026. The
exact-commit hosted result is recorded separately in PR #6 and its checks;
earlier hosted receipts remain historical snapshots.

The remaining written-only statements are the Schmidt-rank/kernel calculation,
the realizing-population pruning fixed point, and the explicit ordinal-rank
calculation at the source paper's full vertex/alphabet generality.

The remaining mathematical bottleneck for a richer reading of Alexander's
question is to define a rank on genealogical structure which distinguishes
avoiders while respecting phase reachability. Ordinary matching-tree rank,
ordinary Schmidt rank of that tree, and all-phase ranking cannot supply that
hierarchy: the first two collapse, and the third has the explicit counterexample
above. Any new structural proposal should specify its recursive operation
before making a claim about which ordinals occur.
