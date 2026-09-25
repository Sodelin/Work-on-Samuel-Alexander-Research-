# Periodic lifeline certificates for cellular automata

Status: mathematical reduction, with an exact finite checker specified below. No new cellular-automaton speed limit or novel rule classification is claimed.

## Setting and certificate

Let a binary, translation-invariant cellular automaton act on $`\mathbb Z^2`$, with a finite neighborhood $`N\subset\mathbb Z^2`$ of predecessor offsets and a quiescent zero state. Write $`C_t`$ for the finite set of live cells at generation $`t`$, starting with finite $`C_0`$. A local rule $`F:\{0,1\}^N\to\{0,1\}`$ determines whether target cell $`x`$ is live at $`t+1`$ from the previous states at $`x+n`$, $`n\in N`$. For predecessor $`p=x+n`$, the directed parent-to-child step is $`x-p=-n`$.

Fix finite permitted step sets $`D_A,D_B\subseteq -N`$. A **two-label local certificate** means that, for every local bit pattern $`q`$ with $`F(q)=1`$, the following two candidate sets admit distinct representatives:

```math
W_A(q)=\{-n:n\in N,\ q(n)=1,\ -n\in D_A\},\qquad
W_B(q)=\{-n:n\in N,\ q(n)=1,\ -n\in D_B\}.
```
Equivalently, $`W_A(q)\ne\varnothing`$, $`W_B(q)\ne\varnothing`$, and $`|W_A(q)\cup W_B(q)|\ge2`$. The last condition matters when the sets overlap: one ordinary edge cannot carry both labels. Checking every truth-table row that yields a live target is sufficient, though a rule may admit weaker certificates after unreachable local patterns have been proved impossible.

## Consequence (proved from Alexander's theorem)

**Proposition.** Suppose the certificate holds and the evolution never becomes empty. Then there is a sequence of live cells $`x_0,x_1,\ldots`$ in consecutive generations whose successive parent-to-child steps alternate $`D_A,D_B,D_A,D_B,\ldots`$. The initial generation of this lifeline need not be zero.

**Proof.** Make a vertex $`(x,t)`$ for each $`x\in C_t`$. For every vertex at $`t\ge1`$, use the certificate to choose two distinct live predecessors in $`C_{t-1}`$ and color the corresponding incoming edges $`A`$ and $`B`$. The vertices in $`C_0`$ are the only roots, so there are finitely many roots. Each vertex has finitely many children because $`N`$ is finite. Finite initial support, a finite neighborhood, and a quiescent zero state imply each $`C_t`$ is finite; hence only finitely many vertices have birth time at most any real bound. Nonextinction gives infinitely many vertices. This is a two-gender population in Alexander's sense. The periodic word $`ABAB\ldots`$ is unavoidable by his Proposition 5, producing the lifeline. The edge-color choice ensures its step restrictions. $`\square`$

**Alternating-word velocity corollary.** If, from some generation onward, $`C_{t+T}=C_t+d`$ for fixed positive integer $`T`$ and integer vector $`d`$, then

```math
\boxed{\quad d/T\ \in\ P_{AB}:=\tfrac12\bigl(\operatorname{conv}D_A+\operatorname{conv}D_B\bigr).\quad}
```
To see this, pair consecutive $`A,B`$ steps. Each pair sum belongs to $`D_A+D_B`$, so every average of completed pairs lies in $`\tfrac12\operatorname{conv}(D_A+D_B)=P_{AB}`$. The unmatched endpoint contributes $`O(1/k)`$ to a $`k`$-step average. A spaceship has finite support in each of its $`T`$ phases; any live cell in generation $`t`$ differs by a bounded vector from $`\lfloor(t-t_0)/T\rfloor d`$. Therefore every infinite lifeline has $`(x_k-x_0)/k\to d/T`$, and closedness of $`P_{AB}`$ yields the inclusion. This excludes candidate velocities; it does not establish a spaceship at any permitted velocity or make the bound sharp.

The same argument works for a certified periodic word of labels $`L_1\ldots L_p`$: its velocity lies in $`p^{-1}\sum_{i=1}^p\operatorname{conv}D_{L_i}`$. The two-label case is the smallest nonconstant example.

**Stronger consequence from constant words.** The same two-label certificate also lets us apply Alexander's theorem separately to the periodic words $`AAAA\ldots`$ and $`BBBB\ldots`$. These give an infinite all-$`A`$ lifeline and an infinite all-$`B`$ lifeline; they need not be the same path. In a finite-support spaceship, *every* infinite lifeline has asymptotic velocity $`v=d/T`$, by the finite-phase argument above. Averages of all-$`A`$ steps lie in $`\operatorname{conv}D_A`$, and averages of all-$`B`$ steps lie in $`\operatorname{conv}D_B`$. Hence the same hypotheses actually give

```math
\boxed{\quad v\in\operatorname{conv}D_A\cap\operatorname{conv}D_B
\ \subseteq\ \tfrac12(\operatorname{conv}D_A+\operatorname{conv}D_B).\quad}
```
The inclusion holds because any $`v`$ in both convex hulls equals $`(v+v)/2`$. Likewise, the intersection is contained in the average convex set for *every* periodic mixture of these fixed label-step sets. Thus the alternating polygon alone cannot improve the velocity exclusion already obtained from the two constant-label paths. This observation corrects the initial search motivation for this note. It is a deduction from Alexander's periodic theorem, not a claim of a new sharp speed limit.

## Exact checker and bounded research target

For a radius-one binary rule, enumerate all $`2^9=512`$ predecessor bit patterns, retaining those where $`F(q)=1`$. For a proposed pair $`(D_A,D_B)`$, compute $`W_A,W_B`$ for each retained pattern and reject the pair if either is empty or their union has size less than two. The companion `check_local_certificate.py` implements this finite check for a supplied neighborhood, rule function, and two step sets; its toy-rule demo checks all eight rows, three of which produce live output. The witness pairs can be recorded as a small, independently replayable certificate table, not merely a yes/no result. For spaceship velocities, compute the exact polygon $`\operatorname{conv}D_A\cap\operatorname{conv}D_B`$. The alternating polygon can be computed too, but is a weaker diagnostic bound. For an integer direction $`u`$, the intersection implies the quick necessary bound $`u\cdot v\le\min(\max_{a\in D_A}u\cdot a,\max_{b\in D_B}u\cdot b)`$; computing the intersection itself can be stronger still.

A useful next question is whether a **stateful or phase-sensitive certificate** can constrain successive predecessor choices beyond the static sets $`D_A,D_B`$, producing a bound stronger than their convex-hull intersection. No such improvement is established here. Any proposed rule-specific result should be compared with that intersection, direct geometric bounds, and published bounds before claiming a gain. For outer-totalistic B3 rules, Johnston already established broad orthogonal, diagonal, and arbitrary-slope bounds; merely recomputing them is reproduction, not novelty.

As a nonvacuous sanity check, consider the anisotropic rule “the next cell is live exactly when its west neighbor and at least one of its northwest or southwest neighbors were live.” Use $`D_A=\{E,NE\}`$, $`D_B=\{E,SE\}`$. If west and northwest are live, label the west predecessor $`A`$ (step $`E`$) and northwest $`B`$ (step $`SE`$). If west and southwest are live, label southwest $`A`$ (step $`NE`$) and west $`B`$ (step $`E`$). A vertical two-cell domino translates east one cell every generation. Its polygon bound is a useful test of the checker but gives no interesting new speed limit: the rule's mandatory west predecessor already constrains its bounding box more strongly.

## Prior work and novelty boundary

| Source | Established result relevant here | Boundary for this note |
|---|---|---|
| Samuel A. Alexander, *Biologically Unavoidable Sequences*, Electronic Journal of Combinatorics 20(1), P31 (2013), §2 Proposition 5 and §5 Lemma 18/Theorem 19. [Journal](https://www.combinatorics.org/ojs/index.php/eljc/article/view/v20i1p31), [arXiv](https://arxiv.org/abs/1212.0186) | Every periodic gender word is unavoidable in the specified infinite population; his cell-time graph finds a lifeline avoiding any chosen two directions under birth $`\ge3`$, survival $`\ge1`$. | The certificate above is an explicit reduction to his theorem. It is not a claim that periodic lifelines themselves are newly discovered. |
| Nathaniel Johnston, *The B36/S125 “2×2” Life-Like Cellular Automaton* (2010), [preprint](https://arxiv.org/abs/1203.1644), and his [author exposition](https://njohnston.ca/2009/10/spaceship-speed-limits-in-life-like-cellular-automata/) | For broad B3 Life-like families, orthogonal speed is at most $`c/2`$, diagonal at most $`c/3`$; the exposition also states a general slope bound, including $`2c/5`$ for a two-vertical-to-one-horizontal displacement. | Do not announce arbitrary-slope bounds or the $`c/2,c/3`$ limits as new consequences. Johnston's detailed assumptions for some stronger Life-specific bounds differ from Alexander's broader family. |

## Formalization boundary

The convex-hull intersection and its containment in every periodic mixture could be formalized independently in Lean. That would verify only the algebraic velocity step. The substantive local-rule-to-infinite-lifeline bridge still rests on Alexander's graph theorem unless formalized separately. No Lean proof is included in this note.
