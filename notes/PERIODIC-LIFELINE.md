# Periodic lifeline certificates for cellular automata

Status: mathematical reduction, with an exact finite checker specified below. No new cellular-automaton speed limit or novel rule classification is claimed.

## Setting and certificate

Let a binary, translation-invariant cellular automaton act on \(\mathbb Z^2\), with a finite neighborhood \(N\subset\mathbb Z^2\) of predecessor offsets and a quiescent zero state. Write \(C_t\) for the finite set of live cells at generation \(t\), starting with finite \(C_0\). A local rule \(F:\{0,1\}^N\to\{0,1\}\) determines whether target cell \(x\) is live at \(t+1\) from the previous states at \(x+n\), \(n\in N\). For predecessor \(p=x+n\), the directed parent-to-child step is \(x-p=-n\).

Fix finite permitted step sets \(D_A,D_B\subseteq -N\). A **two-label local certificate** means that, for every local bit pattern \(q\) with \(F(q)=1\), the following two candidate sets admit distinct representatives:

\[
W_A(q)=\{-n:n\in N,\ q(n)=1,\ -n\in D_A\},\qquad
W_B(q)=\{-n:n\in N,\ q(n)=1,\ -n\in D_B\}.
\]

Equivalently, \(W_A(q)\ne\varnothing\), \(W_B(q)\ne\varnothing\), and \(|W_A(q)\cup W_B(q)|\ge2\). The last condition matters when the sets overlap: one ordinary edge cannot carry both labels. Checking every truth-table row that yields a live target is sufficient, though a rule may admit weaker certificates after unreachable local patterns have been proved impossible.

## Consequence (proved from Alexander's theorem)

**Proposition.** Suppose the certificate holds and the evolution never becomes empty. Then there is a sequence of live cells \(x_0,x_1,\ldots\) in consecutive generations whose successive parent-to-child steps alternate \(D_A,D_B,D_A,D_B,\ldots\). The initial generation of this lifeline need not be zero.

**Proof.** Make a vertex \((x,t)\) for each \(x\in C_t\). For every vertex at \(t\ge1\), use the certificate to choose two distinct live predecessors in \(C_{t-1}\) and color the corresponding incoming edges \(A\) and \(B\). The vertices in \(C_0\) are the only roots, so there are finitely many roots. Each vertex has finitely many children because \(N\) is finite. Finite initial support, a finite neighborhood, and a quiescent zero state imply each \(C_t\) is finite; hence only finitely many vertices have birth time at most any real bound. Nonextinction gives infinitely many vertices. This is a two-gender population in Alexander's sense. The periodic word \(ABAB\ldots\) is unavoidable by his Proposition 5, producing the lifeline. The edge-color choice ensures its step restrictions. \(\square\)

**Spaceship velocity corollary.** If, from some generation onward, \(C_{t+T}=C_t+d\) for fixed positive integer \(T\) and integer vector \(d\), then

\[
\boxed{\quad d/T\ \in\ P_{AB}:=\tfrac12\bigl(\operatorname{conv}D_A+\operatorname{conv}D_B\bigr).\quad}
\]

To see this, pair consecutive \(A,B\) steps. Each pair sum belongs to \(D_A+D_B\), so every average of completed pairs lies in \(\tfrac12\operatorname{conv}(D_A+D_B)=P_{AB}\). The unmatched endpoint contributes \(O(1/k)\) to a \(k\)-step average. A spaceship has finite support in each of its \(T\) phases; any live cell in generation \(t\) differs by a bounded vector from \(\lfloor(t-t_0)/T\rfloor d\). Therefore every infinite lifeline has \((x_k-x_0)/k\to d/T\), and closedness of \(P_{AB}\) yields the inclusion. This excludes candidate velocities; it does not establish a spaceship at any permitted velocity or make the bound sharp.

The same argument works for a certified periodic word of labels \(L_1\ldots L_p\): its velocity lies in \(p^{-1}\sum_{i=1}^p\operatorname{conv}D_{L_i}\). The two-label case is the smallest nonconstant example.

## Exact checker and bounded research target

For a radius-one binary rule, enumerate all \(2^9=512\) predecessor bit patterns, retaining those where \(F(q)=1\). For a proposed pair \((D_A,D_B)\), compute \(W_A,W_B\) for each retained pattern and reject the pair if either is empty or their union has size less than two. The companion `check_local_certificate.py` implements this finite check for a supplied neighborhood, rule function, and two step sets; its toy-rule demo checks all eight rows, three of which produce live output. The witness pairs can be recorded as a small, independently replayable certificate table, not merely a yes/no result. Compute the exact rational velocity polygon from the finite set \(\{(a+b)/2:a\in D_A,b\in D_B\}\) via a planar convex hull. A directional upper bound for integer normal \(u\) is the exact rational number \((\max_{a\in D_A}u\cdot a+\max_{b\in D_B}u\cdot b)/2\).

A useful search target is a **specific anisotropic or isotropic non-totalistic rule** with a known finite spaceship for which this certified polygon excludes a candidate speed that a simpler one-label direction argument permits. Check known literature and direct geometric bounds before claiming a result. For outer-totalistic B3 rules, Johnston already established broad orthogonal, diagonal, and arbitrary-slope bounds; merely recomputing them is reproduction, not novelty.

As a nonvacuous sanity check, consider the anisotropic rule “the next cell is live exactly when its west neighbor and at least one of its northwest or southwest neighbors were live.” Use \(D_A=\{E,NE\}\), \(D_B=\{E,SE\}\). If west and northwest are live, label the west predecessor \(A\) (step \(E\)) and northwest \(B\) (step \(SE\)). If west and southwest are live, label southwest \(A\) (step \(NE\)) and west \(B\) (step \(E\)). A vertical two-cell domino translates east one cell every generation. Its polygon bound is a useful test of the checker but gives no interesting new speed limit: the rule's mandatory west predecessor already constrains its bounding box more strongly.

## Prior work and novelty boundary

| Source | Established result relevant here | Boundary for this note |
|---|---|---|
| Samuel A. Alexander, *Biologically Unavoidable Sequences*, Electronic Journal of Combinatorics 20(1), P31 (2013), §2 Proposition 5 and §5 Lemma 18/Theorem 19. [Journal](https://www.combinatorics.org/ojs/index.php/eljc/article/view/v20i1p31), [arXiv](https://arxiv.org/abs/1212.0186) | Every periodic gender word is unavoidable in the specified infinite population; his cell-time graph finds a lifeline avoiding any chosen two directions under birth \(\ge3\), survival \(\ge1\). | The certificate above is an explicit reduction to his theorem. It is not a claim that periodic lifelines themselves are newly discovered. |
| Nathaniel Johnston, *The B36/S125 “2×2” Life-Like Cellular Automaton* (2010), [preprint](https://arxiv.org/abs/1203.1644), and his [author exposition](https://njohnston.ca/2009/10/spaceship-speed-limits-in-life-like-cellular-automata/) | For broad B3 Life-like families, orthogonal speed is at most \(c/2\), diagonal at most \(c/3\); the exposition also states a general slope bound, including \(2c/5\) for a two-vertical-to-one-horizontal displacement. | Do not announce arbitrary-slope bounds or the \(c/2,c/3\) limits as new consequences. Johnston's detailed assumptions for some stronger Life-specific bounds differ from Alexander's broader family. |

## Formalization boundary

The finite convex-hull inclusion could be formalized independently in Lean using sums over a periodic list of finite step sets. That would verify only the algebraic velocity step. The substantive local-rule-to-infinite-lifeline bridge still rests on Alexander's graph theorem unless formalized separately. No Lean proof is included in this note.
