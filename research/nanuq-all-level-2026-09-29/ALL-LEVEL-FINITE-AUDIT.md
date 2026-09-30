# Independent finite audit of the adjacent-copy plane-tree screen

**Verdict: the reported finite enumeration and arithmetic pass.** An independent exhaustive verifier reproduces all four rows of `all-level-screen.json`. The split test is valid for the stated union of displayed quartet topologies. The OR dynamic program preserves exactly that object. Its integer division is exact on every enumerated case.

This verdict concerns the adjacent-copy plane-tree representation for 3 through 6 labels. It does not establish that every network in the external source class has this representation, that restriction to six labels preserves that class, or an all-level NANUQ theorem. Those are separate mathematical obligations.

## What was checked

Inputs:

- `all_level_screen.py`, SHA-256 `504f8985247d12914a26fcae9eaab2d160dcc037ec26de97ac406cc2f2432d18`.
- `all-level-screen.json`, SHA-256 `fa60e8d87b20ce5b9be21c0681d15b89ad026c519e0cadd2736c5ebcf5a513c5`.

The verifier is [independent_all_level_check.py](independent_all_level_check.py). The machine-readable receipt is [independent-all-level-check.json](independent-all-level-check.json). The program neither imports nor executes the screen. It reads its JSON only to compare the final counts. The input hashes were checked again immediately after the exhaustive run and were unchanged. A later, bounded Modified NANUQ update is recorded separately below.

Each label occurs once or twice, with its two copies adjacent in the fixed cyclic order. Every physical tip is treated as a different graph vertex. A displayed labelled tree is obtained by choosing one physical tip for each label and restricting the original tree to those tips. The quartet system records, for each four distinct labels, every resolved quartet that appears under at least one such choice.

| Labels | Duplication masks | Trees directly enumerated | Distinct quartet systems | Anchor coefficients | Physical-copy quartet checks |
|---:|---:|---:|---:|---:|---:|
| 3 | 8 | 36 | 1 | 9 | 0 |
| 4 | 16 | 406 | 3 | 108 | 3,834 |
| 5 | 32 | 5,390 | 16 | 1,600 | 261,695 |
| 6 | 64 | 78,244 | 102 | 22,950 | 11,583,330 |
| Total | 120 | 84,076 | 122 across the four sizes | 24,667 | 11,848,859 |

All coefficients were nonnegative. Their minimum was 0 and maximum was 2 at each size. Every four-label code was one of `1`, `4`, or `5`: the first noncrossing topology, the second noncrossing topology, or both. No crossing topology occurred.

Execution used Python 3.12.14 and took 17.531 seconds. There was no proof-assistant run. This is a finite exhaustive computation supported by the correctness arguments below.

## Independent enumeration and quartet evaluation

The verifier roots an unrooted binary plane tree at the edge incident to physical tip 0. Its remaining tips form an ordinary ordered full binary tree. Instead of the screen's interval/quartet-set dynamic program, the verifier inserts each new rightmost leaf at every position along the existing tree's right spine.

This generation has an inverse: delete the rightmost leaf and suppress its parent. The parent was on the right spine, so its insertion position is recovered uniquely. Induction gives every ordered full binary tree exactly once. The program also directly checks that each generated family has no duplicate tree tuples. It builds the full undirected graph and checks the numbers of edges and vertices and every leaf/internal degree.

With L physical tips, the family therefore has Catalan(L-2) members. Summing over duplication masks yields sum over d=0..n of binomial(n,d) times Catalan(n+d-2). The independent program counts actual generated objects rather than using this formula as its tree counter.

For every tree, graph traversal supplies all physical-tip distances. For every four-label set, the verifier enumerates all choices of one of each label's physical copies. It identifies the quartet using the unique smallest of

`d(a,b)+d(c,d)`, `d(a,c)+d(b,d)`, `d(a,d)+d(b,c)`.

It checks that the other two sums agree and are strictly larger. This classifies the quartet by the tree four-point condition, independently of the screen's interval split test. The union of these explicit four-copy classifications gives the system. The receipt preserves every resulting quartet-system tuple and per-mask counts.

## Why a split witness extends to a global copy choice

Fix one original physical-tip tree T and four distinct labels a,b,c,d. Suppose an edge of T has a copy of a and a copy of b on one side, and a copy of c and a copy of d on the other. Choose those four copies. They are compatible choices because they belong to four distinct labels. Choose any available copy of every other label. This produces one global selection, and its restriction to the four labels displays ab|cd. Additional chosen tips cannot change that induced quartet.

Conversely, if a global selection displays ab|cd, the quartet's central edge corresponds to a nonempty path in the original tree. Any edge on that path separates the selected a,b copies from the selected c,d copies. Thus an original edge supplies the screen's witness. Deleting other tips and suppressing degree-two vertices does not affect this implication.

Consequently, the screen's use of label *presence* on both sides is sufficient even when some duplicated label has a copy on each side. It does not require incompatible assignments within a single quartet.

As an additional computational check, one representative of each of the 122 systems across the four sizes was evaluated by enumerating **global** one-copy-per-label choices. Across 302 such choices, its union of induced quartets agreed with the independent four-copy evaluation. This extra representative check supplements the general argument; it is not being substituted for the exhaustive four-copy check on all trees.

## Why OR-DP does not lose the relevant correlations

For a fixed duplication mask, each edge directed away from physical tip 0 has an interval of physical tips below it. The quartet contribution of that edge is determined only by this interval and its complement in the full fixed tip list. It does not depend on either subtree's internal shape. The system of a whole physical-tip tree is exactly the union of these edge contributions by the preceding argument.

Induct on interval size. The DP's stored keys are exactly the possible unions of contributions from all internal edges in trees on that interval, still evaluated against the full fixed tip list. At a split, every left tree can be combined with every right tree. Combining their two union masks with the fixed contribution of the parent interval produces the whole union. Conversely, every tree has one of those root splits. Two child trees with identical union masks are interchangeable for this operation, so retaining one representative per key cannot remove any possible resulting union. Singleton intervals contribute no quartet because one physical tip cannot contain two distinct labels.

There is a genuine semantic limit: the union mask does **not** preserve which several quartets can be realized simultaneously by a single global choice. Different bits may need different choices. That information is unnecessary for the object actually screened, which is a union over displayed trees. Reusing the OR summary to assert joint realization, switching counts, display probabilities, or independence would require a different proof and data structure.

## Exact arithmetic in the collapsed entries

The independent verifier uses `fractions.Fraction` for every collapsed entry and every coefficient, with no floor division. For each unordered anchor pair and unordered disjoint label pair, it evaluates twice the number of separating displayed topologies divided by the number of displayed topologies.

Every denominator was 1 or 2. The numerator is twice an integer, so division by either denominator is exact. This was checked on all 9,678 such entries, including 4,374 entries with two displayed topologies; none had a nonintegral value. Entries involving an anchor are the specified 0 or 1 and introduce no division. The exact rational coefficients reproduce all 24,667 reported checks.

For a broader input class allowing all three quartet resolutions, replacing a rational average by integer floor division would require separate justification. The present exhaustive representation produces only the three observed codes above, so that potential issue is absent here.

## Boundary of the result

No finite arithmetic or enumeration discrepancy was found. The computational result can support a theorem once the source-class representation and any reduction to at most six labels are proved. It cannot supply either structural step by itself, and it does not establish statistical NANUQ consistency or the correctness of a network-to-tree display correspondence. No Git state, publication record, original screen, or source proof was changed by this audit.

## Added Modified NANUQ endpoint check

At the parent's request, the verifier was extended to test scores `(cherry, separated, adjacent, opposite) = (1/2, 1, 1/2, 1)` on the **already saved** 122 systems. No tree enumeration was repeated. This changes a collapsed entry from 0 to 1 only when the queried endpoints are disjoint from the anchors and form a cherry in a singleton displayed quartet. All other entries retain their previous definition.

All 24,667 exact rational coefficients again pass, with minimum 0 and maximum 2 at each size. The numbers of changed unordered queried entries are 0, 4, 90, and 1,674 for sizes 3, 4, 5, and 6 respectively: 1,768 changes in total. The `modified_nanuq` object in the receipt records this separate computation, its current verifier hash, the reused-receipt hash, and the matching reference counts. Its final evaluation took 0.172 seconds.

For the score slice `(c, 1, 1/2, 1)` with `0 <= c <= 1/2`, the changed entries equal `2c`. Every anchor coefficient is therefore affine in c and satisfies

`alpha(c) = (1 - 2c) alpha(0) + 2c alpha(1/2) >= 0`.

Thus the endpoint checks certify this entire slice on the enumerated representation, rather than merely two numerical choices. Transfer to the external all-level network class continues to depend on the separately assigned structural representation and restriction arguments.

During this addition, the parent updated the original screen to accept `twice_cherry_score=0`, implement the singleton-cherry case, and test the new endpoint; its enumeration functions were unchanged on inspection. The reference JSON gained the corresponding coefficient counts and `modified_failure: null`, with the original counts unchanged. Current hashes after that delta are:

- `all_level_screen.py`: `354e94339306d01c176e68c022de85dad1f008abeade520096821568231a94d5`.
- `all-level-screen.json`: `396e5e2d271ab2675dec2871aa61e39cfbf2c0288c049f26c6a36fd3b4e0cdaf`.

The receipt retains the original input and verifier hashes for the exhaustive run. Its nested endpoint record contains the later hashes. The current verifier can reproduce the full computation, or use `--modified-only` to evaluate just the saved systems.
