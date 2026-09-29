# Minimum crossing width determines the entire tail

**Status: proved in Lean.** The checked source is [GeneralRigidity.lean](../lean/SamuelAlexanderResearch/GeneralRigidity.lean). This resolves the general finite-label statement in proposal 2, including the degenerate case $`k=0`$.

Let $`P`$ be the existing simple labelled population in natural birth order. Every nonroot has a parent of each of $`k`$ labels, every vertex has at most $`k`$ children, and the root set is finite. Suppose the actual crossing count is eventually

```math
C_n=\frac{k(k+1)}2.
```

Then, after a finite cutoff, the actual edges are exactly

```math
u\longrightarrow v\quad\Longleftrightarrow\quad u<v\le u+k.
```

The hypothesis concerns every sufficiently late cut. One isolated cut attaining the bound does not imply the whole tail conclusion. Edge labels need not be permanent vertex genders. The theorem determines adjacency; it does not by itself assert that every word is realized with arbitrary edge labels.

## Proof

At a cut $`n`$ after all roots, future vertex $`n+i`$ requires at least $`k-i`$ parents before the cut. Thus the first $`k`$ future vertices already account for at least the full triangular number of crossing edges. If the cut attains that number, no crossing edge can target $`n+k`$ or any later vertex.

Apply this observation at cut $`u+1`$. Every outgoing edge from $`u`$ must terminate among $`u+1,\ldots,u+k`$. Equal crossing counts at cuts $`u`$ and $`u+1`$, together with the full-degree conservation identity and the absence of roots, force zero local degree defect. Hence $`u`$ has exactly $`k`$ children. There are only $`k`$ possible distinct positions, so all are occupied.

The formal proof includes a generic finite-sum equality lemma, exclusion of late crossing targets, full-degree regularity from equal neighboring cuts, and a support-aware calculation of the full outgoing degree. No adjacency pattern, regularity conclusion, or abstract total-edge count is a premise.

## Endpoints and verification

- `minimum_cut_no_late_target`: equality at one root-free cut excludes every late target.
- `minimum_tail_edges`: a supplied root-free cutoff gives the exact edge pattern on that same tail.
- `eventually_minimum_tail_edges`: derives a suitable cutoff from eventual numerical equality, without assuming it is already beyond every root.

Direct Lean checking passes with only `propext`, `Classical.choice`, and `Quot.sound` among the printed dependencies. The core remains Std-only. This is an extension of the repository's checked binary argument; literature priority is a separate question.
