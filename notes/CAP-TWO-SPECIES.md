# Optimal child cap while retaining an inspecies

**Status: proved in Lean.** [CapTwoSpecies.lean](../lean/SamuelAlexanderResearch/CapTwoSpecies.lean) strengthens the checked [two-child construction](CAP-TWO-THRESHOLD.md). The underlying graph is independent of the target; only its permanent source genders depend on the chosen word.

Every positive port $`x`$ represents one original edge, with

```math
\operatorname{source}(x)=\lfloor x/2\rfloor,
\qquad
\operatorname{target}(x)=\operatorname{source}(x)+1+(x\bmod2).
```

Port zero is omitted because the original graph has no edge from zero to one. An arc from port $`x`$ to port $`y`$ means that the original edges are consecutive: $`\operatorname{source}(y)=\operatorname{target}(x)`$.

## Cofinite descendants

For every retained port $`x`$, every port $`y`$ satisfying

```math
\operatorname{source}(y)\ge\operatorname{target}(x)
```

is a strict descendant. Equality gives a direct arc. Larger source indices are reached by inserting the original consecutive edges; the proof is an induction on the destination source index.

Consequently every non-descendant has index below $`2\operatorname{target}(x)`$. Thus each retained vertex has only finitely many non-descendants. The retained set is infinite and ancestrally closed. If an infinite ancestrally closed subset omitted $`x`$, it would have to omit all descendants of $`x`$, leaving only a finite set. This proves inclusion minimality and hence the inspecies property.

The graph is also weakly connected, since any two ports reach a sufficiently late common port. Convexity and reflection hold in the retained graph. All arcs already have both endpoints retained, so evaluating the predicates on the actual induced graph gives the same result; deleted port zero is not counted as a vertex or root.

## Combined theorem

`cap_two_inspecies_avoider` supplies, for every non-eventually-periodic binary target:

- an eligible population with permanent vertex genders and child cap two;
- a specieslike whole retained graph;
- a whole retained graph that is an inspecies;
- reflection in the actual induced graph;
- avoidance of the prescribed target.

The separately checked `CapTwo` module gives exactly two children at every vertex, exactly three roots, full path-language preservation, and impossibility below child cap two. The older cap-three productive-core witness remains correct; the line-graph construction improves its uniform child cap while retaining the whole-graph species properties.

This is a proof of the exact model statement, not a literature-priority certificate. Directed line graphs are classical. The relevant contribution to assess is their application to this particular population model and the simultaneous target, degree, root and species guarantees.
