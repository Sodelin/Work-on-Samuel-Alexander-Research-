# Proposal 10 audit: a stateful certificate with a strict static gap

**Disposition.** A small synthetic three-state cellular automaton gives a proved strict gap: its best possible two-label, state-blind constant-step certificate permits eastward speed 1, while an exact two-state potential bounds eastward speed by 0. A finite two-cell oscillator shows the rule has a nonextinct finite-support orbit. The example demonstrates the certificate mechanism; it is not a new speed theorem for a published Life-like rule. The remaining research gate is to obtain a comparably valid gain for a natural binary or published rule after comparison with direct geometric bounds.

## Exact rule

Work on $`\mathbb Z^2`$ with east $`+x`$ and north $`+y`$. The states are dead $`0`$ and two live phases $`R,L`$. At each synchronous step, a target cell becomes:

1. $`L`$, if its west predecessor is $`R`$ and either its northwest or southwest predecessor is $`R`$;
2. otherwise $`R`$, if its east predecessor is $`L`$ and either its northeast or southeast predecessor is $`L`$;
3. otherwise dead.

The first clause has priority if both fire. This makes a deterministic, translation-invariant, finite-neighborhood, quiescent cellular automaton. Both clauses require two **distinct** live predecessor cells. In the first clause, every selected parent is $`R`$ and the parent-to-target horizontal displacement is $`+1`$. In the second, every selected parent is $`L`$ and the displacement is $`-1`$. A local pattern producing $`L`$ cannot violate the first claim, and one producing $`R`$ cannot violate the second, even when additional live neighbors are present.

## Local rule to infinite lifeline

Start from any finite configuration whose evolution never becomes empty. Build a graph with one vertex for each live cell-time pair. For each later live vertex choose its aligned parent (west for an $`L`$ target, east for an $`R`$ target) as label $`A`$, and one qualifying diagonal parent as label $`B`$. Every later vertex has both incoming labels, and their parents are distinct. The only roots are the finitely many generation-zero live cells. Finite neighborhood and finite initial support give finitely many vertices in each generation and finite outdegree. Thus Alexander's population hypotheses hold, and his periodic-word theorem supplies infinite all-$`A`$, all-$`B`$, and alternating lifelines. Because the potential inequality holds on **every** chosen edge, ordinary König's lemma already supplies the infinite path needed for this synthetic velocity bound; label-word unavoidability is unnecessary for that bound. Alexander's theorem becomes relevant when a bound relies on a prescribed label word.

Give each live vertex its visible phase $`q\in\{R,L\}`$. **Every selected edge**, irrespective of label, is one of

| source $`q`$ | target $`q'`$ | horizontal step $`d_x`$ |
|---|---|---:|
| $`R`$ | $`L`$ | $`+1`$ |
| $`L`$ | $`R`$ | $`-1`$ |

For direction $`u=(1,0)`$, set $`c=0`$, $`h(R)=1`$, and $`h(L)=0`$. Both transitions satisfy the exact potential equality

```math
u\cdot d=c+h(q)-h(q').
```

Along any certified lifeline of $`k`$ edges, telescoping gives $`x_k-x_0=h(q_0)-h(q_k)\in\{-1,0,1\}`$. Every such path has horizontal mean speed 0. More directly, the Lean theorem `all_generations_in_initial_charge_strip` proves by induction that every live cell in every generation retains an initial value of $`x+h(q)`$ within a fixed interval. `finite_support_has_extreme_charges` supplies attained extremes for a finite nonempty starting configuration, and `no_horizontal_spaceship` proves that a recurrence $`C_T=C_0+\Delta`$ forces $`\Delta_x=0`$. The argument needs only one translated recurrence and does not use a limit. The reverse-direction speed is also zero because the charge strip bounds horizontal position on both sides. The Lean module `lean/SamuelAlexanderResearch/StatefulCA.lean` proves these global claims, the local parent claims, and the two-cell orbit.

## Strict comparison with the *same rule's* static certificate

Erase the visible phase from the edge constraints and allow any fixed two-label step sets $`D_A,D_B`$ that supply distinct representatives for **every** live-output local row. For example, the following fixed sets work:

```math
D_A=\{E,W\},\qquad D_B=\{NE,SE,NW,SW\}.
```

They assign the aligned predecessor to $`A`$ and the diagonal predecessor to $`B`$ in either phase. Their constant-label velocity hulls intersect along $`\{(x,0):-1\le x\le1\}`$, so their eastward bound is $`+1`$.

More strongly, **no valid state-blind fixed-set choice can improve that eastward bound**. Consider two legitimate local rows in isolation: an $`L`$ target supported by exactly west+northwest $`R`$ parents, with steps $`E=(1,0)`$ and $`SE=(1,-1)`$; and an $`L`$ target supported by exactly west+southwest $`R`$ parents, with steps $`E=(1,0)`$ and $`NE=(1,1)`$. Each label must have an admissible step from each row. Thus each of $`D_A,D_B`$ contains an eastward step with vertical component $`\le0`$ and an eastward step with vertical component $`\ge0`$. Interpolating those two steps shows $`(1,0)\in\operatorname{conv}D_A\cap\operatorname{conv}D_B`$. Every neighborhood step has horizontal displacement at most 1, so the optimal static intersection bound in the east direction is **exactly 1**. The stateful potential improves it strictly to **0**.

This comparison is with the full static constant-label convex-hull intersection, not merely with an alternating-word average polygon. The Lean `InConv` predicate uses rational barycentric weights and proves an explicit rational witness for $`(1,0)`$ in each hull of every valid certificate. Those rational witnesses also establish membership in the usual real convex hulls; that rational-to-real embedding is explained mathematically here but is not separately formalized in the Lean module. The upper bound 1 follows directly from the six allowed steps, each with horizontal component at most 1. Different constant-label paths may witness the two hulls, but a finite spaceship has the same asymptotic velocity on every infinite live path.

## Nonvacuity and exact checks

Two vertically adjacent $`R`$ cells at $`(0,0),(0,1)`$ become two $`L`$ cells at $`(1,0),(1,1)`$, then return to the original $`R`$ pair. No other cells are produced, so this is a finite nonextinct period-two oscillator. The independent checker `checks/check_stateful_ca.py` exhausts all $`3^6=729`$ local input rows. It found 135 $`L`$-output and 110 $`R`$-output rows, checked the two qualifying predecessors and the potential inequality on every live row, and verified eight steps of the two-phase orbit. The Lean module separately proves both full configuration transitions, $`R`$ domino to $`L`$ domino and back, plus the finite-support spaceship obstruction; these proofs do not rely on finite simulation.

## Prior work and the missing gate

Alexander's [*Biologically Unavoidable Sequences*](https://www.combinatorics.org/ojs/index.php/eljc/article/view/v20i1p31) proves periodic-label paths in the relevant finite-branching populations and applies them to Life-like lifelines. Johnston's [B3 spaceship speed-limit proof](https://njohnston.ca/2009/10/spaceship-speed-limits-in-life-like-cellular-automata/) and [B36/S125 paper](https://arxiv.org/abs/1203.1644) already establish broad orthogonal, diagonal, and arbitrary-slope bounds for their rule families. Those results do not establish a bound for this synthetic three-state rule, nor does this example improve them.

The potential inequality is a standard weighted-graph reweighting and telescoping argument. [Young, Tarjan, and Orlin (1991), §3](https://www.cs.ucr.edu/~neal/publication/Tarjan91Faster.pdf) explicitly uses the edge reweighting $`c^\pi(u,v)=c(u,v)+\pi(u)-\pi(v)`$; [Karp's primary cycle-mean paper](https://www2.eecs.berkeley.edu/Pubs/TechRpts/1977/Archive/ERL-m-77-47.pdf) is earlier prior work on computing extremal cycle means (maximum means follow by negating weights). The novelty question remains open here: find a **binary or published rule** whose complete local truth table supports a finite state graph, prove that every selected predecessor edge respects it, and show its rational cycle-mean bound strictly improves both the optimal static intersection and known direct or published bounds. This three-state example is deliberately phase-driven; the rule itself visibly forces horizontal backtracking, so it should be treated as a feasibility witness for the certificate architecture, not as an intrinsically difficult CA speed limit.
