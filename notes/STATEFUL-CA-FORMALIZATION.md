# A stateful cellular-automaton certificate with a strict static gap

The Lean module [`StatefulCA.lean`](../lean/SamuelAlexanderResearch/StatefulCA.lean) defines a synthetic three-state, two-dimensional cellular automaton and proves a complete rule-to-trajectory horizontal obstruction. This is a method demonstration, not a new bound for a published binary or Life-like rule.

## Rule and local certificate

The states are dead, `r`, and `l`. An `r` west neighbor together with an `r` northwest or southwest neighbor creates `l`; otherwise an `l` east neighbor together with an `l` northeast or southeast neighbor creates `r`; otherwise the output is dead. The first clause wins if both fire. Directions in the module identify **predecessor locations** relative to the target, while `xStep` and `yStep` are predecessor-to-target displacements.

`every_live_row_has_two_parents` proves, for every six-neighbor input row with a live output, two distinct live predecessors, one aligned and one diagonal. For each selected edge, the parent-to-child horizontal step equals the phase-potential drop: `dx = potential(parent) - potential(child)`, where `potential(r)=1` and `potential(l)=0`. The finite checker [`check_stateful_ca.py`](../checks/check_stateful_ca.py) independently exhausts the $`3^6=729`$ rows; it finds 110 `r` and 135 `l` outputs and checks the selected parents and charge identity on each live row.

## Global endpoint

`selected_edge_charge` derives conservation of `x + potential(state)` on a chosen parent edge. `evolve_preserves_charge_bound` proves that a charge strip containing all live cells is invariant under a full generation update, for arbitrary configurations. `all_generations_in_initial_charge_strip` inducts over every finite generation. `finite_support_has_extreme_charges` proves that a finite nonempty initial support has attained minimum and maximum charge. `no_horizontal_spaceship` combines those facts: if an iterate equals a translate of the initial finite nonempty configuration, its horizontal translation is zero, even when the vertical translation is arbitrary. Period zero causes no exception. The proof needs neither an infinite-path choice theorem nor an asymptotic limit.

`rDomino_step`, `lDomino_step`, and `nontrivial_two_cycle` prove a full-configuration period-two orbit: the two `r` cells at `(0,0),(0,1)` become two `l` cells at `(1,0),(1,1)` and return with no other births. `rDomino_finite` proves finite support. The final theorem `stateful_rule_static_gap_and_global_obstruction` bundles the certificate, optimal static comparison, global spaceship obstruction, finite example, and its full transitions.

## Exact static comparison and formal scope

`FixedCert a b` quantifies over **every** live-output local row and asks two distinct live parents whose directions belong to fixed, phase-blind label sets `a,b`. `InConv D v` represents membership in the full rational convex hull of all six possible predecessor-to-target vectors using nonnegative rational barycentric weights. `no_static_east_improvement` proves that, for every valid pair of fixed label sets, $`(1,0)`$ lies in **both** hulls. The witnesses are either the aligned east direction or equal weights on its two east diagonals. `any_static_convex_east_bound` proves no point in either rational hull has east coordinate above 1; `optimal_static_east_bound` combines both directions. `aligned_diagonal_certificate` supplies an actual valid fixed two-label certificate. Thus the optimal bound in this particular rational static certificate family is exactly 1 while the stateful global obstruction is 0.

The explicit rational barycentric witnesses also give points in the usual real convex hulls by inclusion $`\mathbb Q\hookrightarrow\mathbb R`$. That embedding is a mathematical observation; this module does not import Mathlib or formalize real convex geometry. It does formalize both rational upper and lower bounds, including the exact static optimum for the family specified above.

## Prior work and research gate

The potential algebra is classical graph reweighting: [Young, Tarjan, and Orlin (1991), §3](https://www.cs.ucr.edu/~neal/publication/Tarjan91Faster.pdf) writes the corresponding edge-cost change $`c^\pi(u,v)=c(u,v)+\pi(u)-\pi(v)`$. [Karp (1978)](https://www2.eecs.berkeley.edu/Pubs/TechRpts/1977/Archive/ERL-m-77-47.pdf) gives primary prior work on extremal cycle means. [Alexander (2013)](https://www.combinatorics.org/ojs/index.php/eljc/article/view/v20i1p31) supplies the biological-unavoidability and Life-like-lifeline context; his periodic-word theorem is unnecessary for this particular certificate because **every** selected parent edge conserves charge. [Johnston's Life-like speed-limit work](https://arxiv.org/abs/1203.1644) is separate prior art for published rule families.

The remaining research gate is a binary or published rule for which a complete local-rule-to-stateful-certificate bridge yields an improvement over its strongest relevant static and known direct bounds. This synthetic phase-driven rule establishes feasibility of the proof architecture only.

Verification from the repository root: `lean lean/SamuelAlexanderResearch/StatefulCA.lean` with Lean 4.33.1, and `python checks/check_stateful_ca.py`.
