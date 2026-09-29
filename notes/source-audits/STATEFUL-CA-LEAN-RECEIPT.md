# Stateful cellular automaton: verification receipt

Date: 25 September 2026. Status: frozen local proof, reviewed and sent for
integration. This is separate from the completed PR 5 release.

## Exact source and checks

- Module: `lean/SamuelAlexanderResearch/StatefulCA.lean`.
- Local SHA-256: `f02f2b808a0c15d85b26c55559b54621599e89a04c44957679612f24bd4c9bba`.
- Compiler: Lean 4.33.1, importing `Std` and the bundled rational-number lemmas.
- Frozen source compilation: passed; the coordinating task also generated
  the object file and checked the endpoint axiom reports.
- Eight selected endpoint reports contain only the permitted subset of
  `propext`, `Classical.choice`, and `Quot.sound`. The charge-strip induction
  and the concrete nonemptiness witness require only `propext`.
- No `sorry`, `admit` or custom axiom declarations.
- Independent finite checker: `checks/check_stateful_ca.py`, SHA-256
  `f21a40c5f4b7c60dfa7527a6f9bd6d0840516504dca982535c1152debc1b71f5`.
  It checks all 729 local rows and eight generations of the sample orbit.

## What the proof certifies

| Endpoint | Verified conclusion |
| --- | --- |
| `every_live_row_has_two_parents` | Every live output has two distinct selected live predecessors obeying the exact potential identity. |
| `optimal_static_east_bound` | Every valid fixed two-label certificate includes the east unit vector in both rational convex hulls, and every point of their intersection has east coordinate at most one. |
| `all_generations_in_initial_charge_strip` | A charge bound for an initial configuration holds at every generation of the actual update rule. |
| `no_horizontal_spaceship` | If a finite, nonempty configuration evolves into a translated copy of itself, its horizontal translation is zero. |
| `nontrivial_two_cycle`, `rDomino_finite`, `rDomino_nonempty` | A finite, nonempty two-cell oscillator exists, with full configuration equalities including the dead exterior. |
| `stateful_rule_static_gap_and_global_obstruction` | The actual certificate, exact static comparison, global obstruction and concrete finite orbit are packaged together. |

The global proof uses attained minimum and maximum initial charge. It does
not assume an infinite lifeline, a velocity limit, or the desired strip bound.
The nonempty and finite-support assumptions are explicit. The translated
recurrence is an equality of full configurations after an actual iterate.

## Semantic review and limits

An independent read-only audit checked the static-certificate quantifiers,
convex coefficients, coordinate signs and full-configuration oscillator
equalities. The coordinator separately reviewed the actual evolution,
charge-strip induction and extremal-charge recurrence argument.

The rule has three states and is synthetic. The strict comparison concerns
fixed two-label local convex-hull certificates. The encoded convex hulls use
rational coefficients; the explicit rational witnesses also lie in the usual
real hulls mathematically, but a Mathlib real-hull adapter is not part of this
module. No improved bound for a published or binary rule is claimed.

The potential method has established antecedents. See the
[mathematical audit](PROPOSAL10-STATEFUL-CA-AUDIT.md) and
[primary-source comparison](PROPOSALS3-10-SOURCE-AUDIT.md).
