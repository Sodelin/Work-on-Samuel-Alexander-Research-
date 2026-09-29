# Scope review of the new generic pruning and mortal-rank proofs

Date: 29 September 2026. Review mode: independent read-only inspection of statements, definitions and proof structure. The parent reports successful Lean compilation with standard axioms for the 10 selected pruning endpoints and 9 selected mortal-rank endpoints. This review did not rerun builds and does not replace those compiler receipts.

**Verdict:** no semantic blocker found for the stated, finitely branching, reachable-state results. They characterize actual sequence realization, extend to graphs containing both realizing and nonrealizing states, and do not assume global avoidance. The principal reporting boundary is that these files prune reachable vertex/phase states, rather than the older tree of all finite histories with an extra superroot.

## Actual sequence realization and phase

The imported `GenericCertificate.Realizes E s` means that there is a function `p : Nat → V` with `E (p n) (p (n+1)) (s n)` for every `n`. In a general labelled relation this is an infinite labelled walk. In an Alexander population, strict birth-time increase along edges makes its vertices distinct, so it is a path. That chronological deduction is mathematically immediate but is not a new population-specific adapter theorem in these two modules.

The state type records both a vertex and a target phase, together with proof that the target prefix reaches that pair. `Step child parent` increases phase by one and consumes the letter at the parent's phase. The relation is oriented consistently throughout: the child is the first argument. Reachability is essential when concluding that an infinite continuation from an arbitrary state realizes the full word. It supplies the finite prefix to join to that continuation; a ray for an unrelated suffix at an unreachable pair would not suffice.

`GenericPruning.start_core_iff_realizes_from` anchors the abstraction to a specified starting vertex: the phase-zero state belongs to the core if and only if there is an actual matching walk whose first vertex is that vertex. The proof explicitly establishes that the projected phase at step `n` is `n`. The corollaries `realizes_iff_surviving_start` and `realizes_iff_nonempty_core` consequently characterize the full word, not merely some suffix. At a general state of phase `k`, the continuation consumes `s (k+n)`. The same vertex can therefore have different behavior at different phases.

## Pruning and finite branching

`survives R n x` means that there is a continuation of exactly `n` edges from `x`; round zero retains every state. The monotonicity lemma proves these stages decrease, and `survives_successor_iff` proves that explicitly requiring retention from the preceding round is redundant. The `core` is the intersection of all finite stages.

Finite branching is used precisely where it is needed: `core_iff_child` extracts a single child that survives every finite round, and `core_iff_live` repeatedly chooses such a child to produce an infinite chain. Label-wise finite children suffice, since each state has one required next label and its successor phase is forced. No finite alphabet, countability, root bound or birth-date hypothesis is required for the generic statements.

The finite-branching assumption cannot be silently removed. A root with infinitely many children leading to finite chains of every possible length survives all finite rounds but has no infinite continuation. In this example the intersection of finite stages is not a fixed point. Under the stated assumption, the code proves that the core is a fixed point of the successor operator and contains every other fixed point; the stronger inclusion for every postfixed set is also proved.

Calling the intersection the stage at omega is valid mathematical terminology. The code itself defines finite stages and their intersection, rather than a general ordinal-indexed pruning recursion. Under avoidance every reachable state is removed at some finite round, so this state core is empty. An added superroot above all starting histories can survive all finite rounds and disappear one round later. The old history-tree omega/omega-plus-one description must therefore remain distinguished from the new state-pruning theorem. These files do not independently formalize a bridge between those two objects.

## The mortal complement and exact rank

`GenericMortalRank.Mortal R` is the subtype of states outside the core. `mortal_forward_closed` proves that every successor of a mortal state is mortal. `mortal_wellFounded` proves the restricted relation well-founded without any global-avoidance premise and even without finite branching: an infinite chain inside that subtype would make its first state live and hence a core member. Outside the finite-branching setting, the complement of the core need not include every nonlive state; the preceding infinitely branching example explains why.

With finite branching, `height` is a natural-valued rank on this subtype. Its value is the attained maximum number of remaining matching edges; a terminal state has height zero. `survives_iff_le_height` identifies all finite survival stages exactly, so a mortal state of height `h` first fails at round `h+1`. `height_least` establishes pointwise minimality among natural-valued, strictly decreasing certificates on the mortal region. It does not claim minimality among arbitrary biological complexity measures or provide a ranking of the whole graph when live states exist.

`matching_state_dichotomy` applies to every reachable state even if the graph realizes the target elsewhere. Its disjunction says either an infinite continuation exists or an attained finite maximum exists. The alternatives are mathematically exclusive because a live state survives all finite rounds, although exclusivity is not a separately selected endpoint. The constructions are noncomputable and use classical choice; the statements do not supply a terminating decision procedure for membership in the live core.

## Reviewed source identities

| File | SHA-256 |
|---|---|
| `../formal/GenericPruning.lean` | `46425EE10A089DD24529631C531B04F36AD1CDC7B72E4C8380C0AFA62FE6FEE4` |
| `../formal/GenericMortalRank.lean` | `227B2CFCD452A5F75674FF0F835F9814818F70F3401DD440FA220A3F0C822F9B` |
| Imported `../formal/GenericCertificate.lean` | `F3B1FBFB72D2E7E08B94FF88279432B809747321E0003EE687C04F6307ED5581` |

These are local task extensions, not statements attributed to the older public PR-6 checkpoint in the source evidence map.
