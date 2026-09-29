# Finite checkpoint audit and remaining Alexander obligations

25 September 2026. **Four selected finite endpoints compiled; independent semantic and artifact review passed. Infinite ancestry conclusion remains unformalized.**

Sol2 compiled [PureInductionJoint.lean](PureInductionJoint.lean) with Lean 4.33.1, exit 0 according to [CHECK-RECEIPT.json](verification/worker-receipt.json). The Alexander lead independently read the final definitions, imported kernel/pulse, and four axiom reports; recomputed source/object/log/receipt hashes; and verified the four frozen source files against both manifest and receipt and their cached objects against that receipt. This was not a second compiler run. [Independent audit](verification/independent-scope-audit.json).

## Four selected statements

| Endpoint in PureInductionJoint | Checked result |
|---|---|
| joint_total | Weights over 16 parent tables and 16 homologue tables sum to 38416. |
| designated_probability | The ordered shared-parent event has numerator 576 and rational mass 36/2401. |
| ordinary_01_22_frozen_real | Compressed count mass from (0,1) to (2,2) equals the actual frozen real kernel entry at states 55 and 74. Its value is 9/9604. |
| pulse_00_01_frozen_real | Separate initialization mass from (0,0) to (0,1) equals the actual frozen pulse at state 55. Its value is 12/49. |

The embedding is 54+9*b0+b1, with EE in deme 0 and ee in deme 1. Local parent weight is 6, foreign weight 1, and homologue choice is uniform. Pulse marks foreign gametes into deme 1 while preserving parent identity; it is distinct from ordinary inheritance from bb adults.

All four printed axiom sets are exactly {propext, Classical.choice, Quot.sound}. Finite reductions use decide +kernel. No sorryAx or native_decide appears in reviewed source/log. The introductory source comment still says uncompiled; that comment is stale. The hashed source was preserved.

This is a normalized finite weighted representation and two count-entry correspondences. It does not yet construct the infinite probability law. The 34-endpoint released comparison packet remains separate and unchanged.

## Remaining obligations in dependency order

**R1 — Raw-noise transport.** For uniform U in (Fin2 -> Fin2 -> Fin14), prove that the fibre of each compressed record (p,h) has cardinal W(p). Checked one-slot counts 6 and 1 are ingredients, not the four-slot theorem. Deduce pushforward masses W(p)/38416 and transport the shared-parent event mass. A uniform distribution on parent tables would be the wrong law.

**R2 — Full marginals.** Prove all 81 ordinary identities on the nine-state embedding, no mass outside the embedded support, and all nine initial pulse identities. Only one ordinary and one pulse entry are checked in Lean. The existing exact Python audit of all entries is reference evidence, not their Lean proof.

**R3 — Actual paths.** Construct the countable product of the uniform raw-noise law and the recursively driven count process, with pulse only at index zero. Define the parent schedule from the same noises. Prove finite-path marginals agree with the frozen initialization and ordinary kernel. Parent tables are iid but nonuniform; count states are dependent. Marker-state independence of parents is specific to this pure-induction specialization.

**R4 — Resolution bound.** Prove avoidance of the designated table on n=a,...,a+k-1 has probability (2365/2401)^k and is independent of complete earlier history. For an organism born strictly before a, show an occurrence makes it ancestral to all or none of cohort a+k and preserves that status. Mixed-cohort probability is bounded by avoidance, not asserted equal to it. Handle k=0 and strict ancestry explicitly.

**R5 — Alexander IAP under this law.** Establish required measurable or outer-null statements; use the geometric bound and countable union for arbitrarily late designated tables; instantiate the existing ParentSchedules and ExtinctionPedigree deterministic bridge. Check finite earlier cohorts, nonempty cohorts, one-generation edges and parent coverage. The result is the strict finite/cofinite descendant alternative. Additional specieslike, common-ancestor, reflection and Knight-Darwin hypotheses do not follow automatically.

**R6 — Exact comparison.** Combine the released marker RI=3/7 with R1-R5: this fixed model has a positive marker barrier and whole-history IAP almost surely. Marker resistance and eventual genealogical splitting are different predicates. This does not prove DNA determines species, human cultures constitute biological species, or Wong completion.

A conservative route can reuse UniformParentProcess.ae_recurrent for the single raw symbol (0,6,6,0), whose avoidance is (38415/38416)^k. That can establish almost-sure recurrence after the deterministic projection is connected, but does not close the sharper 576-symbol bound in R4. Record that distinction if chosen first.

**Bounded finish criterion:** R1-R6 with checked statements, source mapping, actual-law scope and audited receipt. Passing the four finite endpoints alone does not meet it. Shared worker assignments and compiler scheduling remain with the coordinator.


The optional all-path obstruction and four-state arithmetic exploration are excluded from this bounded publication packet. Neither is claimed as a checked result here.
