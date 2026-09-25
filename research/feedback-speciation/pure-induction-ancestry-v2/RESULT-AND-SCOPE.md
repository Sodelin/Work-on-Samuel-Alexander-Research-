# Checked pure-induction ancestry connection

25 September 2026. Local Lean checks passed for the bounded R1–R6 statement described here. This packet adds 36 selected endpoint reports across four new modules to the earlier checkpoints. Endpoint counts describe verification coverage, not novel discoveries.

The model has two adults per generation, one in each deme, two parental slots per child, and four independent uniform draws from Fin14 per generation. A draw selects a local parent with probability 6/7, the other parent with probability 1/7, and a homologue with probability 1/2. Marker inheritance and the parent graph use those same draws. Selected-state induction is the fixed pure-induction specialization of the existing finite model; only generation zero uses the separate marking pulse.

## What is now checked

| Obligation | Checked statements and their meaning |
|---|---|
| R1: raw sampling | PureInductionR1R2.raw_fibre_card and raw_event_card transport the uniform raw draws to the weighted parent/homologue records. PureInductionAncestry.raw_record_mass is the actual probability W(p)/38416. |
| R2: all finite transitions | PureInductionR1R2.ordinary_all_real and pulse_all_real prove all 81 ordinary and nine pulse entries. The off-support theorems assign zero frozen mass outside the nine-state embedding. |
| R3: actual paths | PureInductionPaths.countPath applies the pulse at transition zero and ordinary inheritance afterward. The measurable coupled map records both counts and parents. PureInductionAncestry.finite_path_frozen proves every finite admissible count path has the product of the frozen pulse/kernel probabilities. |
| R4: quantitative resolution | PureInductionAncestry.shared_avoidance_exact gives (2365/2401)^k. shared_history_exact and shared_conditional_exact include every event in the complete earlier raw history, with nonzero history mass required for division. resolution_bound and resolution_conditional_bound bound non-resolution by that quantity. |
| R5: actual-law IAP | PureInductionNoise.actual_parent_ae_iap proves whole-history Alexander IAP for the nonuniform parent schedule projected from this raw law. The proof uses recurrence of one specific positive-probability raw symbol and the existing deterministic bridge. |
| R6: exact comparison | PureInductionAncestry.marker_barrier_and_iap conjoins the frozen kernel's RI statistic 3/7, realization of its finite paths under the actual law, and almost-sure IAP of that law's parent graph. |

The selected statements, full source paths, hashes and axiom reports are in [COMBINED-RECEIPT.json](COMBINED-RECEIPT.json). The implementation is in [PureInductionAncestry.lean](PureInductionAncestry.lean), [PureInductionPaths.lean](PureInductionPaths.lean), [PureInductionNoise.lean](PureInductionNoise.lean) and [PureInductionR1R2.lean](PureInductionR1R2.lean).

## Why the probability bound is correct

There are 14^4 = 38416 equally likely raw records at one generation. Exactly 576 give the designated ordered common-parent table: slot zero selects parent zero and slot one selects parent one for every child. Its probability is 36/2401, so avoidance for k independent generations is (2365/2401)^k.

If an organism u was born strictly before generation a, one designated table at n in [a,a+k) makes u an ancestor of all or none of the next cohort. That status persists. Therefore non-resolution from generation a+k onward is contained in the avoidance event. The inequality does not assert that avoidance and non-resolution are the same event. k=0 is included and gives the bound by one.

The earlier-history event can constrain all raw records before a, so it can also constrain all counts and parents derived from that prefix. The future-window independence proof does not assume successive marker counts are independent.

PureInductionPaths.unresolved_measurable proves that the resolution event is measurable: strict ancestry is a countable union of explicitly nonempty finite paths, and all/none ancestry from a given generation is a countable intersection. The normalized intersection bounds therefore concern measurable events; they need not be interpreted merely as outer-measure ratios.

For almost-sure IAP, a single raw symbol with probability 1/38416 suffices. It recurs arbitrarily late and always projects to the common-parent table. This qualitative route does not supply the sharper rate on its own; the separate 576-record proof supplies the rate above. The deterministic graph model verifies finite earlier cohorts, occupied generations, one-generation edges and parent coverage. IAP uses strict descendants and the finite/cofinite alternative.

## Exact scope of the comparison

The RI number is the existing finite kernel statistic 1 - 8 times its fixationValue. Its earlier finite-distribution fixation-limit theorem is retained in FiniteEpigenetic. This new result formally realizes every finite count history of that kernel and proves actual-law IAP.

This packet does not separately define an eventual-fixation event on raw infinite streams and prove its measure equals fixationValue. Do not describe the R6 conjunction as that additional event-transfer theorem. The conjunction is the bounded comparison above; there is no claim that a kernel statistic by itself proves permanent genealogical separation.

There is no empirical species classification, DNA-only species theorem, human cultural speciation claim, general adaptive-law result, Knight–Darwin theorem under unstated extra hypotheses, or completion of Wong in this packet. The separate same-observation IAP/non-IAP obstruction and the four-state ancestry-indicator formulas remain deferred and are not counted.

The contribution's priority is unestablished. The existing evidence task has verified prior theoretical work on timing-sensitive plasticity/epigenetic models and normalized marker fixation. The present claim is the precise specified model and formal connection, not novelty of those general ideas.

## Verification and preservation

The four new modules compiled against Lean 4.33.1 and Mathlib 0df444a360eaa60ab8c11dca51a86af692955474. All 36 selected axiom reports contain only propext, Classical.choice and Quot.sound. No admitted proof occurs in those reports. A harmless deprecated-lemma warning remains in the final module; the checked bytes are preserved.

The new sources were checked locally against previously checked local dependency objects. This packet contains all 13 custom source modules for independent replay; it does not ship compiled objects. A fresh complete replay or clean-machine download was not run during packaging. Reusing checked work avoided a second local compilation of the old dependency stack.

[REPRODUCTION.md](REPRODUCTION.md) gives integrity checks and a serialized fresh-replay route. The earlier 34-endpoint comparison and four-endpoint finite checkpoint remain unchanged. Their historical status is not overwritten by this continuation. A few preserved source comments describe the draft state before checking; this dated result, the successful logs and their source hashes identify the checked snapshot.

Independent review examined the coupling, indexing, history quantifiers, IAP scope and comparison. Its two concrete scope findings led to the new measurability theorem and the explicit R6 qualification above. Publication and researcher correspondence remain with the main coordinator.
