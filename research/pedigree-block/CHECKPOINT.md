# Finite-family proof checkpoint

The base is `a096e498045a07d867f1a2201870596fbfaad68a`, whose ARG proof sources were verified at `1ac3dd9446e7264336f0764040ff47ad684099cb`. This separate worktree is `codex/pedigree-block-recovery-2026-09-27`. Original ARG sources and source-family ledger are preserved. Shared registration, this packet and the compiler-lock override belong to the coordinating lane.

## Acceptance gate

The new target is the exact probability that the connected-component relation of the observed symbol-sharing graph equals the true sampled-family partition, for every finite collection of nonempty families and every positive number of independent blocks. The relation is computed from symbols; hidden family labels occur in its correctness criterion. Singletons and empty collections of families are included by the finite product convention.

Acceptance requires the whole new import closure to compile, selected axiom reports to contain only the three standard allowed axioms, an independent statement review, and a clean exact proof commit. The exact accepted result is recorded in `verification/RESULT.json`; isolated development receipts are not substitutes for that gate.

The compiler is shared with the separate time/self-reference research. Set `WONG_COMPILER_LOCK` to the original ARG checkout's `.local-build/wong-continuation/compiler.lock`, then use the checked script `research/wong/continuation-2026-09-27/check.py`. Never bypass the lock or reuse an object whose source/dependency/toolchain/log hash no longer matches.

## Endpoints and source boundary

- Graph: `not_connected_iff_bad` and `connected_of_restrict`.
- Probability: the explicit `badEquiv`, exact `bad_probability`, coordinate factorization `config_bit_cylinder`, and independent `families_good_probability`.
- Observation: `recovered_iff_connected`, justified by injective parent-symbol assignments and family-preserving paths.
- Recovery: `recovered_probability` and `output_recovery_probability`, with an actual observed-symbol pushforward law.
- Dependence: `repeatedLaw_block_marginal` and `repeatedLaw_connected_probability`, retaining each complete one-block marginal while eliminating improvement with the number of repeated blocks.

These specialize an explicit first-generation founder model. The source's full multigeneration theorem and asymptotic parameter regime are not asserted. Its conventional proof has not been converted merely by compiling this specialization. The bounded public formalization search is preserved under `source/` and is not a priority claim.

## Research value and stopping condition

This is a positive finite-observation control and an explicit dependence obstruction, with no novelty claim. Close its acceptance gate and retain it as a reusable formal result. A separate discovery track should investigate stronger ARG-to-organism maps and genuine information-loss examples; this lane will not duplicate the independently owned owner-assignment investigation. Valuable known-result formalization remains legitimate when it has a concrete purpose. Distinguish known mathematics formalized, new results supported by a prior-work check, and speculative ideas. Do not infer publication authorization from this direction.

## Still unproved or deliberately outside this formal gate

1. The written pair-event argument separates distributions of different family partitions. Its general pair-event mass and distribution-injectivity statements are not yet Lean endpoints in this packet. A short route is to count configurations with two specified child vectors complementary, use uniform coordinate marginals, and lift the positive/zero pair-sharing probabilities to partition-law separation.
2. The written observation-error coupling bound is not yet a Lean endpoint. Its route is to intersect ideal recovery with graph agreement and apply the union bound, with the same labeled children and target family partition on both sides.
3. There is no construction deriving the independent founder-block observation law from the continuous marked ARG law. A coupling or a quantified approximation law is needed before using the recovery formula for that process.
4. No mutation, sequencing error, shared-parent families, linked-block approximation, historical-sample model, or ordinary diploid phasing inference is supplied. Each would change the observation model and its proof obligations.
5. Finite family recovery does not determine infinite IAP, ancestry convexity, specieslike maximality, or biological species. Earlier owner-map conditions and infinite-completion counterexamples remain applicable.
6. The Lean graph estimator is defined mathematically through reachability. The Python component checker has finite controls; a verified executable implementation and complexity bound are separate tasks.

All tasks and their histories remain visible and unarchived. No source upload, publication, pull-request creation or merge is implied by this local proof checkpoint.
