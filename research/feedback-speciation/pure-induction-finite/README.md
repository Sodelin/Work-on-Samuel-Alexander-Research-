# A finite parent/marker checkpoint for the Alexander connection

**Verified status: four selected finite statements compiled in Lean 4.33.1 and passed an independent source-and-scope audit. The infinite ancestry theorem is not yet formalized.**

This packet records a small, exact part of a proposed connection between a finite epigenetic marker model and Samuel Allen Alexander's ancestry framework. It provides the checked source, its two local source dependencies, the original logs and receipts, the independent review, and pinned reproduction instructions.

The introductory comment in [PureInductionJoint.lean](PureInductionJoint.lean) still calls the file uncompiled. That comment predates the successful check. We preserve the checked source byte-for-byte; the actual status is recorded in the [worker receipt](verification/worker-receipt.json) and [independent audit](verification/independent-scope-audit.json).

## What the finite model means

There are two demes, each containing one diploid adult per generation. Each offspring independently samples two parent/gamete slots; selfing is allowed. A local parent has probability 6/7 and a foreign parent 1/7. A sampled homologue determines the neutral B marker. After reproduction, environmental induction resets the selected state to EE in deme 0 and ee in deme 1.

The state (b0,b1) records zero, one or two B copies in each adult. It embeds in the earlier 81-state model as 54+9*b0+b1. An explicit first-step pulse marks foreign gametes entering deme 1; it preserves parent identity and is distinct from ordinary inheritance. These assumptions specialize the earlier finite model at migration 1/4, selection 1/2, free recombination 1/2 and complete selected-state induction.

The intended random implementation has four uniform Fin14 draws. The checked finite representation groups these draws by parent identities and homologue choices, with local weight 6 and foreign weight 1. The full proof connecting those raw draws to the grouped representation remains R1 below.

## The four selected results

| Lean endpoint in PureInductionJoint | Meaning |
|---|---|
| joint_total | The total weight of all 256 parent/homologue records is 38416. |
| designated_probability | The ordered event in which both children use adult 0 in slot 0 and adult 1 in slot 1 has mass 36/2401. |
| ordinary_01_22_frozen_real | The grouped count transition (0,1) to (2,2), of mass 9/9604, equals the imported frozen kernel entry at states 55 and 74. |
| pulse_00_01_frozen_real | The first-step transition (0,0) to (0,1), of mass 12/49, equals the imported frozen pulse entry at state 55. |

There are additional helper declarations in the file. Four is the number of selected audited endpoints, not the total declaration count or a percentage of a paper. The local source dependencies have their own earlier 21-endpoint receipt; those results are not counted as new here.

Each selected result has the printed axiom set {propext, Classical.choice, Quot.sound}. The finite computations use decide +kernel. The [saved log](verification/PureInductionJoint.log) is unchanged.

## What remains to complete the proposed ancestry connection

1. **R1: Raw-noise transport.** Prove the four-slot fibre and pushforward formula.
2. **R2: Full marginals.** Prove all 81 ordinary and nine pulse identities, with support closure.
3. **R3: Actual paths.** Construct the joint infinite noise, parent and recursive count process and prove its finite-path correspondence.
4. **R4: Resolution bound.** Prove the conditional finite-window synchronization bound, with correct strict-ancestry indexing.
5. **R5: Alexander IAP.** Transfer almost-sure recurrent synchronization to the finite/cofinite strict-descendant condition on the actual parent graph.
6. **R6: Exact comparison.** Combine that result with the earlier marker RI=3/7 statement at the same model assumptions.

[The full audit and remaining obligations](CHECKPOINT-AND-REMAINING-OBLIGATIONS.md) state the dependencies and finish criterion. The motivation is to distinguish a marker barrier from permanent genealogical splitting. This packet does not establish the infinite-law conclusion, a general species criterion, an empirical speciation event, or completion of Wong's paper. No cultural mechanism or claim that DNA uniquely determines species is included.

## Read and reproduce

- [Reproduction instructions](REPRODUCTION.md): exact original command, portable replay route and limitations.
- [Dependency pins](DEPENDENCIES.json) and [Lake lockfile](lake-manifest.json): Lean 4.33.1 and nine pinned Git packages.
- [Provenance](PROVENANCE.json): original artifact hashes and the one documented editorial transformation.
- [Packet manifest](MANIFEST.json): every shipped file's byte length and SHA256.
- [Packet verifier](verify_packet.py): checks file integrity and saved proof reports without invoking Lean.
- [Portable check script](Check.ps1): integrity-only by default; an explicit -Run rebuilds in a new .replay directory.

The publication packaging introduced no compiler run. Its portable Lake/replay setup has been statically checked but has not been executed against a fresh dependency download. Original local compilation and independent semantic review are the verification evidence currently supplied. This packet is ready for the coordinator's publication review; it is not external peer-review endorsement.

## Research sources

The motivating model is Planidin et al. (2025), [Adaptive epigenetic divergence can facilitate ecological speciation](https://doi.org/10.1098/rspb.2025.1217). The finite count specialization and its model-to-source limitations are documented in the [earlier frozen comparison release](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/4fd6f7cc89fda47f245e9ae28fca140fd04de783/research/feedback-speciation/finite-epigenetic/README.md).

The intended ancestry target uses Alexander's strict-descendant definitions in [Specieslike clusters based on identical ancestor points](https://arxiv.org/abs/2602.05274). This finite checkpoint does not claim a new solution to a named open problem or verified publication priority.
