Run from the isolated repository root, with exclusive access to the shared
continuation compiler slot:

```powershell
python research\wong\continuation-2026-09-27\check.py WongPedigreeBridge
```

The checked-in verifier uses Lean 4.33.1 and rejects a mismatch in the pinned
mathlib revision `0df444a360eaa60ab8c11dca51a86af692955474`. It rebuilds the local
project import closure and reuses an object only when its source and dependency
hashes match. This avoids treating older project object files as proof of the
new source.

Inspect both the exit status and
`.local-build/wong-continuation/WongPedigreeBridge.log`. The module prints axiom
dependencies for these 14 acceptance endpoints:

1. `WongPedigreeBridge.finiteSupport_preimage_iff`
2. `WongPedigreeBridge.infiniteSupport_preimage_iff`
3. `WongPedigreeBridge.iap_iff`
4. `WongPedigreeBridge.reflection_iff`
5. `WongPedigreeBridge.commonAncestor_descends`
6. `WongPedigreeBridge.convex_pullback`
7. `WongPedigreeBridge.convex_iff`
8. `WongPedigreeBridge.specieslike_descends`
9. `WongPedigreeBridge.specieslike_iff`
10. `WongPedigreeBridge.maximal_saturated_iff`
11. `WongPedigreeBridge.maximalSpecieslike_descends`
12. `WongPedigreeBridge.iap_iff_of_finite_ancestry_errors`
13. `WongPedigreeBridge.sound_projection_does_not_determine_iap`
14. `WongPedigreeBridge.no_specieslike_recovery_from_garg_coarsening`

Admissible standard dependencies are `propext`, `Classical.choice`, and
`Quot.sound`. A source draft, a zero exit status from a different checkout, or an
old receipt does not establish this module at the integrated commit. The parent
lane will register the accepted module and rerun the combined verification at
the final exact commit. `CHECKPOINT.md` records the successful serialized run
and the remaining integrated-commit check.

To check that the preserved evidence still corresponds to the source and all
34 project files in its recorded import closure, without starting Lean:

```powershell
python -X utf8 research\wong\continuation-2026-09-27\bridge\check_evidence.py
```

This validates the complete list of 14 printed endpoints, their allowed axioms,
the source and log hashes, and the successful closure receipt. It writes
`verification/RESULT.json` with status
`PASS_SOURCE_SNAPSHOT_PENDING_INTEGRATED_COMMIT`.
