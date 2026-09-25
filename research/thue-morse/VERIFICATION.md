# Historical interval-stage verification receipt

This receipt preserves the initial interval/coalescence theorem and checker
stage. At that stage the sharp claims had not yet been proved. They are
now fully Lean checked, including actual bits, dyadic runs, the original
edge bridge, finite maxima, and the exact equality set. Current integrated
verification is in
[`FORMALIZATION-RECEIPT.md`](../../verification/FORMALIZATION-RECEIPT.md)
and the [final source-hashed audit](../../verification/formal-audit.json):
the expanded core build and optional real project now have their own audited endpoints. The exact first-hit formula and real-coefficient optimality are checked in their separate modules.
The commands and output below are retained as a historical receipt for
the earlier, smaller proof stage.

Working directory:
`C:\Users\Owner\Documents\Codex\2026-09-24\alexander-formalization`

## Lean command and result

```powershell
$env:ELAN_HOME = 'C:\Users\Owner\.elan'
& 'C:\Users\Owner\.elan\bin\lean.exe' --version
& 'C:\Users\Owner\.elan\bin\lean.exe' 'lean\SamuelAlexanderResearch\ThueMorseBound.lean'
```

The version command returned:

```text
Lean (version 4.33.1, x86_64-w64-windows-gnu, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6, Release)
```

The initial direct module check exited 0 without warnings. Its axiom output:

```text
'SamuelAlexanderResearch.ThueMorseBound.interval_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'SamuelAlexanderResearch.ThueMorseBound.reachable_iff_interval' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SamuelAlexanderResearch.ThueMorseBound.coalescence_persists' does not depend on any axioms
'SamuelAlexanderResearch.ThueMorseBound.maximum_length_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The file has no admitted declaration, `sorry`, custom `axiom`, or
`native_decide`. It imports only `Std`. The direct command above checked
the complete interval module. That module has since been imported into
the successful default build alongside the full sharp proof.

## Independent diagnostic command and result

```powershell
python research/thue-morse/interval_check.py --output research/thue-morse/check-results.json
```

Exit code: 0. The persisted result reports:

- 8,191 exact-length agreements with the existing set-frontier output,
  covering starts 1 through 8,191.
- 1,632 complete-frontier agreements with direct edge expansion for small
  starts, including empty frontiers after extinction.
- 8,192 finite checks of the two-bit substitution formula.

The implementation uses the prior proved quadratic stopping guard and
does not assume the linear bound. The initial stage left the sharp-bound
question unresolved; that is historical context, not the current theorem
status. The current interval output describes itself as finite
corroboration of the separately proved sharp result.

## Subsequent sharp-proof diagnostic

The current small reproduction command is:

```powershell
python research/thue-morse/sharp_check.py --output research/thue-morse/sharp-check-results.json
```

It exits 0: 18 complete trajectories, 8,140 advance comparisons, and 256
bounded `H(v)` checks pass, along with the inequality and exact equality
set in the saved scan. These finite diagnostics do not replace the
universal Lean proofs in the current integrated receipt.

## Initial-stage scope preserved

Only these owned paths were created during the initial interval stage:

- `lean/SamuelAlexanderResearch/ThueMorseBound.lean`
- `research/thue-morse/INTERVAL-REDUCTION.md`
- `research/thue-morse/interval_check.py`
- `research/thue-morse/check-results.json`
- `research/thue-morse/VERIFICATION.md`

Existing checks, shared notes, default imports, lake configuration, and Git
refs were not modified by that initial work lane. Later integration and
sharp-theorem work have their own current receipts linked above.
