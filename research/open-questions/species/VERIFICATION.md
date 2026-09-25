# Founder-window supporting lemmas: verification receipt

Date: 2026-09-25. Scope: reuse of the original successful isolated Lean check. No additional proof checks were run to prepare this receipt.

## Verified artifact

- File: [FounderWindow.lean](FounderWindow.lean).
- SHA-256: `75ef5ebd9b1feb0751b047f5fe30cb2532da30be96dcf4dee3941408ae4d4ae3`.
- The public copy and the originally checked file have identical SHA-256 hashes.
- Compiler toolchain: `leanprover/lean4:v4.33.1` (Lean 4.33.1).
- Original compiler command: `lean +leanprover/lean4:v4.33.1 FounderWindow.lean`.
- Original process exit code: **0**.
- Imports: the owner's already compiled `SamuelAlexanderResearch.SpeciesBridge` module. The owner checkout was neither modified nor rebuilt for this check.

## Seven supporting lemmas compiled

All names are in namespace `FounderWindowResearch`.

| Exact theorem name | Compiled statement |
|---|---|
| `FounderWindowResearch.founder_covers` | Every member of a set has an internal founder above it under strict natural birth order. |
| `FounderWindowResearch.founder_restrict` | A founder of a larger set remains a founder in every smaller set containing it. |
| `FounderWindowResearch.window_finite_founders` | A bounded founding window implies finitely many founders. |
| `FounderWindowResearch.commonAncestor_window` | Common ancestry implies every nonnegative natural founding window. |
| `FounderWindowResearch.nonempty_has_minimum` | Every nonempty set of natural birth ranks has a minimum. |
| `FounderWindowResearch.window_directed_union` | A fixed founding window survives every nonempty directed union. |
| `FounderWindowResearch.directed_union_finite_founders` | Such a directed union has finitely many founders. |

The helper `FounderWindowResearch.descendant_strict` also compiles in this file.

## Axiom output retained from the original successful run

That run explicitly printed the following four endpoint axiom lists. It did not print separate lists for the other three supporting lemmas, so no such individual output is claimed here.

```text
'FounderWindowResearch.founder_covers' depends on axioms: [propext, Classical.choice, Quot.sound]
'FounderWindowResearch.commonAncestor_window' depends on axioms: [propext, Quot.sound]
'FounderWindowResearch.window_directed_union' depends on axioms: [propext, Classical.choice, Quot.sound]
'FounderWindowResearch.directed_union_finite_founders' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx` occurred in these printed lists. The printed endpoints depend on the supporting lemmas used in their proofs; the file passed compilation in its entirety.

## Mathematical scope

These checks cover natural birth ranks and natural window widths. The full existence theorem in [FOUNDER-WINDOW-THEOREM.md](FOUNDER-WINDOW-THEOREM.md) is a written proof. Its real-date formulation, finite-founder Koenig argument, IAP closure lemma, and Zorn application have not been certified by this Lean file. The verification does not establish independent review, biological plausibility, or literature priority.

## Public Markdown formatting

The existing `checks/check_math_format.py` was run on the public theorem note alone. It returned exit code 0 with one file checked, **208 protected inline expressions**, **6 fenced math displays**, and **0 errors**. This checks Markdown delimiter conventions; it is not a mathematical proof or full TeX-renderer check.
