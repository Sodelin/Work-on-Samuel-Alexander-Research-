# Finite-edit stability in the actual target-dependent graphs

The checked module is [`FiniteEditStability.lean`](../lean/SamuelAlexanderResearch/FiniteEditStability.lean). It proves finite matching-path transport and quantitative upper/lower witnesses directly for `BinaryAvoidance.Edge`. It does not assume a transport property, a maximum-length estimate, or the existence of long matches as a model premise.

## Exact finite-edit statement

`AgreeFrom s t m` means `s k = t k` for every `k ≥ m`. Thus only the first `m` positions may change. The parameter is a bound on the edited prefix, not the number of altered bits at arbitrary positions.

`QuantitativeAvoidance.MatchesPrefix s path ell` requires every one of the first `ell` edges of the actual path function to be an edge of `P_s` carrying the corresponding symbol `s k`. It imposes no condition on the function after that finite prefix.

`finite_edit_transport` proves that, given any such prefix in `P_s`, there is a path `changed` in `P_t` satisfying all of:

- `MatchesPrefix t changed ell`: the same finite number of edges is matched.
- `changed 0 ≤ path 0 + m` and `path 0 ≤ changed 0 + m`: the two starting vertices differ by at most `m`.
- `changed k = path k` for every `k ≥ min m ell`: the suffix, including the splice vertex, is preserved exactly.

The result holds for arbitrary Boolean sequences, every `m`, and every finite length, including zero. Its symmetric version follows by reversing the pointwise agreement hypothesis and applying the same theorem; no aperiodicity assumption is used.

## Why the splice is valid

`prefix_lower_bound` proves the finite own-target offset invariant `2*k ≤ path k` for every `k ≤ ell`. This is proved from the actual edge labels. In particular, an attempted one-step edge from `2*k` to `2*k+1` would have label opposite to `s k` and is impossible. `prefix_displacement` separately proves `path 0 + k ≤ path k ≤ path 0 + 2*k` from the one-or-two-step geometry.

At `r = min m ell`, let `w = path r`. The invariant gives `w ≥ 2*r`. `backward_prefix` constructs the first `r` target symbols of `t` backward from `w`, choosing an actual parent of the needed label at each step. Every backward destination is at least two, so this never assumes the missing edge `0 → 1` or invents a parent of a root. The rebuilt prefix start `u` obeys `u+r ≤ w ≤ u+2*r`. Comparing this with the old prefix's displacement gives both start-distance inequalities.

If the suffix is nonempty, every suffix time is at least `m`, and its destinations are at least `2*m`. `row_eq_of_agree` then proves equality of the actual row colors because `row s w` depends on `s (w/2)`. `tail_edge_transfer` preserves both the edge row color and the required target symbol. `splice_prefix` joins the rebuilt front and the unchanged, correctly phased suffix. If `ell < m`, the suffix contains no required edges and the entire finite match is rebuilt safely.

## Thue-Morse endpoints

Here `t` is the actual checked sequence `ThueMorseBits.t`, not an abstract sequence supplied with a sharp bound.

- `reachable_thue_prefix` converts the existing interval model's `Reachable t t` proof into an actual path function and `MatchesPrefix t`. `sharp_family_prefix` uses the checked sharp equality theorem to produce an actual match of length `8*2^n-3` starting at `3*2^n-1`.
- `thue_zero_maximum` proves that the original Thue-Morse graph has maximum matching length exactly one from vertex zero. It includes the one-edge witness `0 → 2` and rules out all longer prefixes. This handles the possibility that transport from a positive edited-graph start reaches zero.
- `finite_edit_thue_upper` proves, for every actual finite matching prefix in `P_s` with `path 0 ≥ 1`,

  ```lean
  3*ell ≤ 8*path 0 + 8*m - 1
  ```

- `HasPrefix s v ell` is existence of an actual matching path function with start `v`. `IsMaximumPrefix s v ell` requires such a witness and bounds **every** other witnessed finite length by `ell`. `finite_edit_thue_maximum` proves that every positive start has such a genuine finite maximum and that the maximum satisfies the same integral inequality. Maximum existence is obtained by a finite bounded search argument, not left as a premise.
- `finite_edit_thue_lower` transports the checked dyadic witnesses back to `P_s`. Whenever `m < 3*2^n-1`, it produces a positive-start actual matching path of length `8*2^n-3`, with its start within `m` of `3*2^n-1`, and proves

  ```lean
  8*path 0 ≤ 3*(8*2^n-3) + 8*m + 1
  ```

- `finite_edit_thue_lower_above` proves these actual near-sharp witnesses occur above every requested starting-vertex bound. It chooses a sufficiently large dyadic scale internally.

These are integer statements about original-graph finite paths and their actual maxima. Together they supply the upper estimate and arbitrarily late lower witnesses needed for the real coefficient `8/3` interpretation. The real-number and limit translation is handled separately; no analytic limit theorem is claimed inside this Std-only module. The transported lower witnesses need not remain exact maximizers after editing.

The generic finite path lower bound, displacement bound, backward construction, splicing lemma, and sharp-family extraction are also the shared proved helpers used by the independent `PhaseShift.lean` module. There is no circular dependency: finite-edit stability imports the existing sharp theorem, and phase shift imports these finite-edit helpers.

## Verification and provenance

From the repository root, using the existing Lean 4.33.1 toolchain:

```powershell
$env:ELAN_HOME = 'C:\Users\Owner\.elan'
& 'C:\Users\Owner\.elan\bin\lake.exe' env lean lean/SamuelAlexanderResearch/FiniteEditStability.lean
& 'C:\Users\Owner\.elan\bin\lake.exe' build SamuelAlexanderResearch.FiniteEditStability
```

Both checks pass without warnings. The module contains no `sorry`, `admit`, new axiom, or `native_decide`. Printed endpoints use only `propext`, `Classical.choice`, and `Quot.sound`; the finite offset/splicing lemmas and zero-start maximum avoid `Classical.choice`.

The specific row-colored +1/+2 population construction comes from the [September 2026 classification manuscript, Section 2](https://github.com/avg-netizen/biological-unavoidability/blob/3d6175e3e23f67bd68e7be591b5a9a6d04e496a3/paper.md#2-an-explicit-binary-avoiding-population), as recorded in `BinaryAvoidance.lean`. Alexander's earlier paper supplies the broader population and positive-unavoidability background. The finite-edit transport and its quantitative corollaries are repository deductions. This note does not attribute those deductions to a source theorem or assert literature-wide novelty.
