import WeightedCoefficients
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
Circular reconstruction is proved for arbitrary symmetric zero-diagonal rational
matrices. In particular no triangle inequality is assumed of an anchor matrix.
-/

namespace Nanuq.Reconstruction

open scoped BigOperators
open Nanuq.Weighted

variable {n : Nat}

def cut (i x : Fin n) : ℚ := if i < x then 1 else 0

/-- Membership in the circular interval (i,j], for i<j in the chosen numbering. -/
def inArc (i j x : Fin n) : Prop := i < x ∧ x ≤ j

instance (i j x : Fin n) : Decidable (inArc i j x) := inferInstanceAs (Decidable (i < x ∧ x ≤ j))

/-- Squared indicator difference, defined symmetrically in the two gaps. -/
def gapSplit (i j x y : Fin n) : ℚ :=
  ((cut i x - cut j x) - (cut i y - cut j y)) ^ 2

theorem gapSplit_symm_gaps (i j x y : Fin n) :
    gapSplit i j x y = gapSplit j i x y := by
  unfold gapSplit
  ring

@[simp] theorem gapSplit_same_gap (i x y : Fin n) : gapSplit i i x y = 0 := by
  simp [gapSplit]

theorem cut_sub_eq_arc (i j x : Fin n) (hij : i < j) :
    cut i x - cut j x = if inArc i j x then 1 else 0 := by
  unfold cut inArc
  split_ifs <;> simp_all <;> omega

/-- Thus the reconstruction's summands are precisely ordinary split distances. -/
theorem gapSplit_eq_separation (i j x y : Fin n) (hij : i < j) :
    gapSplit i j x y = if (inArc i j x ↔ inArc i j y) then 0 else 1 := by
  rw [gapSplit, cut_sub_eq_arc i j x hij, cut_sub_eq_arc i j y hij]
  by_cases hx : inArc i j x <;> by_cases hy : inArc i j y <;> simp [hx, hy]

theorem cyclicNext_injective : Function.Injective (@cyclicNext n) := by
  intro i j hij
  have heq := congrArg Fin.val hij
  simp only [cyclicNext] at heq
  have hi := i.isLt
  have hj := j.isLt
  apply Fin.ext
  by_cases hi' : i.val + 1 < n
  · rw [Nat.mod_eq_of_lt hi'] at heq
    by_cases hj' : j.val + 1 < n
    · rw [Nat.mod_eq_of_lt hj'] at heq
      omega
    · have hjn : j.val + 1 = n := by omega
      rw [hjn, Nat.mod_self] at heq
      omega
  · have hin : i.val + 1 = n := by omega
    rw [hin, Nat.mod_self] at heq
    by_cases hj' : j.val + 1 < n
    · rw [Nat.mod_eq_of_lt hj'] at heq
      omega
    · have hjn : j.val + 1 = n := by omega
      omega

theorem sum_cyclicNext (f : Fin n → ℚ) : (∑ i, f (cyclicNext i)) = ∑ i, f i := by
  exact Equiv.sum_comp (Equiv.ofBijective cyclicNext
    ⟨cyclicNext_injective, Finite.surjective_of_injective cyclicNext_injective⟩) f

theorem sum_difference_zero (f : Fin n → ℚ) :
    (∑ i, (f i - f (cyclicNext i))) = 0 := by
  rw [Finset.sum_sub_distrib, sum_cyclicNext, sub_self]

theorem cyclicNext_castSucc {k : Nat} (i : Fin k) :
    cyclicNext i.castSucc = i.succ := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt (Nat.succ_lt_succ i.isLt)

/-- Discrete integration by parts for the cut indicators. -/
theorem sum_difference_cut {k : Nat} (f : Fin (k+1) → ℚ) (x : Fin (k+1)) :
    (∑ i, (f i - f (cyclicNext i)) * cut i x) = f 0 - f x := by
  induction x using Fin.induction with
  | zero => simp [cut]
  | succ j ih =>
    have hstep : ∀ i : Fin (k+1),
        (f i - f (cyclicNext i)) * cut i j.succ =
          (f i - f (cyclicNext i)) * cut i j.castSucc +
            if i = j.castSucc then f i - f (cyclicNext i) else 0 := by
      intro i
      unfold cut
      by_cases h1 : i < j.castSucc
      · have h2 : i < j.succ := by exact lt_trans h1 Fin.castSucc_lt_succ
        have h3 : i ≠ j.castSucc := ne_of_lt h1
        simp [h1, h2, h3]
      · by_cases heq : i = j.castSucc
        · subst i
          simp
        · have h2 : ¬ i < j.succ := by
            simp only [Fin.lt_def, Fin.val_succ, Fin.val_castSucc] at *
            have hi_ne : i.val ≠ j.val := by
              intro h
              exact heq (Fin.ext h)
            omega
          simp [h1, h2, heq]
    simp_rw [hstep]
    rw [Finset.sum_add_distrib, ih]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, cyclicNext_castSucc]
    ring

theorem sum_difference_cut_difference (f : Fin n → ℚ) (x y : Fin n) :
    (∑ i, (f i - f (cyclicNext i)) * (cut i x - cut i y)) = f y - f x := by
  cases n with
  | zero => exact Fin.elim0 x
  | succ k =>
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, sum_difference_cut, sum_difference_cut]
    ring

theorem alpha_symmetric (d : Matrix n) (hsym : ∀ x y, d x y = d y x)
    (i j : Fin n) : circularAlpha d i j = circularAlpha d j i := by
  unfold circularAlpha
  rw [hsym i j, hsym (cyclicNext i) (cyclicNext j), hsym i (cyclicNext j),
    hsym (cyclicNext i) j]
  ring

theorem alpha_row_sum_zero (d : Matrix n) (i : Fin n) :
    (∑ j, circularAlpha d i j) = 0 := by
  simp only [circularAlpha, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    sum_cyclicNext]
  ring

theorem alpha_col_sum_zero (d : Matrix n) (j : Fin n) :
    (∑ i, circularAlpha d i j) = 0 := by
  simp only [circularAlpha, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [sum_cyclicNext (fun i => d i (cyclicNext j)), sum_cyclicNext (fun i => d i j)]
  ring

theorem alpha_cut_sum (d : Matrix n) (i x y : Fin n) :
    (∑ j, circularAlpha d i j * (cut j x - cut j y)) =
      (d i y - d i x) - (d (cyclicNext i) y - d (cyclicNext i) x) := by
  have heq : ∀ j, circularAlpha d i j =
      (d i j - d i (cyclicNext j)) -
        (d (cyclicNext i) j - d (cyclicNext i) (cyclicNext j)) := by
    intro j
    unfold circularAlpha
    ring
  calc
    _ = (∑ j, (d i j - d i (cyclicNext j)) * (cut j x - cut j y)) -
        ∑ j, (d (cyclicNext i) j - d (cyclicNext i) (cyclicNext j)) *
          (cut j x - cut j y) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      rw [heq]
      ring
    _ = _ := by
      rw [sum_difference_cut_difference, sum_difference_cut_difference]

theorem alpha_bilinear_cut (d : Matrix n) (x y : Fin n) :
    (∑ i, ∑ j, circularAlpha d i j * (cut i x - cut i y) * (cut j x - cut j y)) =
      d y y - d y x - (d x y - d x x) := by
  have heq : ∀ i j, circularAlpha d i j * (cut i x - cut i y) * (cut j x - cut j y) =
      (cut i x - cut i y) * (circularAlpha d i j * (cut j x - cut j y)) := by
    intro i j
    ring
  simp_rw [heq, ← Finset.mul_sum, alpha_cut_sum]
  have hf := sum_difference_cut_difference (fun i => d i y - d i x) x y
  simpa only [mul_comm] using hf

/-- Reconstruction with ordered gap pairs. Each actual split appears twice,
so its weight is alpha/2 even though this convenient double sum divides by 4. -/
theorem circular_reconstruction_ordered (d : Matrix n)
    (hsym : ∀ x y, d x y = d y x) (hdiag : ∀ x, d x x = 0) (x y : Fin n) :
    d x y = (∑ i, ∑ j, circularAlpha d i j * gapSplit i j x y) / 4 := by
  have hexpand : ∀ i j, circularAlpha d i j * gapSplit i j x y =
      circularAlpha d i j * (cut i x - cut i y)^2 +
      circularAlpha d i j * (cut j x - cut j y)^2 -
      2 * (circularAlpha d i j * (cut i x - cut i y) * (cut j x - cut j y)) := by
    intro i j
    unfold gapSplit
    ring
  have hrow : (∑ i, ∑ j, circularAlpha d i j * (cut i x - cut i y)^2) = 0 := by
    simp_rw [← Finset.sum_mul, alpha_row_sum_zero, zero_mul]
    simp
  have hcol : (∑ i, ∑ j, circularAlpha d i j * (cut j x - cut j y)^2) = 0 := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, alpha_col_sum_zero, zero_mul]
    simp
  simp_rw [hexpand, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hrow, hcol]
  simp_rw [← Finset.mul_sum]
  rw [alpha_bilinear_cut, hdiag x, hdiag y, hsym y x]
  ring

#print axioms gapSplit_eq_separation
#print axioms circular_reconstruction_ordered

end Nanuq.Reconstruction
