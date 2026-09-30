import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.ByContra

/-!
Kernel-checked algebra used in the NANUQ weighted-blob argument.

This file proves preservation of nonnegative circular coefficients and their
positive support under positive finite combinations. The graph decomposition,
anchor formula, and finite theta-template audit are separate mathematical and
computational arguments; this is not a Lean formalization of the full conjecture.
-/

namespace NanuqPositiveCombination

variable {ι X : Type*} [Fintype ι]

def coefficient (d : X → X → ℝ) (a b c e : X) : ℝ :=
  d a c + d b e - d a e - d b c

def mixture (w : ι → ℝ) (d : ι → X → X → ℝ) : X → X → ℝ :=
  fun x y => ∑ i, w i * d i x y

theorem coefficient_mixture (w : ι → ℝ) (d : ι → X → X → ℝ)
    (a b c e : X) :
    coefficient (mixture w d) a b c e = ∑ i, w i * coefficient (d i) a b c e := by
  simp only [coefficient, mixture, mul_sub, mul_add,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]

theorem coefficient_mixture_nonneg (w : ι → ℝ) (d : ι → X → X → ℝ)
    (a b c e : X) (hw : ∀ i, 0 ≤ w i)
    (hd : ∀ i, 0 ≤ coefficient (d i) a b c e) :
    0 ≤ coefficient (mixture w d) a b c e := by
  rw [coefficient_mixture]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (hd i)

theorem coefficient_mixture_pos_iff (w : ι → ℝ) (d : ι → X → X → ℝ)
    (a b c e : X) (hw : ∀ i, 0 < w i)
    (hd : ∀ i, 0 ≤ coefficient (d i) a b c e) :
    0 < coefficient (mixture w d) a b c e ↔
      ∃ i, 0 < coefficient (d i) a b c e := by
  classical
  rw [coefficient_mixture]
  constructor
  · intro hpos
    by_contra! hnone
    have hnonpos : (∑ i, w i * coefficient (d i) a b c e) ≤ 0 :=
      Finset.sum_nonpos fun i _ => mul_nonpos_of_nonneg_of_nonpos (le_of_lt (hw i)) (hnone i)
    exact (not_lt_of_ge hnonpos) hpos
  · rintro ⟨i, hi⟩
    have hle : w i * coefficient (d i) a b c e ≤
        ∑ j, w j * coefficient (d j) a b c e :=
      Finset.single_le_sum (fun j _ => mul_nonneg (le_of_lt (hw j)) (hd j)) (Finset.mem_univ i)
    exact lt_of_lt_of_le (mul_pos (hw i) hi) hle

theorem positive_weights_preserve_support (w v : ι → ℝ) (d : ι → X → X → ℝ)
    (a b c e : X) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (hd : ∀ i, 0 ≤ coefficient (d i) a b c e) :
    0 < coefficient (mixture w d) a b c e ↔
      0 < coefficient (mixture v d) a b c e := by
  exact (coefficient_mixture_pos_iff w d a b c e hw hd).trans
    (coefficient_mixture_pos_iff v d a b c e hv hd).symm

#print axioms coefficient_mixture
#print axioms coefficient_mixture_nonneg
#print axioms coefficient_mixture_pos_iff
#print axioms positive_weights_preserve_support

end NanuqPositiveCombination
