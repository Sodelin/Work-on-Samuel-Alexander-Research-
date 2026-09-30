import SplitReconstruction
import WeightedOrderedPairs

/-! Explicit nonnegative circular split decompositions and their metric laws. -/
namespace Nanuq.Reconstruction

open scoped BigOperators
open Nanuq.Weighted

variable {n : Nat}

theorem circular_reconstruction (d : Matrix n)
    (hsym : ∀ x y, d x y = d y x) (hdiag : ∀ x, d x x = 0) (x y : Fin n) :
    d x y = ∑ pq ∈ upperPairs n,
      (circularAlpha d pq.1 pq.2 / 2) * gapSplit pq.1 pq.2 x y := by
  have hsum := ordered_pair_sum_eq_twice_upperPairs
    (fun i j => circularAlpha d i j * gapSplit i j x y)
    (fun i j => by rw [alpha_symmetric d hsym i j, gapSplit_symm_gaps i j x y])
    (fun i => by simp)
  rw [circular_reconstruction_ordered d hsym hdiag x y, hsum]
  have hscale : (∑ pq ∈ upperPairs n,
      (circularAlpha d pq.1 pq.2 / 2) * gapSplit pq.1 pq.2 x y) =
      (∑ pq ∈ upperPairs n, circularAlpha d pq.1 pq.2 * gapSplit pq.1 pq.2 x y) / 2 := by
    simp only [div_eq_mul_inv]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro pq _
    ring
  rw [hscale]
  ring

/-- A nonnegative combination of the ordinary interval split distances. -/
def CircularDecomposable (d : Matrix n) : Prop :=
  ∃ weights : Matrix n,
    (∀ i j, i < j → 0 ≤ weights i j) ∧
      ∀ x y, d x y = ∑ pq ∈ upperPairs n, weights pq.1 pq.2 * gapSplit pq.1 pq.2 x y

theorem circular_decomposable_of_coefficients (d : Matrix n)
    (hsym : ∀ x y, d x y = d y x) (hdiag : ∀ x, d x x = 0)
    (hcoeff : ∀ i j, i < j → 0 ≤ circularAlpha d i j) :
    CircularDecomposable d := by
  refine ⟨fun i j => circularAlpha d i j / 2, ?_, ?_⟩
  · intro i j hij
    exact div_nonneg (hcoeff i j hij) (by decide)
  · exact circular_reconstruction d hsym hdiag

@[simp] theorem gapSplit_diag (i j x : Fin n) : gapSplit i j x x = 0 := by
  simp [gapSplit]

theorem gapSplit_symmetric (i j x y : Fin n) : gapSplit i j x y = gapSplit i j y x := by
  unfold gapSplit
  ring

theorem gapSplit_nonneg (i j x y : Fin n) : 0 ≤ gapSplit i j x y := sq_nonneg _

theorem gapSplit_triangle (i j x y z : Fin n) (hij : i < j) :
    gapSplit i j x z ≤ gapSplit i j x y + gapSplit i j y z := by
  simp only [gapSplit_eq_separation i j _ _ hij]
  by_cases hx : inArc i j x <;> by_cases hy : inArc i j y <;>
    by_cases hz : inArc i j z <;> simp [hx, hy, hz]

/-- The usual pseudometric laws, before any separate positive-support argument
establishes that distinct taxa have strictly positive distance. -/
def PseudometricLaws (d : Matrix n) : Prop :=
  (∀ x y, 0 ≤ d x y) ∧ (∀ x, d x x = 0) ∧
    (∀ x y, d x y = d y x) ∧ (∀ x y z, d x z ≤ d x y + d y z)

theorem circular_decomposable_pseudometric (d : Matrix n) (h : CircularDecomposable d) :
    PseudometricLaws d := by
  obtain ⟨weights, hw, hd⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y
    rw [hd]
    exact Finset.sum_nonneg fun pq hpq => mul_nonneg
      (hw _ _ ((mem_upperPairs _ _).mp hpq)) (gapSplit_nonneg _ _ _ _)
  · intro x
    simp [hd]
  · intro x y
    rw [hd, hd]
    apply Finset.sum_congr rfl
    intro pq _
    rw [gapSplit_symmetric]
  · intro x y z
    rw [hd, hd, hd, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro pq hpq
    have hij := (mem_upperPairs _ _).mp hpq
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (gapSplit_triangle _ _ _ _ _ hij) (hw _ _ hij)

theorem pseudometric_of_coefficients (d : Matrix n)
    (hsym : ∀ x y, d x y = d y x) (hdiag : ∀ x, d x x = 0)
    (hcoeff : ∀ i j, i < j → 0 ≤ circularAlpha d i j) :
    PseudometricLaws d :=
  circular_decomposable_pseudometric d (circular_decomposable_of_coefficients d hsym hdiag hcoeff)

#print axioms circular_reconstruction
#print axioms circular_decomposable_of_coefficients
#print axioms pseudometric_of_coefficients

end Nanuq.Reconstruction
