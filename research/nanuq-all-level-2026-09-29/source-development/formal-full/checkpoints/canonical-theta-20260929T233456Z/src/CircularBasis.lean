import CircularDecomposition

/-! A circular interval split has exactly one positive circular coefficient.
This supplies uniqueness and exact support for nonnegative split mixtures. -/
namespace Nanuq.Reconstruction

open scoped BigOperators
open Nanuq.Weighted

variable {n : Nat}

theorem cut_boundary_difference (i j k : Fin n) :
    (cut i k - cut j k) - (cut i (cyclicNext k) - cut j (cyclicNext k)) =
      (if k = j then 1 else 0) - (if k = i then 1 else 0) := by
  have hi := i.isLt
  have hj := j.isLt
  have hk := k.isLt
  by_cases hnext : k.val + 1 < n
  · simp only [cut, cyclicNext, Fin.lt_def, Nat.mod_eq_of_lt hnext]
    split_ifs <;> norm_num <;> simp_all only [Fin.ext_iff] <;> omega
  · have hlast : k.val + 1 = n := by omega
    simp only [cut, cyclicNext, Fin.lt_def, hlast, Nat.mod_self]
    split_ifs <;> norm_num <;> simp_all only [Fin.ext_iff] <;> omega

theorem alpha_gapSplit (i j k l : Fin n) (hij : i < j) (hkl : k < l) :
    circularAlpha (gapSplit i j) k l = if k = i ∧ l = j then 2 else 0 := by
  have heq : circularAlpha (gapSplit i j) k l =
      -2 * ((cut i k - cut j k) - (cut i (cyclicNext k) - cut j (cyclicNext k))) *
        ((cut i l - cut j l) - (cut i (cyclicNext l) - cut j (cyclicNext l))) := by
    unfold circularAlpha gapSplit
    ring
  rw [heq, cut_boundary_difference, cut_boundary_difference]
  split_ifs <;> norm_num <;> simp_all only [Fin.ext_iff, Fin.lt_def] <;> try omega
  all_goals simp_all only [true_and, and_true, not_true_eq_false]

def splitMixture (weights : Matrix n) : Matrix n := fun x y =>
  ∑ pq ∈ upperPairs n, weights pq.1 pq.2 * gapSplit pq.1 pq.2 x y

theorem alpha_splitMixture_expansion (weights : Matrix n) (i j : Fin n) :
    circularAlpha (splitMixture weights) i j =
      ∑ pq ∈ upperPairs n, weights pq.1 pq.2 * circularAlpha (gapSplit pq.1 pq.2) i j := by
  simp only [circularAlpha, splitMixture, mul_sub, mul_add,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]

/-- No two distinct circular gap pairs encode the same split contribution. -/
theorem alpha_splitMixture (weights : Matrix n) (i j : Fin n) (hij : i < j) :
    circularAlpha (splitMixture weights) i j = 2 * weights i j := by
  rw [alpha_splitMixture_expansion]
  calc
    _ = ∑ pq ∈ upperPairs n, if pq = (i,j) then 2 * weights i j else 0 := by
      apply Finset.sum_congr rfl
      intro pq hpq
      rw [alpha_gapSplit _ _ _ _ ((mem_upperPairs _ _).mp hpq) hij]
      by_cases heq : pq = (i,j)
      · subst pq
        simp [mul_comm]
      · have hnot : ¬ (i = pq.1 ∧ j = pq.2) := by
          rintro ⟨hi, hj⟩
          apply heq
          exact Prod.ext hi.symm hj.symm
        simp [hnot, heq]
    _ = _ := by simp [hij]

theorem splitMixture_support (weights : Matrix n) (i j : Fin n) (hij : i < j) :
    0 < circularAlpha (splitMixture weights) i j ↔ 0 < weights i j := by
  rw [alpha_splitMixture weights i j hij]
  exact mul_pos_iff_of_pos_left (by decide)

theorem circular_decomposition_unique (weights other : Matrix n)
    (heq : splitMixture weights = splitMixture other) (i j : Fin n) (hij : i < j) :
    weights i j = other i j := by
  have h := congrArg (fun d => circularAlpha d i j) heq
  rw [alpha_splitMixture weights i j hij, alpha_splitMixture other i j hij] at h
  exact (mul_left_cancel₀ (by decide : (2 : ℚ) ≠ 0)) h

#print axioms alpha_gapSplit
#print axioms splitMixture_support
#print axioms circular_decomposition_unique

end Nanuq.Reconstruction
