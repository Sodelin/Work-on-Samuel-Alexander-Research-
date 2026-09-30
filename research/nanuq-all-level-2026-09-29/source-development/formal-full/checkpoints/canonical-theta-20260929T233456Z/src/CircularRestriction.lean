import CircularDecomposition
import Lean.Elab.Tactic.Omega

/-! Circular split decomposition survives restriction to an ordered subset of
taxa. This is proved from interval split metrics, without a network assumption. -/
namespace Nanuq.Reconstruction

open scoped BigOperators
open Nanuq.Weighted

variable {n m : Nat}

theorem gapSplit_cyclic_four_nonneg (a b x y z w : Fin m) (hab : a < b)
    (hxy : x ≤ y) (hyz : y ≤ z) (hwrap : z ≤ w ∨ w ≤ x) :
    0 ≤ gapSplit a b x z + gapSplit a b y w - gapSplit a b x w - gapSplit a b y z := by
  simp only [gapSplit_eq_separation a b _ _ hab]
  by_cases hx : inArc a b x <;> by_cases hy : inArc a b y <;>
    by_cases hz : inArc a b z <;> by_cases hw : inArc a b w <;>
    simp [hx, hy, hz, hw]
  all_goals
    simp only [inArc] at hx hy hz hw
    omega

theorem increasing_cyclic_four (f : Fin n → Fin m) (hf : StrictMono f)
    (i j : Fin n) (hij : i < j) :
    f i ≤ f (cyclicNext i) ∧ f (cyclicNext i) ≤ f j ∧
      (f j ≤ f (cyclicNext j) ∨ f (cyclicNext j) ≤ f i) := by
  have hni : i.val + 1 < n := by omega
  have hnexti : (cyclicNext i).val = i.val + 1 := by
    simp [cyclicNext, Nat.mod_eq_of_lt hni]
  refine ⟨hf.monotone (by show i.val ≤ (cyclicNext i).val; omega),
    hf.monotone (by show (cyclicNext i).val ≤ j.val; omega), ?_⟩
  by_cases hnj : j.val + 1 < n
  · left
    have hnextj : (cyclicNext j).val = j.val + 1 := by
      simp [cyclicNext, Nat.mod_eq_of_lt hnj]
    exact hf.monotone (by show j.val ≤ (cyclicNext j).val; omega)
  · right
    have hlast : j.val + 1 = n := by omega
    have hnextj : (cyclicNext j).val = 0 := by simp [cyclicNext, hlast]
    exact hf.monotone (by show (cyclicNext j).val ≤ i.val; omega)

theorem gapSplit_restriction_coefficient_nonneg (f : Fin n → Fin m)
    (hf : StrictMono f) (a b : Fin m) (hab : a < b)
    (i j : Fin n) (hij : i < j) :
    0 ≤ circularAlpha (fun x y => gapSplit a b (f x) (f y)) i j := by
  obtain ⟨hxy, hyz, hwrap⟩ := increasing_cyclic_four f hf i j hij
  exact gapSplit_cyclic_four_nonneg a b (f i) (f (cyclicNext i))
    (f j) (f (cyclicNext j)) hab hxy hyz hwrap

theorem circular_decomposable_restriction (d : Matrix m) (hd : CircularDecomposable d)
    (f : Fin n → Fin m) (hf : StrictMono f) :
    CircularDecomposable (fun x y => d (f x) (f y)) := by
  have hlaws := circular_decomposable_pseudometric d hd
  obtain ⟨weights, hw, heq⟩ := hd
  apply circular_decomposable_of_coefficients
  · intro x y; exact hlaws.2.2.1 _ _
  · intro x; exact hlaws.2.1 _
  · intro i j hij
    have hexpand : circularAlpha (fun x y => d (f x) (f y)) i j =
        ∑ pq ∈ upperPairs m, weights pq.1 pq.2 *
          circularAlpha (fun x y => gapSplit pq.1 pq.2 (f x) (f y)) i j := by
      simp only [circularAlpha, heq, mul_add, mul_sub,
        Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [hexpand]
    apply Finset.sum_nonneg
    intro pq hpq
    have hord := (mem_upperPairs _ _).mp hpq
    exact mul_nonneg (hw _ _ hord)
      (gapSplit_restriction_coefficient_nonneg f hf _ _ hord i j hij)

#print axioms gapSplit_cyclic_four_nonneg
#print axioms circular_decomposable_restriction

end Nanuq.Reconstruction
