import WeightedAnchor
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.Field.Rat

/-!
Circular coefficients of the concrete weighted NANUQ formula.
These results prove nonnegativity and exact positive-support invariance under
positive terminal masses from the anchor inequalities. The anchor inequalities
themselves are separate graph-dependent obligations.
-/
namespace Nanuq.Weighted

variable {n : Nat}

def upperPairs (n : Nat) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun pq => pq.1 < pq.2)

@[simp] theorem mem_upperPairs (p q : Fin n) :
    (p, q) ∈ upperPairs n ↔ p < q := by simp [upperPairs]

theorem upperSum_eq_pair_sum (f : Fin n → Fin n → ℚ) :
    upperSum f = ∑ pq ∈ upperPairs n, f pq.1 pq.2 := by
  simp [upperSum, upperPairs, Finset.sum_filter, Fintype.sum_prod_type]

/-- The cyclic successor is defined even for a type parameter n=0:
there is then no input i. -/
def cyclicNext (i : Fin n) : Fin n :=
  ⟨(i.val + 1) % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)⟩

def circularAlpha (d : Matrix n) (i j : Fin n) : ℚ :=
  d i j + d (cyclicNext i) (cyclicNext j) -
    d i (cyclicNext j) - d (cyclicNext i) j

/-- Coefficients use the paper's unhalved convention; actual split weights
are alpha/2. This is an explicit expansion of the source-defined matrix. -/
theorem circularAlpha_weightedNanuq (rho : QuartetData n) (m : Fin n → ℚ)
    (i j : Fin n) :
    circularAlpha (weightedNanuq rho m) i j =
    ∑ pq ∈ upperPairs n, m pq.1 * m pq.2 *
      circularAlpha (anchorMatrix rho pq.1 pq.2) i j := by
  simp only [circularAlpha, weightedNanuq_eq_anchor_sum, upperSum_eq_pair_sum,
    mul_sub, mul_add, Finset.sum_add_distrib, Finset.sum_sub_distrib]

theorem circularAlpha_weightedNanuq_nonneg (rho : QuartetData n)
    (m : Fin n → ℚ) (hm : ∀ x, 0 ≤ m x) (i j : Fin n)
    (ha : ∀ p q, p < q → 0 ≤ circularAlpha (anchorMatrix rho p q) i j) :
    0 ≤ circularAlpha (weightedNanuq rho m) i j := by
  rw [circularAlpha_weightedNanuq]
  apply Finset.sum_nonneg
  intro pq hpq
  exact mul_nonneg (mul_nonneg (hm _) (hm _))
    (ha _ _ ((mem_upperPairs _ _).mp hpq))

/-- Positive support consists exactly of the union of anchor supports. -/
theorem circularAlpha_weightedNanuq_pos_iff (rho : QuartetData n)
    (m : Fin n → ℚ) (hm : ∀ x, 0 < m x) (i j : Fin n)
    (ha : ∀ p q, p < q → 0 ≤ circularAlpha (anchorMatrix rho p q) i j) :
    0 < circularAlpha (weightedNanuq rho m) i j ↔
      ∃ p q, p < q ∧ 0 < circularAlpha (anchorMatrix rho p q) i j := by
  rw [circularAlpha_weightedNanuq]
  constructor
  · intro hpos
    by_contra! hnone
    have hnonpos :
        (∑ pq ∈ upperPairs n, m pq.1 * m pq.2 *
          circularAlpha (anchorMatrix rho pq.1 pq.2) i j) ≤ 0 := by
      apply Finset.sum_nonpos
      intro pq hpq
      exact mul_nonpos_of_nonneg_of_nonpos
        (le_of_lt (mul_pos (hm _) (hm _)))
        (hnone _ _ ((mem_upperPairs _ _).mp hpq))
    exact (not_lt_of_ge hnonpos) hpos
  · rintro ⟨p, q, hpq, hpos⟩
    have hone :
        m p * m q * circularAlpha (anchorMatrix rho p q) i j ≤
        ∑ pq ∈ upperPairs n, m pq.1 * m pq.2 *
          circularAlpha (anchorMatrix rho pq.1 pq.2) i j := by
      apply Finset.single_le_sum (a := (p, q)) (s := upperPairs n)
        (f := fun pq : Fin n × Fin n => m pq.1 * m pq.2 *
          circularAlpha (anchorMatrix rho pq.1 pq.2) i j)
      · intro pq hpq'
        exact mul_nonneg (le_of_lt (mul_pos (hm _) (hm _)))
          (ha _ _ ((mem_upperPairs _ _).mp hpq'))
      · exact (mem_upperPairs _ _).mpr hpq
    exact lt_of_lt_of_le (mul_pos (mul_pos (hm _) (hm _)) hpos) hone

theorem positive_masses_preserve_circular_support (rho : QuartetData n)
    (m v : Fin n → ℚ) (hm : ∀ x, 0 < m x) (hv : ∀ x, 0 < v x)
    (i j : Fin n)
    (ha : ∀ p q, p < q → 0 ≤ circularAlpha (anchorMatrix rho p q) i j) :
    0 < circularAlpha (weightedNanuq rho m) i j ↔
    0 < circularAlpha (weightedNanuq rho v) i j :=
  (circularAlpha_weightedNanuq_pos_iff rho m hm i j ha).trans
    (circularAlpha_weightedNanuq_pos_iff rho v hv i j ha).symm

theorem positive_masses_preserve_circular_zeros (rho : QuartetData n)
    (m v : Fin n → ℚ) (hm : ∀ x, 0 < m x) (hv : ∀ x, 0 < v x)
    (i j : Fin n)
    (ha : ∀ p q, p < q → 0 ≤ circularAlpha (anchorMatrix rho p q) i j) :
    circularAlpha (weightedNanuq rho m) i j = 0 ↔
    circularAlpha (weightedNanuq rho v) i j = 0 := by
  have hm0 := circularAlpha_weightedNanuq_nonneg rho m (fun x => le_of_lt (hm x)) i j ha
  have hv0 := circularAlpha_weightedNanuq_nonneg rho v (fun x => le_of_lt (hv x)) i j ha
  have hs := positive_masses_preserve_circular_support rho m v hm hv i j ha
  constructor
  · intro hz
    apply le_antisymm _ hv0
    by_contra! hvp
    have hmp := hs.mpr hvp
    rw [hz] at hmp
    exact (lt_irrefl 0) hmp
  · intro hz
    apply le_antisymm _ hm0
    by_contra! hmp
    have hvp := hs.mp hmp
    rw [hz] at hvp
    exact (lt_irrefl 0) hvp

#print axioms circularAlpha_weightedNanuq
#print axioms circularAlpha_weightedNanuq_nonneg
#print axioms positive_masses_preserve_circular_support
#print axioms positive_masses_preserve_circular_zeros

end Nanuq.Weighted



