import WeightedSource
import Mathlib.Tactic.Linarith

/-! Structural properties of the concrete source and weighted metrics. -/
namespace Nanuq.Weighted

variable {n : Nat}

/-- Only valid four-distinct-taxon entries are required to be symmetric. -/
def QuartetEndpointSymmetric (rho : QuartetData n) : Prop :=
  ∀ x y p q, x ≠ y → p ≠ q → outside x y p → outside x y q →
    rho x y p q = rho y x p q

theorem weightedNanuq_symmetric (rho : QuartetData n) (m : Fin n → ℚ)
    (hrho : QuartetEndpointSymmetric rho) :
    ∀ x y, weightedNanuq rho m x y = weightedNanuq rho m y x := by
  intro x y
  by_cases hxy : x = y
  · subst y
    rfl
  · have ho : ∀ c, outside y x c ↔ outside x y c := by
      intro c
      exact and_comm
    simp only [weightedNanuq, if_neg hxy, if_neg (Ne.symm hxy), ho]
    rw [add_comm (m y) (m x)]
    congr 1
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    split_ifs with hpq
    · rw [hrho x y p q hxy (ne_of_lt hpq.1) hpq.2.1 hpq.2.2]
    · rfl

theorem sourceNanuq_symmetric (rho : QuartetData n)
    (hrho : QuartetEndpointSymmetric rho) :
    ∀ x y, sourceNanuq rho x y = sourceNanuq rho y x := by
  rw [← weightedNanuq_unit_eq_source]
  exact weightedNanuq_symmetric rho _ hrho

/-- The original constant guarantees strictly positive distances off the
diagonal for at least three taxa, independently of circular decomposition. -/
theorem sourceNanuq_pos_of_three_le (rho : QuartetData n) (hn : 3 ≤ n)
    (x y : Fin n) (hxy : x ≠ y)
    (hrho : ∀ p q, p < q → outside x y p → outside x y q → 0 ≤ rho x y p q) :
    0 < sourceNanuq rho x y := by
  have hsum :
      0 ≤ (∑ p, ∑ q, if p < q ∧ outside x y p ∧ outside x y q
        then rho x y p q else 0) := by
    apply Finset.sum_nonneg
    intro p _
    apply Finset.sum_nonneg
    intro q _
    split_ifs with hpq
    · exact hrho p q hpq.1 hpq.2.1 hpq.2.2
    · exact le_refl 0
  have hn' : (3 : ℚ) ≤ n := by exact_mod_cast hn
  simp only [sourceNanuq, if_neg hxy]
  linarith

#print axioms weightedNanuq_symmetric
#print axioms sourceNanuq_pos_of_three_le

end Nanuq.Weighted

