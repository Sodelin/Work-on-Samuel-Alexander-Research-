import QuartetCompositionDependent
import WeightedOrderedPairs
import WeightedSource

/-! The ordered-pair composition algebra is exactly the source's unordered-pair
NANUQ formula, including its constant term and all repeated-label masks. -/
namespace Nanuq.Composition

open scoped BigOperators
open Nanuq.Weighted

variable {n : Nat}

def maskedRho (rho : QuartetData n) : QuartetData n := fun x y z w =>
  if x ≠ y ∧ z ≠ w ∧ outside x y z ∧ outside x y w then rho x y z w else 0

def WitnessSymmetric (rho : QuartetData n) : Prop :=
  ∀ x y z w, x ≠ y → z ≠ w → outside x y z → outside x y w →
    rho x y z w = rho x y w z

@[simp] theorem maskedRho_repeated_endpoints (rho : QuartetData n) (x z w : Fin n) :
    maskedRho rho x x z w = 0 := by simp [maskedRho]

@[simp] theorem maskedRho_repeated_witnesses (rho : QuartetData n) (x y z : Fin n) :
    maskedRho rho x y z z = 0 := by simp [maskedRho]

theorem maskedRho_witness_symmetric (rho : QuartetData n) (hsym : WitnessSymmetric rho)
    (x y z w : Fin n) : maskedRho rho x y z w = maskedRho rho x y w z := by
  have hvalid : (x ≠ y ∧ w ≠ z ∧ outside x y w ∧ outside x y z) ↔
      (x ≠ y ∧ z ≠ w ∧ outside x y z ∧ outside x y w) := by
    constructor
    · rintro ⟨hxy, hwz, hw, hz⟩
      exact ⟨hxy, hwz.symm, hz, hw⟩
    · rintro ⟨hxy, hzw, hz, hw⟩
      exact ⟨hxy, hzw.symm, hw, hz⟩
  simp only [maskedRho, hvalid]
  split_ifs with h
  · exact hsym x y z w h.1 h.2.1 h.2.2.1 h.2.2.2
  · rfl

theorem masked_upper_sum (rho : QuartetData n) (x y : Fin n) (hxy : x ≠ y) :
    upperSum (maskedRho rho x y) =
      ∑ z, ∑ w, if z < w ∧ outside x y z ∧ outside x y w then rho x y z w else 0 := by
  unfold upperSum
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro w _
  by_cases hzw : z < w
  · simp [maskedRho, hxy, hzw, ne_of_lt hzw]
  · simp [hzw]

theorem sourceDistance_eq_sourceNanuq (rho : QuartetData n) (hsym : WitnessSymmetric rho)
    (x y : Fin n) :
    sourceDistance (maskedRho rho) x y = sourceNanuq rho x y := by
  by_cases hxy : x = y
  · simp [sourceDistance, sourceNanuq, hxy]
  · simp only [sourceDistance, sourceNanuq, hxy, if_false, Fintype.card_fin]
    rw [ordered_pair_sum_eq_twice_upperSum (maskedRho rho x y)
      (maskedRho_witness_symmetric rho hsym x y)
      (maskedRho_repeated_witnesses rho x y), masked_upper_sum rho x y hxy]

theorem localWeighted_eq_weightedNanuq (rho : QuartetData n) (hsym : WitnessSymmetric rho)
    (m : Fin n → ℚ) (x y : Fin n) :
    localWeighted (maskedRho rho) m x y = weightedNanuq rho m x y := by
  by_cases hxy : x = y
  · simp [localWeighted, weightedNanuq, hxy]
  · have hswap : ∀ z w, m z * m w * maskedRho rho x y z w =
        m w * m z * maskedRho rho x y w z := by
      intro z w
      rw [maskedRho_witness_symmetric rho hsym x y z w, mul_comm (m z) (m w)]
    have hdiag : ∀ z, m z * m z * maskedRho rho x y z z = 0 := by
      intro z
      simp
    simp only [localWeighted, weightedNanuq, hxy, if_false]
    rw [ordered_pair_sum_eq_twice_upperSum _ hswap hdiag]
    congr 1
    · unfold upperSum
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      apply Finset.sum_congr rfl
      intro w _
      by_cases hzw : z < w
      · by_cases ho : outside x y z ∧ outside x y w
        · simp [hzw, maskedRho, hxy, ne_of_lt hzw, ho.1, ho.2]
          ring
        · simp [hzw, maskedRho, hxy, ne_of_lt hzw, ho]
      · simp [hzw]
    · congr 1
      simp only [Finset.sum_filter, outside]
      rfl

#print axioms sourceDistance_eq_sourceNanuq
#print axioms localWeighted_eq_weightedNanuq

end Nanuq.Composition
