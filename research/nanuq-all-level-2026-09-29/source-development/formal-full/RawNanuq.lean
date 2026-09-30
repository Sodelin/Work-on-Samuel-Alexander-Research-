import SourceQuartetSymmetry
import SourceCompositionBridge
import WeightedProperties
import Mathlib.Tactic.FinCases

/-! A numeric NANUQ tensor obtained from actual raw graph switchings. This
connects the graph semantics to the weighted formula without supplying a
quartet resolver or a symmetric tensor as an assumed field. The semidirected
restriction convention and global circularity remain separate obligations. -/
namespace Nanuq.Quartet

theorem distinctMean_nonneg (s : Finset Resolution) : 0 ≤ distinctMean s := by
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro r _
    cases r <;> decide
  · exact Nat.cast_nonneg _

end Nanuq.Quartet

namespace Nanuq.Source.RootedBinary

open Nanuq.Quartet Nanuq.Weighted Nanuq.Composition
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] {n : Nat}

def ValidFour (x y p q : Fin n) : Prop :=
  x ≠ y ∧ p ≠ q ∧ outside x y p ∧ outside x y q

instance (x y p q : Fin n) : Decidable (ValidFour x y p q) :=
  inferInstanceAs (Decidable (x ≠ y ∧ p ≠ q ∧ outside x y p ∧ outside x y q))

def fourTaxa (x y p q : Fin n) (h : ValidFour x y p q) : Fin 4 ↪ Fin n :=
  ⟨(fun i => if i = 0 then x else if i = 1 then y else if i = 2 then p else q), by
    intro i j he
    fin_cases i <;> fin_cases j <;> simp_all [ValidFour, outside, eq_comm]⟩

theorem validFour_first (x y p q : Fin n) (h : ValidFour x y p q) :
    ValidFour y x p q :=
  ⟨h.1.symm, h.2.1, ⟨h.2.2.1.2, h.2.2.1.1⟩, ⟨h.2.2.2.2, h.2.2.2.1⟩⟩

theorem validFour_last (x y p q : Fin n) (h : ValidFour x y p q) :
    ValidFour x y q p := ⟨h.1, h.2.1.symm, h.2.2.2, h.2.2.1⟩

theorem fourTaxa_swap_first (x y p q : Fin n) (h : ValidFour x y p q) :
    fourTaxa y x p q (validFour_first x y p q h) = swapFirst (fourTaxa x y p q h) := by
  ext i
  fin_cases i <;> simp [fourTaxa, swapFirst, Equiv.swap_apply_def] <;> rfl

theorem fourTaxa_swap_last (x y p q : Fin n) (h : ValidFour x y p q) :
    fourTaxa x y q p (validFour_last x y p q h) = swapLast (fourTaxa x y p q h) := by
  ext i
  fin_cases i <;> simp [fourTaxa, swapLast, Equiv.swap_apply_def] <;> rfl

noncomputable def rawRho (N : RootedBinary V E (Fin n)) : QuartetData n := fun x y p q =>
  if h : ValidFour x y p q then N.rawQuartetMean (fourTaxa x y p q h) else 0

theorem rawRho_valid (N : RootedBinary V E (Fin n)) (x y p q : Fin n)
    (h : ValidFour x y p q) :
    N.rawRho x y p q = N.rawQuartetMean (fourTaxa x y p q h) := by
  simp [rawRho, h]

theorem rawRho_nonneg (N : RootedBinary V E (Fin n)) (x y p q : Fin n) :
    0 ≤ N.rawRho x y p q := by
  unfold rawRho
  split_ifs
  · exact distinctMean_nonneg _
  · exact le_refl 0

theorem rawRho_witness_symmetric (N : RootedBinary V E (Fin n)) :
    WitnessSymmetric N.rawRho := by
  intro x y p q hxy hpq hp hq
  have h : ValidFour x y p q := ⟨hxy, hpq, hp, hq⟩
  rw [N.rawRho_valid x y p q h, N.rawRho_valid x y q p (validFour_last x y p q h),
    fourTaxa_swap_last, N.rawQuartetMean_swap_last]

theorem rawRho_endpoint_symmetric (N : RootedBinary V E (Fin n)) :
    QuartetEndpointSymmetric N.rawRho := by
  intro x y p q hxy hpq hp hq
  have h : ValidFour x y p q := ⟨hxy, hpq, hp, hq⟩
  rw [N.rawRho_valid x y p q h, N.rawRho_valid y x p q (validFour_first x y p q h),
    fourTaxa_swap_first, N.rawQuartetMean_swap_first]

noncomputable def rawNanuq (N : RootedBinary V E (Fin n)) : Matrix n :=
  sourceNanuq N.rawRho

theorem rawNanuq_symmetric (N : RootedBinary V E (Fin n)) (x y : Fin n) :
    N.rawNanuq x y = N.rawNanuq y x :=
  sourceNanuq_symmetric N.rawRho N.rawRho_endpoint_symmetric x y

theorem rawNanuq_positive (N : RootedBinary V E (Fin n)) (hn : 3 ≤ n)
    (x y : Fin n) (hxy : x ≠ y) : 0 < N.rawNanuq x y :=
  sourceNanuq_pos_of_three_le N.rawRho hn x y hxy
    (fun p q _ _ _ => N.rawRho_nonneg x y p q)

theorem rawNanuq_ordered_formula (N : RootedBinary V E (Fin n)) (x y : Fin n) :
    N.rawNanuq x y = sourceDistance (maskedRho N.rawRho) x y :=
  (sourceDistance_eq_sourceNanuq N.rawRho N.rawRho_witness_symmetric x y).symm

#print axioms rawRho_valid
#print axioms rawRho_witness_symmetric
#print axioms rawNanuq_symmetric
#print axioms rawNanuq_positive
#print axioms rawNanuq_ordered_formula

end Nanuq.Source.RootedBinary
