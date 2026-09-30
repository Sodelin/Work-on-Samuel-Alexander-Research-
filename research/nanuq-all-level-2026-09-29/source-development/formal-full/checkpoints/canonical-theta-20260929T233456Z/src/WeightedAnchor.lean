import Mathlib.Data.Rat.Lemmas
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.ByContra

/-!
The weighted NANUQ formula and its exact anchor expansion.
Quartet input rho is the source uniform average over distinct displayed
quartets. This algebraic file does not identify rho with a graph evaluator.
All pair sums use p < q, so quartet anchor orientation is explicit.
-/
namespace Nanuq.Weighted

variable {n : Nat}
abbrev Matrix (n : Nat) := Fin n → Fin n → ℚ
abbrev QuartetData (n : Nat) := Fin n → Fin n → Fin n → Fin n → ℚ

def outside (x y c : Fin n) : Prop := c ≠ x ∧ c ≠ y

instance (x y c : Fin n) : Decidable (outside x y c) :=
  inferInstanceAs (Decidable (c ≠ x ∧ c ≠ y))

def upperSum (f : Fin n → Fin n → ℚ) : ℚ :=
  ∑ p, ∑ q, if p < q then f p q else 0

def anchorMatrix (rho : QuartetData n) (p q : Fin n) : Matrix n :=
  fun x y =>
    if x = y then 0
    else if (x = p ∨ x = q) ∧ (y = p ∨ y = q) then 0
    else if (x = p ∨ x = q) ∨ (y = p ∨ y = q) then 1
    else 2 * rho x y p q

def weightedNanuq (rho : QuartetData n) (m : Fin n → ℚ) : Matrix n :=
  fun x y =>
    if x = y then 0
    else
      (∑ p, ∑ q, if p < q ∧ outside x y p ∧ outside x y q
        then 2 * m p * m q * rho x y p q else 0) +
      (m x + m y) * ∑ c, if outside x y c then m c else 0

@[simp] theorem anchorMatrix_diag (rho : QuartetData n) (p q x : Fin n) :
    anchorMatrix rho p q x x = 0 := by simp [anchorMatrix]

@[simp] theorem weightedNanuq_diag (rho : QuartetData n) (m : Fin n → ℚ)
    (x : Fin n) : weightedNanuq rho m x x = 0 := by simp [weightedNanuq]

private theorem ordered_incidence_sum (m : Fin n → ℚ) (x y : Fin n)
    (hxy : x ≠ y) :
    (∑ c, if x < c ∧ c ≠ y then m x * m c else 0) +
    (∑ c, if c < x ∧ c ≠ y then m c * m x else 0) =
    m x * ∑ c, if outside x y c then m c else 0 := by
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  rcases lt_trichotomy x c with h | h | h
  · have hne : c ≠ x := ne_of_gt h
    have hnlt : ¬ c < x := not_lt_of_ge (le_of_lt h)
    by_cases hcy : c = y <;> simp [h, hnlt, hcy, outside, hne]
  · subst c
    simp [outside]
  · have hne : c ≠ x := ne_of_lt h
    have hnlt : ¬ x < c := not_lt_of_ge (le_of_lt h)
    by_cases hcy : c = y <;> simp [h, hnlt, hcy, outside, hne, mul_comm]

private theorem endpoint_sum (m : Fin n → ℚ) (x y : Fin n)
    (hxy : x ≠ y) :
    (∑ p, ∑ q,
      ((if p = x then (if x < q ∧ q ≠ y then m x * m q else 0) else 0) +
       (if q = x then (if p < x ∧ p ≠ y then m p * m x else 0) else 0))) =
    m x * ∑ c, if outside x y c then m c else 0 := by
  simp only [Finset.sum_add_distrib]
  have hfirst :
      (∑ p, ∑ q, if p = x then (if x < q ∧ q ≠ y then m x * m q else 0) else 0) =
      ∑ q, if x < q ∧ q ≠ y then m x * m q else 0 := by
    rw [Finset.sum_comm]
    simp
  have hsecond :
      (∑ p, ∑ q, if q = x then (if p < x ∧ p ≠ y then m p * m x else 0) else 0) =
      ∑ p, if p < x ∧ p ≠ y then m p * m x else 0 := by
    simp
  rw [hfirst, hsecond]
  exact ordered_incidence_sum m x y hxy

private theorem anchor_entry_expansion (rho : QuartetData n) (m : Fin n → ℚ)
    (x y p q : Fin n) (hxy : x ≠ y) :
    (if p < q then m p * m q * anchorMatrix rho p q x y else 0) =
    (if p < q ∧ outside x y p ∧ outside x y q
      then 2 * m p * m q * rho x y p q else 0) +
    ((if p = x then (if x < q ∧ q ≠ y then m x * m q else 0) else 0) +
     (if q = x then (if p < x ∧ p ≠ y then m p * m x else 0) else 0)) +
    ((if p = y then (if y < q ∧ q ≠ x then m y * m q else 0) else 0) +
     (if q = y then (if p < y ∧ p ≠ x then m p * m y else 0) else 0)) := by
  by_cases hpq : p < q
  · have hpq' : p ≠ q := ne_of_lt hpq
    by_cases hpx : p = x <;> by_cases hpy : p = y <;>
      by_cases hqx : q = x <;> by_cases hqy : q = y <;>
      simp_all [anchorMatrix, outside, eq_comm] <;> ring
  · simp only [if_neg hpq, hpq, false_and]
    have hxpq : ¬ (p = x ∧ x < q) := by rintro ⟨rfl, h⟩; exact hpq h
    have hqxp : ¬ (q = x ∧ p < x) := by rintro ⟨rfl, h⟩; exact hpq h
    have hypq : ¬ (p = y ∧ y < q) := by rintro ⟨rfl, h⟩; exact hpq h
    have hqyp : ¬ (q = y ∧ p < y) := by rintro ⟨rfl, h⟩; exact hpq h
    by_cases hpx : p = x <;> by_cases hpy : p = y <;>
      by_cases hqx : q = x <;> by_cases hqy : q = y <;>
      simp_all [anchorMatrix, outside]

/-- Exact algebraic expansion of the source weighted formula. -/
theorem weightedNanuq_eq_anchor_sum (rho : QuartetData n) (m : Fin n → ℚ)
    (x y : Fin n) :
    weightedNanuq rho m x y =
    upperSum (fun p q => m p * m q * anchorMatrix rho p q x y) := by
  by_cases hxy : x = y
  · subst y
    simp [weightedNanuq, upperSum]
  · unfold upperSum
    simp_rw [anchor_entry_expansion rho m x y _ _ hxy]
    simp only [Finset.sum_add_distrib]
    have hex := endpoint_sum m x y hxy
    have hey := endpoint_sum m y x (Ne.symm hxy)
    simp only [Finset.sum_add_distrib] at hex hey
    rw [hex, hey]
    have hout : (∑ c, if outside y x c then m c else 0) =
        ∑ c, if outside x y c then m c else 0 := by
      apply Finset.sum_congr rfl
      intro c _
      by_cases hcx : c = x <;> by_cases hcy : c = y <;> simp [outside, hcx, hcy]
    rw [hout]
    simp only [weightedNanuq, if_neg hxy]
    ring

#print axioms weightedNanuq_eq_anchor_sum

end Nanuq.Weighted




