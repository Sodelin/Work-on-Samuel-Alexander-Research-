import WeightedCoefficients

/-!
The paper's NANUQ formula (uniform distinct-quartet input) is exactly the
unit-mass specialization of the concrete weighted definition. This connection
retains its constant 2n-4 and makes no switching-multiplicity substitution.
-/
namespace Nanuq.Weighted

variable {n : Nat}

/-- The source quartet metric, with its original constant term. -/
def sourceNanuq (rho : QuartetData n) : Matrix n :=
  fun x y =>
    if x = y then 0
    else
      2 * (∑ p, ∑ q, if p < q ∧ outside x y p ∧ outside x y q
        then rho x y p q else 0) + 2 * (n : ℚ) - 4

theorem unit_outside_sum (x y : Fin n) (hxy : x ≠ y) :
    (∑ c, if outside x y c then (1 : ℚ) else 0) = (n : ℚ) - 2 := by
  have hpart : ∀ c : Fin n,
      (if outside x y c then (1 : ℚ) else 0) =
        1 - (if c = x then 1 else 0) - (if c = y then 1 else 0) := by
    intro c
    by_cases hcx : c = x <;> by_cases hcy : c = y <;>
      simp_all [outside]
  simp_rw [hpart]
  simp only [Finset.sum_sub_distrib]
  simp
  ring

/-- The weighted definition specializes literally to equations (10)-(11). -/
theorem weightedNanuq_unit_eq_source (rho : QuartetData n) :
    weightedNanuq rho (fun _ => 1) = sourceNanuq rho := by
  funext x y
  by_cases hxy : x = y
  · subst y
    simp [weightedNanuq, sourceNanuq]
  · simp only [weightedNanuq, sourceNanuq, if_neg hxy, mul_one]
    rw [unit_outside_sum x y hxy]
    simp only [Finset.mul_sum, mul_ite, mul_zero]
    ring

/-- Exact positive support transfers from the source metric to every positive
choice of terminal masses, conditional only on the local anchor inequalities. -/
theorem positive_masses_source_support (rho : QuartetData n)
    (m : Fin n → ℚ) (hm : ∀ x, 0 < m x) (i j : Fin n)
    (ha : ∀ p q, p < q → 0 ≤ circularAlpha (anchorMatrix rho p q) i j) :
    0 < circularAlpha (weightedNanuq rho m) i j ↔
    0 < circularAlpha (sourceNanuq rho) i j := by
  rw [← weightedNanuq_unit_eq_source rho]
  exact positive_masses_preserve_circular_support rho m (fun _ => 1) hm
    (fun _ => by decide) i j ha

theorem positive_masses_source_zeros (rho : QuartetData n)
    (m : Fin n → ℚ) (hm : ∀ x, 0 < m x) (i j : Fin n)
    (ha : ∀ p q, p < q → 0 ≤ circularAlpha (anchorMatrix rho p q) i j) :
    circularAlpha (weightedNanuq rho m) i j = 0 ↔
    circularAlpha (sourceNanuq rho) i j = 0 := by
  rw [← weightedNanuq_unit_eq_source rho]
  exact positive_masses_preserve_circular_zeros rho m (fun _ => 1) hm
    (fun _ => by decide) i j ha

#print axioms weightedNanuq_unit_eq_source
#print axioms positive_masses_source_support
#print axioms positive_masses_source_zeros

end Nanuq.Weighted

