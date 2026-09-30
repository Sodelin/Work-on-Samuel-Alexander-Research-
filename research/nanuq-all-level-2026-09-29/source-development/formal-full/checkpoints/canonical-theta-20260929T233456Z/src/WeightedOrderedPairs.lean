import WeightedCoefficients

/-! Exact conversion between ordered and unordered pair normalizations. -/
namespace Nanuq.Weighted

variable {n : Nat}

/-- An ordered symmetric zero-diagonal sum counts each unordered pair twice. -/
theorem ordered_pair_sum_eq_twice_upperSum (f : Fin n → Fin n → ℚ)
    (hsym : ∀ p q, f p q = f q p) (hdiag : ∀ p, f p p = 0) :
    (∑ p, ∑ q, f p q) = 2 * upperSum f := by
  have hentry : ∀ p q,
      f p q = (if p < q then f p q else 0) + (if q < p then f p q else 0) := by
    intro p q
    rcases lt_trichotomy p q with hpq | hpq | hqp
    · simp [hpq, not_lt_of_ge (le_of_lt hpq)]
    · subst q
      simp [hdiag]
    · simp [hqp, not_lt_of_ge (le_of_lt hqp)]
  have hsum :
      (∑ p, ∑ q, f p q) =
        (∑ p, ∑ q, if p < q then f p q else 0) +
        (∑ p, ∑ q, if q < p then f p q else 0) := by
    calc
      _ = ∑ p, ∑ q,
          ((if p < q then f p q else 0) + (if q < p then f p q else 0)) := by
        apply Finset.sum_congr rfl
        intro p _
        apply Finset.sum_congr rfl
        intro q _
        exact hentry p q
      _ = _ := by simp only [Finset.sum_add_distrib]
  have hreverse :
      (∑ p, ∑ q, if q < p then f p q else 0) = upperSum f := by
    rw [Finset.sum_comm]
    unfold upperSum
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    rw [hsym q p]
  rw [hsum, hreverse]
  unfold upperSum
  ring

/-- The equivalent filtered-pair statement used by split reconstruction. -/
theorem ordered_pair_sum_eq_twice_upperPairs (f : Fin n → Fin n → ℚ)
    (hsym : ∀ p q, f p q = f q p) (hdiag : ∀ p, f p p = 0) :
    (∑ p, ∑ q, f p q) = 2 * ∑ pq ∈ upperPairs n, f pq.1 pq.2 := by
  rw [ordered_pair_sum_eq_twice_upperSum f hsym hdiag, upperSum_eq_pair_sum]

#print axioms ordered_pair_sum_eq_twice_upperSum

end Nanuq.Weighted

