import SamuelAlexanderResearch.SharpThueMorse

/-! Exact first hitting times and an arithmetic form of coefficient optimality.
These results use the actual Thue--Morse trajectories; no hitting-time formula
or asymptotic bound is supplied as a hypothesis. -/

namespace SharpCorollaries
open SamuelAlexanderResearch.ThueMorseBound SharpThueMorse ThueMorseBits

def FirstHit (v time : Nat) : Prop :=
  X v time = 2 * time ∧ ∀ k, k < time → X v k ≠ 2 * k

theorem firstHit_unique {v a b : Nat} (ha : FirstHit v a) (hb : FirstHit v b) :
    a = b := by
  by_cases hab : a < b
  · exact False.elim (hb.2 a hab ha.1)
  · by_cases hba : b < a
    · exact False.elim (ha.2 b hba hb.1)
    · omega

theorem firstHit_zero : FirstHit 0 0 := by
  constructor
  · rfl
  · intro k hk; omega

theorem firstHit_one : FirstHit 1 2 := by
  constructor
  · decide +kernel
  · intro k hk
    have h : k = 0 ∨ k = 1 := by omega
    rcases h with rfl | rfl <;> decide +kernel

theorem firstHit_two : FirstHit 2 2 := by
  constructor
  · decide +kernel
  · intro k hk
    have h : k = 0 ∨ k = 1 := by omega
    rcases h with rfl | rfl <;> decide +kernel

/-- All starts in one dyadic plateau have exactly the same first baseline hit. -/
theorem firstHit_dyadic (n v : Nat)
    (hl : 3 * 2^n ≤ v) (hu : v ≤ 6 * 2^n - 1) :
    FirstHit v (8 * 2^n - 2) := by
  have hp := Nat.two_pow_pos n
  have hlast := common_descent n (3 * 2^n) (lower_join n)
  have htop := upper_coalescence n
  have hb := baseline (8 * 2^n - 2)
  have hlo := trajectory_mono t t (Nat.zero_le v) (8 * 2^n - 2)
  have hhi := trajectory_mono t t hu (8 * 2^n - 2)
  constructor
  · change X 0 _ ≤ X v _ at hlo
    change X v _ ≤ X (6 * 2^n - 1) _ at hhi
    omega
  · intro k hk he
    have hpersist := baseline_later v k (8 * 2^n - 3) he (by omega)
    have hsep := trajectory_mono t t hl (8 * 2^n - 3)
    change X (3 * 2^n) _ ≤ X v _ at hsep
    rw [hlast.1, hpersist] at hsep
    omega

/-- The complete first-hit graph, including the exceptional starts zero to two. -/
theorem firstHit_iff (v time : Nat) :
    FirstHit v time ↔
      (v = 0 ∧ time = 0) ∨
      ((v = 1 ∨ v = 2) ∧ time = 2) ∨
      ∃ n, 3 * 2^n ≤ v ∧ v ≤ 6 * 2^n - 1 ∧ time = 8 * 2^n - 2 := by
  constructor
  · intro h
    by_cases h0 : v = 0
    · subst v
      exact Or.inl ⟨rfl, firstHit_unique h firstHit_zero⟩
    by_cases h1 : v = 1
    · subst v
      exact Or.inr (Or.inl ⟨Or.inl rfl, firstHit_unique h firstHit_one⟩)
    by_cases h2 : v = 2
    · subst v
      exact Or.inr (Or.inl ⟨Or.inr rfl, firstHit_unique h firstHit_two⟩)
    obtain ⟨n, hl, hu⟩ := exists_dyadic_interval v (by omega)
    have hu' : v ≤ 6 * 2^n - 1 := by omega
    exact Or.inr (Or.inr ⟨n, hl, hu', firstHit_unique h (firstHit_dyadic n v hl hu')⟩)
  · intro h
    rcases h with ⟨rfl, rfl⟩ | ⟨hsmall, rfl⟩ | ⟨n, hl, hu, rfl⟩
    · exact firstHit_zero
    · rcases hsmall with rfl | rfl
      · exact firstHit_one
      · exact firstHit_two
    · exact firstHit_dyadic n v hl hu

/-- Dyadic powers exceed every prescribed natural threshold. -/
theorem exists_large_dyadic (bound : Nat) : ∃ n, bound < 2^n := by
  refine ⟨bound + 1, ?_⟩
  have h : ∀ n : Nat, n < 2^n := by
    intro n
    induction n with
    | zero => decide
    | succ n ih => rw [Nat.pow_succ]; omega
  have hb := h (bound + 1)
  omega

/-- No rational leading coefficient below 8/3, with any nonnegative rational
additive allowance after a common denominator, bounds all matching maxima. -/
theorem no_smaller_rational_coefficient (a b c : Nat)
    (hsmall : 3 * a < 8 * b) :
    ∃ v ell, 1 ≤ v ∧ IsMaximumLength t t v ell ∧ a * v + c < b * ell := by
  obtain ⟨n, hn⟩ := exists_large_dyadic (3 * b + c)
  have hp := Nat.two_pow_pos n
  have hgap : (3 * a + 1) * 2^n ≤ (8 * b) * 2^n :=
    Nat.mul_le_mul_right _ (by omega)
  have hminus : b * (8 * 2^n - 3) = b * (8 * 2^n) - b * 3 := by
    rw [Nat.mul_sub_left_distrib]
  have hav : a * (3 * 2^n - 1) ≤ a * (3 * 2^n) :=
    Nat.mul_le_mul_left a (by omega)
  refine ⟨3 * 2^n - 1, 8 * 2^n - 3, by omega, sharp_equality_family n, ?_⟩
  rw [Nat.add_mul, Nat.one_mul] at hgap
  rw [hminus]
  simp only [Nat.mul_assoc] at hgap
  have heq1 : 3 * (a * 2^n) = a * (3 * 2^n) := by
    simp only [← Nat.mul_assoc, Nat.mul_comm 3 a]
  have heq2 : 8 * (b * 2^n) = b * (8 * 2^n) := by
    simp only [← Nat.mul_assoc, Nat.mul_comm 8 b]
  omega

end SharpCorollaries
