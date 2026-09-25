import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-! A finite, explicit Lyapunov potential for the Big-ARG embedded count chain.
This file is algebra only. Probability semantics are supplied separately. -/
namespace WongBigARGDrift
open scoped BigOperators

/-- A finite cutoff above the branching ratio. -/
def base (N : ℕ) : ℝ := 2 * (N : ℝ) + 2

def weight (N j : ℕ) : ℝ := (base N) ^ (3 * N + 1 - j)

/-- `j` is the excess lineage count, so the absorbed count one has `j = 0`. -/
def potential (N j : ℕ) : ℝ := base N * ∑ i ∈ Finset.range j, weight N (i + 1)

lemma base_ge_two (N : ℕ) : 2 ≤ base N := by
  unfold base
  have h : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  linarith
lemma base_pos (N : ℕ) : 0 < base N := lt_of_lt_of_le (by norm_num) (base_ge_two N)
lemma weight_ge_one (N j : ℕ) : 1 ≤ weight N j := by
  exact one_le_pow₀ (by have := base_ge_two N; linarith)
lemma weight_nonneg (N j : ℕ) : 0 ≤ weight N j := le_trans (by norm_num) (weight_ge_one N j)
lemma potential_nonneg (N j : ℕ) : 0 ≤ potential N j := by
  unfold potential
  exact mul_nonneg (le_of_lt (base_pos N)) (Finset.sum_nonneg (fun i _ => weight_nonneg N (i + 1)))
@[simp] lemma potential_zero (N : ℕ) : potential N 0 = 0 := by simp [potential]
lemma potential_succ (N j : ℕ) :
    potential N (j + 1) = potential N j + base N * weight N (j + 1) := by
  simp [potential, Finset.sum_range_succ, mul_add]

lemma weight_low (N j : ℕ) (hj : j < 3 * N + 1) :
    weight N j = base N * weight N (j + 1) := by
  unfold weight
  have h : 3 * N + 1 - j = (3 * N + 1 - (j + 1)) + 1 := by omega
  rw [h, pow_succ, mul_comm]

lemma weight_high (N j : ℕ) (hj : 3 * N + 1 ≤ j) : weight N j = 1 := by
  simp [weight, Nat.sub_eq_zero_of_le hj]

/-- The downward weighted increment dominates the upward one by at least the
jump-probability denominator. This finite potential works also at ratio zero. -/
lemma weighted_gap (θ : ℝ) (hθ : 0 ≤ θ) (N : ℕ) (hN : θ ≤ N)
    (j : ℕ) (hj : 1 ≤ j) :
    θ + j ≤ base N * ((j : ℝ) * weight N j - θ * weight N (j + 1)) := by
  have hjr : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hNr : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hb := base_ge_two N
  have hden : 0 ≤ θ + j := by positivity
  by_cases hlo : j < 3 * N + 1
  · rw [weight_low N j hlo]
    have hprod : (0 : ℝ) ≤ ((j : ℝ) - 1) * N := mul_nonneg (by linarith) hNr
    have hgap : θ + j ≤ (j : ℝ) * base N - θ := by
      dsimp [base]
      nlinarith
    have hg0 : 0 ≤ (j : ℝ) * base N - θ := le_trans hden hgap
    have hw := weight_ge_one N (j + 1)
    have hmul : (j : ℝ) * base N - θ ≤
        ((j : ℝ) * base N - θ) * weight N (j + 1) :=
      le_mul_of_one_le_right hg0 hw
    have hmul0 : 0 ≤ ((j : ℝ) * base N - θ) * weight N (j + 1) :=
      mul_nonneg hg0 (weight_nonneg N (j + 1))
    have hbmul : ((j : ℝ) * base N - θ) * weight N (j + 1) ≤
        base N * (((j : ℝ) * base N - θ) * weight N (j + 1)) :=
      le_mul_of_one_le_left hmul0 (by linarith)
    nlinarith
  · have hhi : 3 * N + 1 ≤ j := by omega
    rw [weight_high N j hhi, weight_high N (j + 1) (by omega)]
    have hjhigh : (3 : ℝ) * N + 1 ≤ j := by exact_mod_cast hhi
    have hdiff : 0 ≤ (j : ℝ) - θ := by linarith
    have hmul : 2 * ((j : ℝ) - θ) ≤ base N * ((j : ℝ) - θ) :=
      mul_le_mul_of_nonneg_right hb hdiff
    nlinarith

/-- Actual negative drift for the two possible next excess counts. -/
theorem potential_drift (θ : ℝ) (hθ : 0 ≤ θ) (N : ℕ) (hN : θ ≤ N)
    (j : ℕ) (hj : 1 ≤ j) :
    (θ / (θ + j)) * potential N (j + 1) +
      ((j : ℝ) / (θ + j)) * potential N (j - 1) + 1 ≤ potential N j := by
  have hden : 0 < θ + j := by
    have hjr : (1 : ℝ) ≤ j := by exact_mod_cast hj
    linarith
  have hback := potential_succ N (j - 1)
  have heq : j - 1 + 1 = j := by omega
  rw [heq] at hback
  rw [potential_succ]
  have hgap := weighted_gap θ hθ N hN j hj
  apply (mul_le_mul_iff_left₀ hden).mp
  calc
    (θ / (θ + j) * (potential N j + base N * weight N (j + 1)) +
        (j : ℝ) / (θ + j) * potential N (j - 1) + 1) * (θ + j)
        = θ * (potential N j + base N * weight N (j + 1)) +
          (j : ℝ) * potential N (j - 1) + (θ + j) := by
            field_simp [ne_of_gt hden]
            <;> ring
    _ ≤ potential N j * (θ + j) := by nlinarith

#print axioms weighted_gap
#print axioms potential_drift
end WongBigARGDrift
