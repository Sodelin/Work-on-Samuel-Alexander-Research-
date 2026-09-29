import WongCountChain
import WongBigARGDrift

set_option autoImplicit false

/-! Connect the explicitly derived finite potential to the actual Big-ARG path
measure. This proves almost-sure finite jump absorption, not an expected-event
formula, a continuous-time holding-time construction, or a marked spatial ARG. -/
namespace WongBigARGAbsorption
open MeasureTheory ProbabilityTheory WongCountChain WongBigARGDrift
open scoped ENNReal NNReal
noncomputable section

/-- The natural-number zero case is only a harmless totalization of the count
kernel; its potential is one because its next state is the absorbed state one. -/
def countPotential (N : ℕ) : ℕ → ℝ≥0
  | 0 => 1
  | j + 1 => ⟨potential N j, potential_nonneg N j⟩

lemma countPotential_drift_nn (θ : ℝ≥0) (N : ℕ) (hN : (θ : ℝ) ≤ N) (j : ℕ) :
    upProbability θ j * countPotential N (j + 3) +
      downProbability θ j * countPotential N (j + 1) + 1 ≤ countPotential N (j + 2) := by
  apply NNReal.coe_le_coe.mp
  have h := potential_drift (θ : ℝ) θ.coe_nonneg N hN (j + 1) (by omega)
  change (upProbability θ j : ℝ) * potential N (j + 2) +
    (downProbability θ j : ℝ) * potential N j + 1 ≤ potential N (j + 1)
  simpa [upProbability, downProbability, Nat.add_assoc] using h

@[simp] lemma countPotential_zero (N : ℕ) : countPotential N 0 = 1 := rfl

@[simp] lemma countPotential_one (N : ℕ) : countPotential N 1 = 0 := by
  apply Subtype.ext
  simp [countPotential, potential_zero]

/-- Verified finite drift for the actual two-point transition measure. -/
theorem countPotential_drift (θ : ℝ≥0) (N : ℕ) (hN : (θ : ℝ) ≤ N) (k : ℕ) :
    (∫⁻ j, (countPotential N j : ℝ≥0∞) ∂jumpKernel θ k) +
      (if k = 1 then 0 else 1) ≤ countPotential N k := by
  rcases k with _ | (_ | j)
  · simp [jumpKernel, transition]
  · simp [jumpKernel, transition]
  · have h := countPotential_drift_nn θ N hN j
    have hk : j + 2 ≠ 1 := by omega
    simp only [hk, if_false]
    change (∫⁻ k, (countPotential N k : ℝ≥0∞) ∂transition θ (j + 2)) + 1 ≤ _
    simp only [transition, lintegral_add_measure, lintegral_smul_measure,
      lintegral_dirac, smul_eq_mul]
    exact_mod_cast h

/-- Almost every path of the constructed embedded count chain is eventually
absorbed at one. The finite Lyapunov witness is constructed for every ratio. -/
theorem ae_eventually_one (θ : ℝ≥0) (n : ℕ) :
    ∀ᵐ ω ∂pathLaw θ n, ∃ T : ℕ, ∀ t ≥ T, ω t = 1 := by
  obtain ⟨N, hN⟩ := exists_nat_ge (θ : ℝ)
  exact ae_finite_absorption_of_drift θ n (fun k => countPotential N k)
    (ENNReal.coe_ne_top) (countPotential_drift θ N hN)

/-- Finite jump absorption, with no recurrence or absorption hypothesis. -/
theorem ae_finite_jump_absorption (θ : ℝ≥0) (n : ℕ) :
    ∀ᵐ ω ∂pathLaw θ n, ∃ T : ℕ, ω T = 1 := by
  filter_upwards [ae_eventually_one θ n] with ω hω
  obtain ⟨T, hT⟩ := hω
  exact ⟨T, hT T le_rfl⟩

/-- Explicit normalization; the merger scale is positive and the split scale
nonnegative. Multiplying both by the same positive clock scale leaves it fixed. -/
def normalizedRatio (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) : ℝ≥0 :=
  ⟨2 * b / a, div_nonneg (mul_nonneg (by norm_num) hb) (le_of_lt ha)⟩

@[simp] theorem normalizedRatio_value (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) :
    (normalizedRatio a b ha hb : ℝ) = 2 * b / a := rfl

/-- The actual upward singleton mass, converted to a real probability, agrees
with the literal split rate divided by the total event rate. -/
theorem literal_up_kernel_mass (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (j : ℕ) :
    (jumpKernel (normalizedRatio a b ha hb) (j + 2) {j + 3}).toReal =
      (b * (j + 2)) / (b * (j + 2) + a * (j + 2) * ((j + 2 : ℝ) - 1) / 2) := by
  rw [jump_up_mass, ENNReal.coe_toReal]
  have hnorm : (upProbability (normalizedRatio a b ha hb) j : ℝ) =
      (2 * b / a) / (2 * b / a + ((j + 2 : ℕ) : ℝ) - 1) := by
    simp only [upProbability, NNReal.coe_div, NNReal.coe_add, NNReal.coe_natCast,
      normalizedRatio_value]
    congr 1 <;> push_cast <;> ring
  calc
    (upProbability (normalizedRatio a b ha hb) j : ℝ) = _ := hnorm
    _ = _ := by
      simpa only [Nat.cast_add, Nat.cast_ofNat] using
        (literal_rate_ratio a b ha hb (j + 2) (by omega)).symm

/-- The actual downward singleton mass agrees with the literal merger rate
ratio. Together with `transition`, this identifies the full two-outcome kernel. -/
theorem literal_down_kernel_mass (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (j : ℕ) :
    (jumpKernel (normalizedRatio a b ha hb) (j + 2) {j + 1}).toReal =
      (a * (j + 2) * ((j + 2 : ℝ) - 1) / 2) /
        (b * (j + 2) + a * (j + 2) * ((j + 2 : ℝ) - 1) / 2) := by
  rw [jump_down_mass, ENNReal.coe_toReal]
  have hnorm : (downProbability (normalizedRatio a b ha hb) j : ℝ) =
      (((j + 2 : ℕ) : ℝ) - 1) /
        (2 * b / a + ((j + 2 : ℕ) : ℝ) - 1) := by
    simp only [downProbability, NNReal.coe_div, NNReal.coe_add, NNReal.coe_natCast,
      normalizedRatio_value]
    congr 1 <;> push_cast <;> ring
  calc
    (downProbability (normalizedRatio a b ha hb) j : ℝ) = _ := hnorm
    _ = _ := by
      simpa only [Nat.cast_add, Nat.cast_ofNat] using
        (literal_merger_ratio a b ha hb (j + 2) (by omega)).symm

/-- Source-rate specialization for every initial count `n+2`. The imported
literal_rate_ratio proves these are the embedded probabilities of
lambda_k=b*k and mu_k=a*k*(k-1)/2, with theta=2*b/a. -/
theorem literal_rates_ae_finite_absorption (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (n : ℕ) :
    ∀ᵐ ω ∂pathLaw (normalizedRatio a b ha hb) (n + 2), ∃ T : ℕ, ω T = 1 :=
  ae_finite_jump_absorption (normalizedRatio a b ha hb) (n + 2)

#print axioms countPotential_drift
#print axioms ae_eventually_one
#print axioms ae_finite_jump_absorption
#print axioms normalizedRatio_value
#print axioms literal_up_kernel_mass
#print axioms literal_down_kernel_mass
#print axioms literal_rates_ae_finite_absorption
end
end WongBigARGAbsorption
