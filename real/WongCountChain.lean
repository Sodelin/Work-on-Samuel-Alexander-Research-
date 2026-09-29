import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

set_option autoImplicit false
set_option maxHeartbeats 300000

/-! A genuine probability measure on infinite paths of the absorbed Big-ARG
embedded lineage-count chain. State 1 is absorbing. State 0 is a totalization
case sent directly to 1; it is not a biological lineage-count state. -/
namespace WongCountChain
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal BigOperators

noncomputable section

def upProbability (θ : ℝ≥0) (j : ℕ) : ℝ≥0 := θ / (θ + (j + 1))
def downProbability (θ : ℝ≥0) (j : ℕ) : ℝ≥0 := (j + 1) / (θ + (j + 1))

lemma probabilities_sum (θ : ℝ≥0) (j : ℕ) :
    upProbability θ j + downProbability θ j = 1 := by
  unfold upProbability downProbability
  rw [← add_div, div_self]
  positivity

/-- The current count is `j+2` in the nonabsorbed branch. -/
def transition (θ : ℝ≥0) : ℕ → Measure ℕ
  | 0 => Measure.dirac 1
  | 1 => Measure.dirac 1
  | j + 2 => (upProbability θ j : ℝ≥0∞) • Measure.dirac (j + 3) +
      (downProbability θ j : ℝ≥0∞) • Measure.dirac (j + 1)

instance transition_probability (θ : ℝ≥0) (k : ℕ) :
    IsProbabilityMeasure (transition θ k) := by
  constructor
  rcases k with _ | (_ | j)
  · simp [transition]
  · simp [transition]
  · simp only [transition, Measure.add_apply, Measure.smul_apply, measure_univ,
      smul_eq_mul, mul_one, ← ENNReal.coe_add, probabilities_sum, ENNReal.coe_one]

/-- A measurable Markov kernel with exactly the specified two jump outcomes. -/
def jumpKernel (θ : ℝ≥0) : Kernel ℕ ℕ where
  toFun := transition θ
  measurable' := measurable_of_countable _

instance jumpKernel_markov (θ : ℝ≥0) : IsMarkovKernel (jumpKernel θ) :=
  ⟨fun k => transition_probability θ k⟩

@[simp] theorem one_absorbing (θ : ℝ≥0) : jumpKernel θ 1 = Measure.dirac 1 := rfl

theorem jump_up_mass (θ : ℝ≥0) (j : ℕ) :
    jumpKernel θ (j + 2) {j + 3} = upProbability θ j := by
  have hne : j + 1 ≠ j + 3 := by omega
  simp [jumpKernel, transition, hne]

theorem jump_down_mass (θ : ℝ≥0) (j : ℕ) :
    jumpKernel θ (j + 2) {j + 1} = downProbability θ j := by
  have hne : j + 3 ≠ j + 1 := by omega
  simp [jumpKernel, transition, hne]

/-- The transition history kernel depends only on the last recorded count. -/
def historyKernel (θ : ℝ≥0) (t : ℕ) : Kernel (Finset.Iic t → ℕ) ℕ :=
  (jumpKernel θ).comap (fun h => h ⟨t, Finset.mem_Iic.mpr le_rfl⟩) (measurable_pi_apply _)

instance historyKernel_markov (θ : ℝ≥0) (t : ℕ) :
    IsMarkovKernel (historyKernel θ t) := by
  unfold historyKernel
  infer_instance

/-- Ionescu–Tulcea constructs the complete infinite path measure from the
constant initial prefix of length one and the actual transition kernels. -/
def pathLaw (θ : ℝ≥0) (n : ℕ) : Measure (ℕ → ℕ) :=
  Kernel.traj (X := fun _ => ℕ) (historyKernel θ) 0 (fun _ => n)

instance pathLaw_probability (θ : ℝ≥0) (n : ℕ) : IsProbabilityMeasure (pathLaw θ n) := by
  unfold pathLaw
  infer_instance

lemma initial_lintegral (θ : ℝ≥0) (n : ℕ) (f : ℕ → ℝ≥0∞) :
    ∫⁻ ω, f (ω 0) ∂pathLaw θ n = f n := by
  let g : (Finset.Iic 0 → ℕ) → ℝ≥0∞ := fun h => f (h ⟨0, Finset.mem_Iic.mpr le_rfl⟩)
  have hg : Measurable g := (measurable_of_countable f).comp (measurable_pi_apply _)
  change (∫⁻ ω, g (Preorder.frestrictLe 0 ω) ∂pathLaw θ n) = f n
  rw [← lintegral_map hg (by fun_prop)]
  rw [pathLaw, Kernel.traj_map_frestrictLe_apply, Kernel.partialTraj_self]
  simp [Kernel.id_apply, g]

/-- Derived one-step expectation identity for arbitrary nonnegative observables;
this is a theorem about the constructed path measure, not a Markov assumption. -/
theorem step_lintegral (θ : ℝ≥0) (n t : ℕ) (f : ℕ → ℝ≥0∞) :
    ∫⁻ ω, f (ω (t + 1)) ∂pathLaw θ n =
      ∫⁻ ω, ∫⁻ k, f k ∂jumpKernel θ (ω t) ∂pathLaw θ n := by
  let ν := Kernel.partialTraj (X := fun _ => ℕ) (historyKernel θ) 0 t (fun _ => n)
  have hp : (pathLaw θ n).map (Preorder.frestrictLe t) = ν := by
    exact Kernel.traj_map_frestrictLe_apply (X := fun _ : ℕ => ℕ)
      (κ := historyKernel θ) 0 t (fun _ => n)
  have hj : ν ⊗ₘ historyKernel θ t =
      (pathLaw θ n).map (fun ω => (Preorder.frestrictLe t ω, ω (t + 1))) :=
    Kernel.partialTraj_compProd_eq_map_traj (X := fun _ : ℕ => ℕ)
      (κ := historyKernel θ) (Nat.zero_le t)
  let g : ℕ → ℝ≥0∞ := fun s => ∫⁻ k, f k ∂jumpKernel θ s
  calc
    _ = ∫⁻ z, f z.2 ∂((pathLaw θ n).map
        (fun ω => (Preorder.frestrictLe t ω, ω (t + 1)))) := by
      simpa only [Function.comp_def] using (lintegral_map ((measurable_of_countable f).comp measurable_snd)
        (by fun_prop : Measurable (fun ω : ℕ → ℕ =>
          (Preorder.frestrictLe t ω, ω (t + 1))))).symm
    _ = ∫⁻ z, f z.2 ∂(ν ⊗ₘ historyKernel θ t) := by rw [hj]
    _ = ∫⁻ h, g (h ⟨t, Finset.mem_Iic.mpr le_rfl⟩) ∂ν := by
      simpa only [Function.comp_def, g, historyKernel, Kernel.comap_apply] using
        (Measure.lintegral_compProd (μ := ν) (κ := historyKernel θ t)
          ((measurable_of_countable f).comp measurable_snd))
    _ = ∫⁻ ω, g (ω t) ∂pathLaw θ n := by
      rw [← hp]
      have hmeas : Measurable (fun h : Finset.Iic t → ℕ =>
          g (h ⟨t, Finset.mem_Iic.mpr le_rfl⟩)) :=
        (measurable_of_countable g).comp (measurable_pi_apply _)
      simpa only [Preorder.frestrictLe_apply] using
        (lintegral_map (μ := pathLaw θ n) (g := Preorder.frestrictLe t)
          hmeas (Preorder.measurable_frestrictLe t))

lemma transient_lintegral (θ : ℝ≥0) (n t : ℕ) :
    ∫⁻ ω, (if ω t = 1 then 0 else 1 : ℝ≥0∞) ∂pathLaw θ n =
      pathLaw θ n {ω | ω t ≠ 1} := by
  have hm : MeasurableSet {ω : ℕ → ℕ | ω t ≠ 1} := by measurability
  rw [← lintegral_indicator_one hm]
  congr 1
  funext ω
  by_cases h : ω t = 1 <;> simp [Set.indicator, h]

lemma singleton_lintegral (θ : ℝ≥0) (n t c : ℕ) :
    ∫⁻ ω, (if ω t = c then 1 else 0 : ℝ≥0∞) ∂pathLaw θ n =
      pathLaw θ n {ω | ω t = c} := by
  have hm : MeasurableSet {ω : ℕ → ℕ | ω t = c} := by measurability
  rw [← lintegral_indicator_one hm]
  congr 1
  funext ω
  by_cases h : ω t = c <;> simp [Set.indicator, h]

lemma transition_zero_lintegral (θ : ℝ≥0) (k : ℕ) :
    ∫⁻ j, (if j = 0 then 1 else 0 : ℝ≥0∞) ∂jumpKernel θ k = 0 := by
  rcases k with _ | (_ | j) <;> simp [jumpKernel, transition]

lemma state_zero_null (θ : ℝ≥0) (n : ℕ) (hn : n ≠ 0) (t : ℕ) :
    pathLaw θ n {ω | ω t = 0} = 0 := by
  rw [← singleton_lintegral]
  cases t with
  | zero =>
      simpa [hn] using
        (initial_lintegral θ n (fun s => if s = 0 then 1 else 0))
  | succ t =>
      have h := step_lintegral θ n t (fun s => if s = 0 then 1 else 0)
      simpa only [transition_zero_lintegral, lintegral_zero] using h

/-- Positive initial counts remain positive at every jump almost surely, so the
natural-number zero totalization is never visited by the modeled chain. -/
theorem ae_positive_counts (θ : ℝ≥0) (n : ℕ) (hn : n ≠ 0) :
    ∀ᵐ ω ∂pathLaw θ n, ∀ t, 0 < ω t := by
  rw [ae_all_iff]
  intro t
  rw [ae_iff]
  simpa only [not_lt, nonpos_iff_eq_zero] using state_zero_null θ n hn t

/-- A finite Lyapunov drift bound implies summable nonabsorption probabilities
for the actual constructed chain. No expected-time premise is assumed. -/
theorem sum_transient_le (θ : ℝ≥0) (n : ℕ) (V : ℕ → ℝ≥0∞)
    (drift : ∀ k, (∫⁻ j, V j ∂jumpKernel θ k) +
      (if k = 1 then 0 else 1) ≤ V k) :
    (∑' t, pathLaw θ n {ω | ω t ≠ 1}) ≤ V n := by
  let moment : ℕ → ℝ≥0∞ := fun t => ∫⁻ ω, V (ω t) ∂pathLaw θ n
  let cost : ℕ → ℝ≥0∞ := fun t => pathLaw θ n {ω | ω t ≠ 1}
  have hstep : ∀ t, moment (t + 1) + cost t ≤ moment t := by
    intro t
    dsimp only [moment, cost]
    rw [step_lintegral, ← transient_lintegral]
    have hm : Measurable (fun ω : ℕ → ℕ => ∫⁻ j, V j ∂jumpKernel θ (ω t)) :=
      (measurable_of_countable (fun s : ℕ => ∫⁻ j, V j ∂jumpKernel θ s)).comp
        (measurable_pi_apply t)
    rw [← lintegral_add_left hm]
    exact lintegral_mono (fun ω => drift (ω t))
  have bound : ∀ T, moment T + ∑ t ∈ Finset.range T, cost t ≤ V n := by
    intro T
    induction T with
    | zero => simpa [moment] using (le_of_eq (initial_lintegral θ n V))
    | succ T ih =>
      rw [Finset.sum_range_succ]
      calc
        moment (T + 1) + ((∑ t ∈ Finset.range T, cost t) + cost T) =
            (moment (T + 1) + cost T) + ∑ t ∈ Finset.range T, cost t := by ac_rfl
        _ ≤ moment T + ∑ t ∈ Finset.range T, cost t := add_le_add (hstep T) (le_refl _)
        _ ≤ V n := ih
  apply ENNReal.tsum_le_of_sum_range_le
  intro T
  calc
    (∑ t ∈ Finset.range T, cost t) = 0 + ∑ t ∈ Finset.range T, cost t := by simp
    _ ≤ moment T + ∑ t ∈ Finset.range T, cost t := add_le_add (bot_le : 0 ≤ moment T) (le_refl _)
    _ ≤ V n := bound T

/-- Probability semantics: under derived finite drift, almost every infinite
trajectory reaches count one at a finite jump index (indeed is eventually one). -/
theorem ae_finite_absorption_of_drift (θ : ℝ≥0) (n : ℕ) (V : ℕ → ℝ≥0∞)
    (finite : V n ≠ ∞)
    (drift : ∀ k, (∫⁻ j, V j ∂jumpKernel θ k) +
      (if k = 1 then 0 else 1) ≤ V k) :
    ∀ᵐ ω ∂pathLaw θ n, ∃ T : ℕ, ∀ t ≥ T, ω t = 1 := by
  have hs : (∑' t, pathLaw θ n {ω | ω t ≠ 1}) ≠ ∞ :=
    ne_top_of_le_ne_top finite (sum_transient_le θ n V drift)
  have he := MeasureTheory.ae_eventually_notMem hs
  filter_upwards [he] with ω hω
  simpa only [Set.mem_setOf_eq, not_not, Filter.eventually_atTop] using hω

/-- Clock-scale invariant conversion from literal split/merge rates. -/
theorem literal_rate_ratio (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (k : ℕ) (hk : 2 ≤ k) :
    (b * k) / (b * k + a * k * ((k : ℝ) - 1) / 2) =
      (2 * b / a) / (2 * b / a + (k : ℝ) - 1) := by
  have hkr : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  have hkpred : 0 < (k : ℝ) - 1 := by linarith
  have hbpart : 0 ≤ b * k := mul_nonneg hb (le_of_lt hkpos)
  have hdeath : 0 < a * k * ((k : ℝ) - 1) / 2 := by positivity
  have htotal : 0 < b * k + a * k * ((k : ℝ) - 1) / 2 := by linarith
  have hrnonneg : 0 ≤ 2 * b / a := by positivity
  have hden : 0 < 2 * b / a + (k : ℝ) - 1 := by linarith
  apply (div_eq_div_iff (ne_of_gt htotal) (ne_of_gt hden)).mpr
  field_simp [ne_of_gt ha]
  <;> ring

/-- The downward jump probability for the same literal rate pair. -/
theorem literal_merger_ratio (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (k : ℕ) (hk : 2 ≤ k) :
    (a * k * ((k : ℝ) - 1) / 2) / (b * k + a * k * ((k : ℝ) - 1) / 2) =
      ((k : ℝ) - 1) / (2 * b / a + (k : ℝ) - 1) := by
  have hkr : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  have hkpred : 0 < (k : ℝ) - 1 := by linarith
  have hbpart : 0 ≤ b * k := mul_nonneg hb (le_of_lt hkpos)
  have hdeath : 0 < a * k * ((k : ℝ) - 1) / 2 := by positivity
  have htotal : 0 < b * k + a * k * ((k : ℝ) - 1) / 2 := by linarith
  have hrnonneg : 0 ≤ 2 * b / a := by positivity
  have hden : 0 < 2 * b / a + (k : ℝ) - 1 := by linarith
  apply (div_eq_div_iff (ne_of_gt htotal) (ne_of_gt hden)).mpr
  field_simp [ne_of_gt ha]
  <;> ring

#print axioms one_absorbing
#print axioms jump_up_mass
#print axioms jump_down_mass
#print axioms initial_lintegral
#print axioms step_lintegral
#print axioms ae_positive_counts
#print axioms sum_transient_le
#print axioms ae_finite_absorption_of_drift
#print axioms literal_rate_ratio
#print axioms literal_merger_ratio
end
end WongCountChain
