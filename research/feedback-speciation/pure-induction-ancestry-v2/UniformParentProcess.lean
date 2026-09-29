import ParentSchedules
import UniformParentCounting
import FeedbackDynamics
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Distributions.Uniform

/-!
A genuine infinite product probability measure for independent uniform parent
tables. Finite avoidance probabilities imply almost-sure genealogical IAP.
This is a fixed-population reference model, not an adaptive biological kernel.
-/
open MeasureTheory Set
open scoped ENNReal
namespace UniformParentProcess

noncomputable section

variable {A : Type*} [Fintype A] [Nonempty A]
  [MeasurableSpace A] [MeasurableSingletonClass A]

def oneStep (A : Type*) [Fintype A] [Nonempty A] [MeasurableSpace A] : Measure A :=
  (PMF.uniformOfFintype A).toMeasure

instance oneStep_probability : IsProbabilityMeasure (oneStep A) := by
  unfold oneStep
  infer_instance

def streamLaw (A : Type*) [Fintype A] [Nonempty A] [MeasurableSpace A] :
    Measure (Nat → A) := Measure.infinitePi (fun _ : Nat => oneStep A)

instance streamLaw_probability : IsProbabilityMeasure (streamLaw A) := by
  unfold streamLaw
  infer_instance

def missRate (A : Type*) [Fintype A] : ℝ :=
  ((Fintype.card A : ℝ)-1)/(Fintype.card A : ℝ)

omit [MeasurableSpace A] [MeasurableSingletonClass A] in
theorem missRate_bounds : 0 ≤ missRate A ∧ missRate A < 1 := by
  have hp : (0:ℝ) < Fintype.card A := Nat.cast_pos.mpr Fintype.card_pos
  have h1 : (1:ℝ) ≤ Fintype.card A := by exact_mod_cast Fintype.card_pos
  constructor
  · exact div_nonneg (by linarith) hp.le
  · exact (div_lt_one hp).mpr (by linarith)

theorem oneStep_singleton (a : A) :
    oneStep A {a} = (Fintype.card A : ℝ≥0∞)⁻¹ := by
  rw [oneStep,PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton a),
    PMF.uniformOfFintype_apply]

theorem oneStep_compl_singleton (a : A) :
    oneStep A ({a}ᶜ) = ENNReal.ofReal (missRate A) := by
  have hp : (0:ℝ) < Fintype.card A := Nat.cast_pos.mpr Fintype.card_pos
  have h1 : (1:ℝ) ≤ Fintype.card A := by exact_mod_cast Fintype.card_pos
  have heq : missRate A = 1 - 1/(Fintype.card A : ℝ) := by
    unfold missRate
    field_simp
  rw [prob_compl_eq_one_sub (measurableSet_singleton a),oneStep_singleton,heq,
    ENNReal.ofReal_sub 1 (by positivity : (0:ℝ) ≤ 1/(Fintype.card A : ℝ))]
  simp [ENNReal.ofReal_inv_of_pos hp]

def Avoid (a : A) (start len : Nat) : Set (Nat → A) :=
  Set.pi (Finset.Ico start (start+len)) (fun _ => ({a}ᶜ))

theorem avoidance_exact (a : A) (start len : Nat) :
    streamLaw A (Avoid a start len) = ENNReal.ofReal ((missRate A)^len) := by
  unfold streamLaw Avoid
  rw [Measure.infinitePi_pi _ (fun _ _ => (measurableSet_singleton a).compl)]
  simp only [oneStep_compl_singleton,Finset.prod_const,Nat.card_Ico,
    Nat.add_sub_cancel_left,ENNReal.ofReal_pow (missRate_bounds (A := A)).1]

theorem measure_zero_of_geometric_bounds {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Set Ω) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (h : ∀ n : Nat, μ S ≤ ENNReal.ofReal (r^n)) : μ S = 0 := by
  apply le_antisymm ?_ (show (0:ℝ≥0∞) ≤ μ S from bot_le)
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  have hεr : (0:ℝ) < ε := hε
  obtain ⟨n,hn⟩ := FeedbackDynamics.geometric_epsilon_limit hr0 hr1
    (show (0:ℝ) ≤ 1 by norm_num) (ε : ℝ) hεr
  have hpow : r^n < (ε : ℝ) := by simpa using hn n (Nat.le_refl n)
  have hb := (h n).trans (ENNReal.ofReal_le_ofReal hpow.le)
  simpa using hb

def ForeverAvoid (a : A) (start : Nat) : Set (Nat → A) :=
  {ω | ∀ n, start ≤ n → ω n ≠ a}

theorem forever_avoid_null (a : A) (start : Nat) :
    streamLaw A (ForeverAvoid a start) = 0 := by
  apply measure_zero_of_geometric_bounds _ _ (missRate_bounds (A := A)).1
    (missRate_bounds (A := A)).2
  intro len
  rw [← avoidance_exact a start len]
  apply measure_mono
  intro ω hω
  change ∀ n ∈ Finset.Ico start (start+len), ω n ∈ ({a}ᶜ : Set A)
  intro n hn
  exact hω n (Finset.mem_Ico.mp hn).1

theorem ae_recurrent (a : A) :
    ∀ᵐ ω ∂streamLaw A, ∀ start, ∃ n, start ≤ n ∧ ω n = a := by
  have hn : ∀ start, ∀ᵐ ω ∂streamLaw A, ω ∉ ForeverAvoid a start := by
    intro start
    rw [ae_iff]
    simpa using forever_avoid_null a start
  have hall := ae_all_iff.mpr hn
  filter_upwards [hall] with ω hω
  intro start
  by_contra hn
  apply hω start
  intro n hstart heq
  exact hn ⟨n,hstart,heq⟩

def designatedPair {N : Nat} (hN : 2 ≤ N) : Fin 2 → Fin N :=
  fun slot => ⟨slot.val,lt_of_lt_of_le slot.isLt hN⟩

theorem designated_table_is_constant {N : Nat} (hN : 2 ≤ N) :
    UniformParentCounting.designatedTable hN =
      ParentSchedules.constantTable (designatedPair hN) := rfl

theorem missRate_parent_tables {N : Nat} (hN : 2 ≤ N) :
    missRate (ParentSchedules.Table N) = 1 - 1/(N : ℝ)^(2*N) := by
  unfold missRate
  rw [UniformParentCounting.card_parent_tables]
  simp only [UniformParentCounting.tableCount, Nat.cast_pow]
  have hp : (0:ℝ) < (N : ℝ)^(2*N) :=
    pow_pos (Nat.cast_pos.mpr (by omega)) _
  field_simp

theorem uniform_parenthood_ae_iap {N : Nat} (hN : 2 ≤ N) :
    letI : Nonempty (ParentSchedules.Table N) :=
      ⟨UniformParentCounting.designatedTable hN⟩
    ∀ᵐ p ∂streamLaw (ParentSchedules.Table N),
      SpeciesBridge.IAP (ParentSchedules.model N (by omega) p).edge SpeciesBridge.Whole := by
  letI : Nonempty (ParentSchedules.Table N) :=
    ⟨UniformParentCounting.designatedTable hN⟩
  filter_upwards [ae_recurrent (UniformParentCounting.designatedTable hN)] with p hp
  apply ParentSchedules.recurrent_constant_table_iap N (by omega) p (designatedPair hN)
  simpa only [designated_table_is_constant] using hp

theorem unresolved_probability_bound {N : Nat} (hN : 2 ≤ N) (u len : Nat) :
    letI : Nonempty (ParentSchedules.Table N) :=
      ⟨UniformParentCounting.designatedTable hN⟩
    streamLaw (ParentSchedules.Table N)
      {p | ¬ (ParentSchedules.model N (by omega) p).ResolvedFrom u (u/N+1+len)}
      ≤ ENNReal.ofReal ((missRate (ParentSchedules.Table N))^len) := by
  letI : Nonempty (ParentSchedules.Table N) :=
    ⟨UniformParentCounting.designatedTable hN⟩
  rw [← avoidance_exact (UniformParentCounting.designatedTable hN) (u/N+1) len]
  apply measure_mono
  intro p hp
  change ∀ t ∈ Finset.Ico (u/N+1) (u/N+1+len),
    p t ∈ ({UniformParentCounting.designatedTable hN}ᶜ : Set (ParentSchedules.Table N))
  intro t ht heq
  have ht' := Finset.mem_Ico.mp ht
  have hres := ParentSchedules.constant_table_resolves_older N (by omega) p t u
    (designatedPair hN) (by simpa only [designated_table_is_constant] using (Set.mem_singleton_iff.mp heq)) (by omega)
  apply hp
  rcases hres with hn | ha
  · exact Or.inl (fun v hv => hn v (by omega))
  · exact Or.inr (fun v hv => ha v (by omega))

end
end UniformParentProcess
#print axioms UniformParentProcess.oneStep_singleton
#print axioms UniformParentProcess.avoidance_exact
#print axioms UniformParentProcess.measure_zero_of_geometric_bounds
#print axioms UniformParentProcess.forever_avoid_null
#print axioms UniformParentProcess.ae_recurrent
#print axioms UniformParentProcess.uniform_parenthood_ae_iap
#print axioms UniformParentProcess.unresolved_probability_bound

#print axioms UniformParentProcess.missRate_parent_tables
