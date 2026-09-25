import WongBigARGAbsorption
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.CDF
import Mathlib.Data.Nat.Find
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option autoImplicit false

/-! Timed, stopped embedded Big-ARG count paths. This file adds independent
unit-exponential innovations to the previously checked count-path law. It does
not assert a spatial ARG projection or a full real-time Markov process. -/
namespace WongWaitingTimes
open MeasureTheory ProbabilityTheory WongCountChain WongBigARGAbsorption Finset
open scoped ENNReal NNReal BigOperators Classical
noncomputable section

abbrev CountPath := ℕ → ℕ
abbrev ClockPath := ℕ → ℝ
abbrev Sample := CountPath × ClockPath

/-- Literal total event intensity at a transient lineage count. -/
def totalRate (a b : ℝ) (k : ℕ) : ℝ :=
  b * k + a * k * ((k : ℝ) - 1) / 2

theorem totalRate_pos (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (k : ℕ) (hk : 2 ≤ k) : 0 < totalRate a b k := by
  have hkr : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hk1 : (0 : ℝ) < (k : ℝ) - 1 := by linarith
  have hm : 0 < a * k * ((k : ℝ) - 1) / 2 := by positivity
  have hs : 0 ≤ b * (k : ℝ) := mul_nonneg hb hk0.le
  unfold totalRate
  linarith

/-- Unconditioned innovations; all rate dependence enters through scaling. -/
def unitClockLaw : Measure ClockPath :=
  Measure.infinitePi (fun _ : ℕ => expMeasure 1)

private instance unitExpProbability : IsProbabilityMeasure (expMeasure (1 : ℝ)) :=
  isProbabilityMeasure_expMeasure (by norm_num)


instance unitClockLaw_probability : IsProbabilityMeasure unitClockLaw := by
  unfold unitClockLaw
  infer_instance

/-- The actual joint law couples the checked count trajectory to independent
unit-rate exponential innovations by an ordinary product measure. -/
def jointLaw (θ : ℝ≥0) (n : ℕ) : Measure Sample :=
  (pathLaw θ n).prod unitClockLaw

instance jointLaw_probability (θ : ℝ≥0) (n : ℕ) : IsProbabilityMeasure (jointLaw θ n) := by
  unfold jointLaw
  infer_instance

theorem joint_count_marginal (θ : ℝ≥0) (n : ℕ) :
    (jointLaw θ n).map Prod.fst = pathLaw θ n := by
  simpa only [jointLaw] using
    (measurePreserving_fst (μ := pathLaw θ n) (ν := unitClockLaw)).map_eq

theorem joint_clock_marginal (θ : ℝ≥0) (n : ℕ) :
    (jointLaw θ n).map Prod.snd = unitClockLaw := by
  simpa only [jointLaw] using
    (measurePreserving_snd (μ := pathLaw θ n) (ν := unitClockLaw)).map_eq

theorem unit_clock_marginal (i : ℕ) :
    unitClockLaw.map (fun E => E i) = expMeasure 1 := by
  exact Measure.infinitePi_map_eval (fun _ : ℕ => expMeasure 1) i

/-- The entire clock-innovation path is independent of the entire count path. -/
theorem count_clock_independent (θ : ℝ≥0) (n : ℕ) :
    (fun z : Sample => z.1) ⟂ᵢ[jointLaw θ n] (fun z : Sample => z.2) := by
  simpa only [jointLaw, id_eq] using
    (indepFun_prod (μ := pathLaw θ n) (ν := unitClockLaw)
      (X := id) (Y := id) measurable_id measurable_id)

/-- The clock innovations are independent across all natural indices. -/
theorem unit_clocks_independent :
    iIndepFun (fun i (E : ClockPath) => E i) unitClockLaw := by
  exact iIndepFun_infinitePi (P := fun _ : ℕ => expMeasure 1)
    (X := fun (_ : ℕ) (x : ℝ) => x) (fun _ => measurable_id)

/-- Path reaches the absorbing count one at some finite jump index. -/
def hitsOne (K : CountPath) : Prop := ∃ t : ℕ, K t = 1

private noncomputable instance : DecidablePred hitsOne := Classical.decPred _

private def hitCandidate (K : CountPath) (t : ℕ) : Prop :=
  K t = 1 ∨ (t = 0 ∧ ¬hitsOne K)

private noncomputable instance (K : CountPath) : DecidablePred (hitCandidate K) :=
  Classical.decPred _

private theorem hitCandidate_exists (K : CountPath) : ∃ t, hitCandidate K t := by
  classical
  by_cases h : hitsOne K
  · obtain ⟨t, ht⟩ := h
    exact ⟨t, Or.inl ht⟩
  · exact ⟨0, Or.inr ⟨rfl, h⟩⟩

/-- First absorbing index, totalized to zero on a nonhitting path. The
physical time below assigns infinity to that separate nonhitting case. -/
def firstHit (K : CountPath) : ℕ := Nat.find (hitCandidate_exists K)

theorem firstHit_spec (K : CountPath) (h : hitsOne K) : K (firstHit K) = 1 := by
  have hs : hitCandidate K (firstHit K) := Nat.find_spec (hitCandidate_exists K)
  rcases hs with hs | ⟨_, hn⟩
  · exact hs
  · exact False.elim (hn h)

theorem firstHit_min (K : CountPath) (h : hitsOne K) {i : ℕ}
    (hi : i < firstHit K) : K i ≠ 1 := by
  intro he
  exact Nat.find_min (hitCandidate_exists K) hi (Or.inl he)

theorem measurableSet_hitsOne : MeasurableSet {K : CountPath | hitsOne K} := by
  have h : {K : CountPath | hitsOne K} = ⋃ t : ℕ, {K | K t = 1} := by
    ext K
    simp [hitsOne]
  rw [h]
  exact MeasurableSet.iUnion (fun _ => by measurability)

private theorem measurableSet_hitCandidate (t : ℕ) :
    MeasurableSet {K : CountPath | hitCandidate K t} := by
  have h1 : MeasurableSet {K : CountPath | K t = 1} := by measurability
  have h2 : MeasurableSet {K : CountPath | t = 0 ∧ ¬hitsOne K} := by
    by_cases ht : t = 0
    · simp only [ht, true_and]
      convert measurableSet_hitsOne.compl using 1
      ext K
      simp
    · simp [ht]
  have heq : {K : CountPath | hitCandidate K t} =
      {K | K t = 1} ∪ {K | t = 0 ∧ ¬hitsOne K} := rfl
  rw [heq]
  exact h1.union h2

theorem measurable_firstHit : Measurable firstHit := by
  classical
  exact measurable_find hitCandidate_exists measurableSet_hitCandidate

/-- A raw wait is used only at a count at least two. Real division at zero
outside the admitted pre-hit states is only a totalization. -/
def rawWait (a b : ℝ) (z : Sample) (i : ℕ) : ℝ :=
  z.2 i / totalRate a b (z.1 i)

/-- There is no event and no wait at or after the first hit. -/
def stoppedWait (a b : ℝ) (z : Sample) (i : ℕ) : ℝ :=
  if hitsOne z.1 ∧ i < firstHit z.1 then rawWait a b z i else 0

/-- Finite event-time prefix; waits after the first hit contribute zero. -/
def eventTime (a b : ℝ) (z : Sample) (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range j, stoppedWait a b z i

@[simp] theorem eventTime_zero (a b : ℝ) (z : Sample) : eventTime a b z 0 = 0 := by
  simp [eventTime]

theorem eventTime_succ (a b : ℝ) (z : Sample) (j : ℕ) :
    eventTime a b z (j + 1) = eventTime a b z j + stoppedWait a b z j := by
  simp [eventTime, Finset.sum_range_succ]

theorem measurable_rawWait (a b : ℝ) (i : ℕ) :
    Measurable (fun z : Sample => rawWait a b z i) := by
  unfold rawWait totalRate
  fun_prop

theorem measurable_stoppedWait (a b : ℝ) (i : ℕ) :
    Measurable (fun z : Sample => stoppedWait a b z i) := by
  have hh : MeasurableSet {z : Sample | hitsOne z.1} :=
    measurableSet_hitsOne.preimage measurable_fst
  have ht : MeasurableSet {z : Sample | i < firstHit z.1} :=
    measurableSet_lt measurable_const (measurable_firstHit.comp measurable_fst)
  unfold stoppedWait
  exact Measurable.ite (hh.inter ht) (measurable_rawWait a b i) measurable_const

theorem measurable_eventTime (a b : ℝ) (j : ℕ) :
    Measurable (fun z : Sample => eventTime a b z j) := by
  unfold eventTime
  exact Finset.measurable_sum _ (fun i _ => measurable_stoppedWait a b i)

/-- A finite prefix sum of nonnegative extended-real wait lengths. -/
def prefixDuration (a b : ℝ) (z : Sample) (j : ℕ) : ℝ≥0∞ :=
  ∑ i ∈ Finset.range j, ENNReal.ofReal (stoppedWait a b z i)

theorem measurable_prefixDuration (a b : ℝ) (j : ℕ) :
    Measurable (fun z : Sample => prefixDuration a b z j) := by
  unfold prefixDuration
  exact Finset.measurable_sum _ (fun i _ =>
    ENNReal.measurable_ofReal.comp (measurable_stoppedWait a b i))

/-- Nonhitting paths have infinite physical stopping time. The supremum selects
exactly one finite prefix on a hitting path and makes measurability explicit. -/
def physicalAbsorptionTime (a b : ℝ) (z : Sample) : ℝ≥0∞ :=
  if hitsOne z.1 then
    ⨆ j : ℕ, if firstHit z.1 = j then prefixDuration a b z j else 0
  else ∞

theorem measurable_physicalAbsorptionTime (a b : ℝ) :
    Measurable (physicalAbsorptionTime a b) := by
  have hh : MeasurableSet {z : Sample | hitsOne z.1} :=
    measurableSet_hitsOne.preimage measurable_fst
  have hs : Measurable (fun z : Sample =>
      ⨆ j : ℕ, if firstHit z.1 = j then prefixDuration a b z j else 0) := by
    apply Measurable.iSup
    intro j
    have hj : MeasurableSet {z : Sample | firstHit z.1 = j} :=
      (measurable_firstHit.comp measurable_fst) (measurableSet_singleton j)
    exact Measurable.ite hj (measurable_prefixDuration a b j) measurable_const
  change Measurable (fun z : Sample =>
    if hitsOne z.1 then
      ⨆ j : ℕ, if firstHit z.1 = j then prefixDuration a b z j else 0
    else ∞)
  exact Measurable.ite hh hs measurable_const

theorem physicalAbsorptionTime_of_hit (a b : ℝ) (z : Sample)
    (h : hitsOne z.1) :
    physicalAbsorptionTime a b z = prefixDuration a b z (firstHit z.1) := by
  unfold physicalAbsorptionTime
  rw [if_pos h]
  apply le_antisymm
  · refine iSup_le fun j => ?_
    by_cases hj : firstHit z.1 = j
    · simpa [hj]
    · simp [hj]
  · exact le_iSup_of_le (firstHit z.1) (by simp)

theorem physicalAbsorptionTime_of_no_hit (a b : ℝ) (z : Sample)
    (h : ¬hitsOne z.1) : physicalAbsorptionTime a b z = ∞ := by
  simp [physicalAbsorptionTime, h]
/-- For a fixed count path, scale independent unit clocks at the literal
transient rates and stop the clock path at the first absorbing count. -/
def scaledWaits (a b : ℝ) (K : CountPath) (E : ClockPath) : ClockPath :=
  fun i => stoppedWait a b (K, E) i

theorem measurable_scaledWaits (a b : ℝ) :
    Measurable (fun z : Sample => scaledWaits a b z.1 z.2) := by
  apply measurable_pi_iff.mpr
  intro i
  exact measurable_stoppedWait a b i

theorem measurable_scaledWaits_fixed (a b : ℝ) (K : CountPath) :
    Measurable (scaledWaits a b K) := by
  exact (measurable_scaledWaits a b).comp (measurable_const.prodMk measurable_id)

/-- Actual conditional holding-path law as a pushforward of the unit clocks. -/
def holdingLaw (a b : ℝ) (K : CountPath) : Measure ClockPath :=
  unitClockLaw.map (scaledWaits a b K)

instance holdingLaw_probability (a b : ℝ) (K : CountPath) :
    IsProbabilityMeasure (holdingLaw a b K) := by
  unfold holdingLaw
  exact Measure.isProbabilityMeasure_map (measurable_scaledWaits_fixed a b K).aemeasurable

private theorem unitExp_survival (u : ℝ) (hu : 0 ≤ u) :
    expMeasure 1 (Set.Ioi u) = ENNReal.ofReal (Real.exp (-u)) := by
  have hcdf : (expMeasure 1).real (Set.Iic u) = 1 - Real.exp (-u) := by
    rw [← cdf_eq_real, cdf_expMeasure_eq (by norm_num) u]
    simp [hu]
  calc
    expMeasure 1 (Set.Ioi u) =
        ENNReal.ofReal ((expMeasure 1).real (Set.Ioi u)) :=
      (ofReal_measureReal (measure_ne_top _ _)).symm
    _ = ENNReal.ofReal (Real.exp (-u)) := by
      congr 1
      rw [← Set.compl_Iic, measureReal_compl measurableSet_Iic, probReal_univ, hcdf]
      ring

private theorem unitExp_scaled_survival (q t : ℝ) (hq : 0 < q) (ht : 0 ≤ t) :
    expMeasure 1 {x : ℝ | x / q > t} =
      ENNReal.ofReal (Real.exp (-(q * t))) := by
  have hs : {x : ℝ | x / q > t} = Set.Ioi (q * t) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_Ioi]
    constructor
    · intro hx
      simpa only [mul_comm] using (lt_div_iff₀ hq).mp hx
    · intro hx
      apply (lt_div_iff₀ hq).mpr
      simpa only [mul_comm] using hx
  rw [hs]
  exact unitExp_survival (q * t) (mul_nonneg hq.le ht)

/-- Finite conditional survival cylinder, at each fixed positive hitting
count path. This is the joint rate-dependent holding law, not merely a list
of individual clock marginals. -/
theorem holdingLaw_survival_cylinder (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (K : CountPath) (hK : ∀ i, 0 < K i) (hhit : hitsOne K)
    (F : Finset ℕ) (t : ℕ → ℝ)
    (hpre : ∀ i ∈ F, i < firstHit K) (ht : ∀ i ∈ F, 0 ≤ t i) :
    holdingLaw a b K (Set.pi F (fun i => Set.Ioi (t i))) =
      ∏ i ∈ F, ENNReal.ofReal (Real.exp (-(totalRate a b (K i) * t i))) := by
  have heq : (scaledWaits a b K) ⁻¹' (Set.pi F (fun i => Set.Ioi (t i))) =
      Set.pi F (fun i => {x : ℝ | x / totalRate a b (K i) > t i}) := by
    ext E
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_Ioi, Set.mem_setOf_eq]
    constructor
    · intro h i hi
      simpa only [scaledWaits, stoppedWait, hhit, hpre i hi, and_self, if_true, rawWait] using h i hi
    · intro h i hi
      simpa only [scaledWaits, stoppedWait, hhit, hpre i hi, and_self, if_true, rawWait] using h i hi
  have hpi : MeasurableSet (Set.pi F (fun i => Set.Ioi (t i))) :=
    MeasurableSet.pi F.countable_toSet (fun _ _ => measurableSet_Ioi)
  rw [holdingLaw, Measure.map_apply (measurable_scaledWaits_fixed a b K)
      hpi, heq, unitClockLaw]
  rw [Measure.infinitePi_pi (fun _ : ℕ => expMeasure 1) (by measurability)]
  apply Finset.prod_congr rfl
  intro i hi
  have hki : 2 ≤ K i := by
    have hne := firstHit_min K hhit (hpre i hi)
    have hp := hK i
    omega
  exact unitExp_scaled_survival (totalRate a b (K i)) (t i)
    (totalRate_pos a b ha hb (K i) hki) (ht i hi)
/-- Exact joint finite-observation identity. The conditional holding law is
the fixed-count-path pushforward above, integrated against the checked count
path law. This identifies the count-clock coupling without assuming it. -/
theorem joint_holding_observation (θ : ℝ≥0) (n : ℕ) (a b : ℝ)
    (A : Set CountPath) (hA : MeasurableSet A)
    (B : Set ClockPath) (hB : MeasurableSet B) :
    jointLaw θ n {z : Sample | z.1 ∈ A ∧ scaledWaits a b z.1 z.2 ∈ B} =
      ∫⁻ K, (if K ∈ A then holdingLaw a b K B else 0) ∂pathLaw θ n := by
  classical
  have hS : MeasurableSet {z : Sample | z.1 ∈ A ∧ scaledWaits a b z.1 z.2 ∈ B} :=
    (hA.preimage measurable_fst).inter
      (hB.preimage (measurable_scaledWaits a b))
  rw [jointLaw, Measure.prod_apply hS]
  apply lintegral_congr
  intro K
  by_cases hK : K ∈ A
  · have he : (Prod.mk K) ⁻¹' {z : Sample | z.1 ∈ A ∧ scaledWaits a b z.1 z.2 ∈ B} =
        (scaledWaits a b K) ⁻¹' B := by
      ext E
      simp [hK]
    rw [he]
    simpa only [hK, if_true, holdingLaw] using
      (Measure.map_apply (measurable_scaledWaits_fixed a b K) hB).symm
  · have he : (Prod.mk K) ⁻¹' {z : Sample | z.1 ∈ A ∧ scaledWaits a b z.1 z.2 ∈ B} = ∅ := by
      ext E
      simp [hK]
    simp only [hK, if_false, he]
    simp
theorem prehit_count_ge_two (K : CountPath) (hp : ∀ i, 0 < K i)
    (hh : hitsOne K) (i : ℕ) (hi : i < firstHit K) : 2 ≤ K i := by
  have hne := firstHit_min K hh hi
  have hpos := hp i
  omega

theorem stoppedWait_pos_before_hit (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (z : Sample) (hp : ∀ i, 0 < z.1 i) (hh : hitsOne z.1)
    (hE : ∀ i, 0 < z.2 i) (i : ℕ) (hi : i < firstHit z.1) :
    0 < stoppedWait a b z i := by
  have hk : 2 ≤ z.1 i := prehit_count_ge_two z.1 hp hh i hi
  have hq := totalRate_pos a b ha hb (z.1 i) hk
  simp only [stoppedWait, hh, hi, and_self, if_true, rawWait]
  exact div_pos (hE i) hq

theorem eventTime_strict_before_hit (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (z : Sample) (hp : ∀ i, 0 < z.1 i) (hh : hitsOne z.1)
    (hE : ∀ i, 0 < z.2 i) (i : ℕ) (hi : i < firstHit z.1) :
    eventTime a b z i < eventTime a b z (i + 1) := by
  rw [eventTime_succ]
  have hw := stoppedWait_pos_before_hit a b ha hb z hp hh hE i hi
  linarith

theorem physicalAbsorptionTime_finite_of_hit (a b : ℝ) (z : Sample)
    (hh : hitsOne z.1) : physicalAbsorptionTime a b z ≠ ∞ := by
  rw [physicalAbsorptionTime_of_hit a b z hh]
  unfold prefixDuration
  exact ENNReal.sum_ne_top.mpr (fun i hi => ENNReal.ofReal_ne_top)

@[simp] theorem physicalAbsorptionTime_start_one (a b : ℝ) (z : Sample)
    (h0 : z.1 0 = 1) : physicalAbsorptionTime a b z = 0 := by
  have hh : hitsOne z.1 := ⟨0, h0⟩
  have hfirst : firstHit z.1 = 0 := by
    apply Nat.eq_zero_of_le_zero
    apply Nat.find_min' (hitCandidate_exists z.1)
    exact Or.inl h0
  rw [physicalAbsorptionTime_of_hit a b z hh, hfirst]
  simp [prefixDuration]

/-- A unit exponential innovation is strictly positive almost surely. -/
theorem unitExp_ae_positive : ∀ᵐ x ∂expMeasure (1 : ℝ), 0 < x := by
  have hm : expMeasure 1 (Set.Ioi (0 : ℝ)) = 1 := by
    simpa using unitExp_survival 0 le_rfl
  have hn : expMeasure 1 (Set.Ioi (0 : ℝ))ᶜ = 0 := by
    rw [prob_compl_eq_one_sub₀ measurableSet_Ioi.nullMeasurableSet, hm]
    simp
  rw [ae_iff]
  have he : {x : ℝ | ¬ 0 < x} = (Set.Ioi (0 : ℝ))ᶜ := by
    ext x
    simp
  rw [he]
  exact hn

/-- Every coordinate of the innovation path is positive on one common full-measure set. -/
theorem unitClocks_ae_all_positive :
    ∀ᵐ E ∂unitClockLaw, ∀ i : ℕ, 0 < E i := by
  rw [ae_all_iff]
  intro i
  have h := ae_of_ae_map (μ := unitClockLaw) (f := fun E : ClockPath => E i)
    (measurable_pi_apply i).aemeasurable (by
      rw [unit_clock_marginal]
      exact unitExp_ae_positive)
  exact h

/-- Almost every joint sample inherits positivity of all clock innovations. -/
theorem jointClocks_ae_all_positive (θ : ℝ≥0) (n : ℕ) :
    ∀ᵐ z ∂jointLaw θ n, ∀ i : ℕ, 0 < z.2 i := by
  exact ae_of_ae_map (μ := jointLaw θ n) (f := Prod.snd)
    (p := fun E : ClockPath => ∀ i : ℕ, 0 < E i)
    measurable_snd.aemeasurable (by
      rw [joint_clock_marginal]
      exact unitClocks_ae_all_positive)

/-- Almost every joint sample reaches one at a finite count index. -/
theorem joint_ae_hitsOne (θ : ℝ≥0) (n : ℕ) :
    ∀ᵐ z ∂jointLaw θ n, hitsOne z.1 := by
  apply ae_of_ae_map (μ := jointLaw θ n) (f := Prod.fst)
    measurable_fst.aemeasurable
  rw [joint_count_marginal]
  exact ae_finite_jump_absorption θ n

/-- Positive starts never visit the natural-number zero totalization. -/
theorem joint_ae_positive_counts (θ : ℝ≥0) (n : ℕ) (hn : n ≠ 0) :
    ∀ᵐ z ∂jointLaw θ n, ∀ i : ℕ, 0 < z.1 i := by
  exact ae_of_ae_map (μ := jointLaw θ n) (f := Prod.fst)
    (p := fun K : CountPath => ∀ i : ℕ, 0 < K i)
    measurable_fst.aemeasurable (by
      rw [joint_count_marginal]
      exact ae_positive_counts θ n hn)

/-- The extended-real stopping time is the image of the actual finite real
sum over pre-hit events on positive paths and clocks. -/
theorem physicalAbsorptionTime_eq_ofReal_eventTime (a b : ℝ)
    (ha : 0 < a) (hb : 0 ≤ b) (z : Sample)
    (hp : ∀ i, 0 < z.1 i) (hh : hitsOne z.1)
    (hE : ∀ i, 0 < z.2 i) :
    physicalAbsorptionTime a b z =
      ENNReal.ofReal (eventTime a b z (firstHit z.1)) := by
  rw [physicalAbsorptionTime_of_hit a b z hh]
  unfold prefixDuration eventTime
  rw [ENNReal.ofReal_sum_of_nonneg]
  intro i hi
  exact (stoppedWait_pos_before_hit a b ha hb z hp hh hE i
    (Finset.mem_range.mp hi)).le

/-- The initial count equals its prescribed value almost surely. -/
theorem count_ae_initial (θ : ℝ≥0) (n : ℕ) :
    ∀ᵐ K ∂pathLaw θ n, K 0 = n := by
  have hm : pathLaw θ n {K | K 0 = n} = 1 := by
    rw [← singleton_lintegral]
    simpa using initial_lintegral θ n (fun k => if k = n then 1 else 0)
  have hn : pathLaw θ n {K | K 0 = n}ᶜ = 0 := by
    have hset : MeasurableSet {K : CountPath | K 0 = n} := by measurability
    rw [prob_compl_eq_one_sub₀ hset.nullMeasurableSet, hm]
    simp
  rw [ae_iff]
  have he : {K : CountPath | ¬K 0 = n} = {K : CountPath | K 0 = n}ᶜ := by
    ext K
    simp
  rw [he]
  exact hn

/-- The prescribed initial count also holds in the joint law. -/
theorem joint_ae_initial (θ : ℝ≥0) (n : ℕ) :
    ∀ᵐ z ∂jointLaw θ n, z.1 0 = n := by
  exact ae_of_ae_map (μ := jointLaw θ n) (f := Prod.fst)
    (p := fun K : CountPath => K 0 = n)
    measurable_fst.aemeasurable (by
      rw [joint_count_marginal]
      exact count_ae_initial θ n)

/-- On every good path starting with at least two lineages, the stopped
physical time is strictly positive. -/
theorem physicalAbsorptionTime_pos_of_start_ge_two (a b : ℝ)
    (ha : 0 < a) (hb : 0 ≤ b) (z : Sample)
    (hp : ∀ i, 0 < z.1 i) (hh : hitsOne z.1)
    (hE : ∀ i, 0 < z.2 i) (h0 : 2 ≤ z.1 0) :
    0 < physicalAbsorptionTime a b z := by
  have htau : 0 < firstHit z.1 := by
    by_contra h
    have hz : firstHit z.1 = 0 := by omega
    have hfirst := firstHit_spec z.1 hh
    rw [hz] at hfirst
    omega
  rw [physicalAbsorptionTime_of_hit a b z hh]
  unfold prefixDuration
  have hfirst : 0 < ENNReal.ofReal (stoppedWait a b z 0) :=
    ENNReal.ofReal_pos.mpr
      (stoppedWait_pos_before_hit a b ha hb z hp hh hE 0 htau)
  have hle : ENNReal.ofReal (stoppedWait a b z 0) ≤
      ∑ i ∈ Finset.range (firstHit z.1), ENNReal.ofReal (stoppedWait a b z i) := by
    exact Finset.single_le_sum (s := Finset.range (firstHit z.1))
      (f := fun i => ENNReal.ofReal (stoppedWait a b z i))
      (fun i hi => bot_le) (Finset.mem_range.mpr htau)
  exact lt_of_lt_of_le hfirst hle

/-- Literal positive rates give finite physical first-hit time almost surely.
The finite prefix is the sequence of actual events; its zero padded tail
contains no further event. -/
theorem literal_rates_ae_finite_physical_absorption
    (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (n : ℕ) (hn : 1 ≤ n) :
    ∀ᵐ z ∂jointLaw (normalizedRatio a b ha hb) n,
      hitsOne z.1 ∧
      (∀ i < firstHit z.1, 2 ≤ z.1 i) ∧
      (∀ i < firstHit z.1, 0 < stoppedWait a b z i) ∧
      (∀ i < firstHit z.1, eventTime a b z i < eventTime a b z (i + 1)) ∧
      physicalAbsorptionTime a b z ≠ ∞ ∧
      physicalAbsorptionTime a b z =
        ENNReal.ofReal (eventTime a b z (firstHit z.1)) := by
  have hn0 : n ≠ 0 := by omega
  filter_upwards [joint_ae_hitsOne (normalizedRatio a b ha hb) n,
    joint_ae_positive_counts (normalizedRatio a b ha hb) n hn0,
    jointClocks_ae_all_positive (normalizedRatio a b ha hb) n] with z hh hp hE
  refine ⟨hh, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    exact prehit_count_ge_two z.1 hp hh i hi
  · intro i hi
    exact stoppedWait_pos_before_hit a b ha hb z hp hh hE i hi
  · intro i hi
    exact eventTime_strict_before_hit a b ha hb z hp hh hE i hi
  · exact physicalAbsorptionTime_finite_of_hit a b z hh
  · exact physicalAbsorptionTime_eq_ofReal_eventTime a b ha hb z hp hh hE

/-- A one-lineage start is already absorbed, with zero physical time almost surely. -/
theorem literal_rates_ae_start_one_zero_time
    (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) :
    ∀ᵐ z ∂jointLaw (normalizedRatio a b ha hb) 1,
      firstHit z.1 = 0 ∧ physicalAbsorptionTime a b z = 0 := by
  filter_upwards [joint_ae_initial (normalizedRatio a b ha hb) 1] with z h0
  have hh : hitsOne z.1 := ⟨0, h0⟩
  have hfirst : firstHit z.1 = 0 := by
    apply Nat.eq_zero_of_le_zero
    apply Nat.find_min' (hitCandidate_exists z.1)
    exact Or.inl h0
  exact ⟨hfirst, physicalAbsorptionTime_start_one a b z h0⟩

/-- At a start of at least two lineages, the actual finite stopping time is
strictly positive almost surely. -/
theorem literal_rates_ae_positive_physical_time
    (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (n : ℕ) (hn : 2 ≤ n) :
    ∀ᵐ z ∂jointLaw (normalizedRatio a b ha hb) n,
      0 < physicalAbsorptionTime a b z ∧ physicalAbsorptionTime a b z ≠ ∞ := by
  have hn0 : n ≠ 0 := by omega
  filter_upwards [joint_ae_hitsOne (normalizedRatio a b ha hb) n,
    joint_ae_positive_counts (normalizedRatio a b ha hb) n hn0,
    jointClocks_ae_all_positive (normalizedRatio a b ha hb) n,
    joint_ae_initial (normalizedRatio a b ha hb) n] with z hh hp hE h0
  have hstart : 2 ≤ z.1 0 := by simpa [h0] using hn
  exact ⟨physicalAbsorptionTime_pos_of_start_ge_two a b ha hb z hp hh hE hstart,
    physicalAbsorptionTime_finite_of_hit a b z hh⟩

/-- A transparent rate-three check at count two, with split mass two-thirds. -/
theorem rate_three_at_two : totalRate 1 1 2 = 3 := by
  norm_num [totalRate]

theorem split_mass_two_thirds :
    (jumpKernel (normalizedRatio 1 1 (by norm_num) (by norm_num)) 2 {3}).toReal =
      (2 : ℝ) / 3 := by
  have h := literal_up_kernel_mass 1 1 (by norm_num) (by norm_num) 0
  convert h using 1 <;> norm_num

#print axioms unitClockLaw_probability
#print axioms jointLaw_probability
#print axioms joint_count_marginal
#print axioms joint_clock_marginal
#print axioms unit_clock_marginal
#print axioms count_clock_independent
#print axioms unit_clocks_independent
#print axioms measurable_firstHit
#print axioms measurable_physicalAbsorptionTime
#print axioms holdingLaw_probability
#print axioms holdingLaw_survival_cylinder
#print axioms joint_holding_observation
#print axioms unitClocks_ae_all_positive
#print axioms jointClocks_ae_all_positive
#print axioms joint_ae_hitsOne
#print axioms joint_ae_positive_counts
#print axioms physicalAbsorptionTime_eq_ofReal_eventTime
#print axioms count_ae_initial
#print axioms joint_ae_initial
#print axioms literal_rates_ae_finite_physical_absorption
#print axioms literal_rates_ae_start_one_zero_time
#print axioms literal_rates_ae_positive_physical_time
#print axioms rate_three_at_two
#print axioms split_mass_two_thirds
end
end WongWaitingTimes