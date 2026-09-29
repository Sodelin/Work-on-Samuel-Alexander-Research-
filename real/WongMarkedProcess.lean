import WongMarkedLaw
import WongMarkedRecorder

set_option autoImplicit false

/-! Actual marked-record folding. Malformed consumed transitions return
`none`; unused mark components and the post-stopping tail are not validated.
The fold does not check clock positivity. It never substitutes a fabricated
valid event. The stopping index is the count law's first hit of one. -/
namespace WongMarkedProcess
open MeasureTheory ProbabilityTheory WongCountChain WongWaitingTimes
open WongMarkedLaw WongMarkedRecorder
open scoped ENNReal NNReal BigOperators Classical
noncomputable section

def pairIDs (p : Finset ℕ) (hp : p.card = 2) :
    {q : ℕ × ℕ // q.1 ≠ q.2 ∧ p = {q.1, q.2}} := by
  have hex : ∃ q : ℕ × ℕ, q.1 ≠ q.2 ∧ p = {q.1, q.2} := by
    obtain ⟨i, j, hij, he⟩ := Finset.card_eq_two.mp hp
    exact ⟨(i,j), hij, he⟩
  exact ⟨Classical.choose hex, Classical.choose_spec hex⟩

def step (L : ℝ) (hL : 0 < L) (s : RawState ℝ) (next : ℕ)
    (m : SpatialMark) : Option (RawState ℝ) :=
  if next = s.active.card + 1 then
    if h : m.1 ∈ s.active ∧ 0 < m.2.2 ∧ m.2.2 < L then
      some (split s m.1 ⟨m.2.2, h.2⟩)
    else none
  else if next + 1 = s.active.card then
    if h : m.2.1 ⊆ s.active ∧ m.2.1.card = 2 then
      let ids := pairIDs m.2.1 h.2
      some (merge s ids.val.1 ids.val.2 hL)
    else none
  else none

theorem step_valid_count {L : ℝ} (hL : 0 < L) {n : ℕ} {s : RawState ℝ}
    (hs : Valid n 0 L s) (hk : 2 ≤ s.active.card) (next : ℕ)
    (jump : LegalStep s.active.card next) (m : SpatialMark)
    (hm : ValidSpatialMark L s.active m) :
    ∃ out, step L hL s next m = some out ∧ Valid n 0 L out ∧
      out.active.card = next ∧ out.events.length = s.events.length + 1 := by
  have hne : ¬s.active.card ≤ 1 := by omega
  have hj : next = s.active.card + 1 ∨ next + 1 = s.active.card := by
    simpa [LegalStep, hne] using jump
  rcases hj with up | down
  · have hsel : m.1 ∈ s.active := hm.1 (Finset.card_pos.mp (by omega))
    let cut : Cut (0 : ℝ) L := ⟨m.2.2, hm.2.2⟩
    refine ⟨split s m.1 cut, ?_, split_preserves_valid hs hsel cut, ?_, ?_⟩
    · simp [step, up, hsel, hm.2.2.1, hm.2.2.2, cut]
    · rw [split_frontier_count hs hsel cut, up]
    · simp [split, advance]
  · have notup : ¬next = s.active.card + 1 := by omega
    have hp : m.2.1 ⊆ s.active ∧ m.2.1.card = 2 := hm.2.1 hk
    let ids := pairIDs m.2.1 hp.2
    have hi : ids.val.1 ∈ s.active := hp.1
      ((congrArg (fun p : Finset ℕ => ids.val.1 ∈ p) ids.property.2).mpr (by simp))
    have hj : ids.val.2 ∈ s.active := hp.1
      ((congrArg (fun p : Finset ℕ => ids.val.2 ∈ p) ids.property.2).mpr (by simp))
    refine ⟨merge s ids.val.1 ids.val.2 hL, ?_,
      merge_preserves_valid hs hi hj ids.property.1 hL, ?_, ?_⟩
    · simp [step, notup, down, hp, ids]
    · have hc := merge_frontier_count hs hi hj ids.property.1 hL
      omega
    · simp [merge, advance]

def recordPrefix (L : ℝ) (hL : 0 < L) (n : ℕ) (z : WongMarkedLaw.Sample) :
    ℕ → Option (RawState ℝ)
  | 0 => some (initial n hL)
  | t + 1 => (recordPrefix L hL n z t).bind
      (fun s => step L hL s (z.1.1 (t + 1)) (z.2 (t, s.active)))

/-- Causality is an equality of the actual total fold, including failures.
No future innovation row can affect a prefix already recorded. -/
theorem recordPrefix_causal (L : ℝ) (hL : 0 < L) (n t : ℕ)
    (z w : WongMarkedLaw.Sample) (hc : z.1.1 = w.1.1)
    (hm : ∀ ix : InnovationIndex, ix.1 < t → z.2 ix = w.2 ix) :
    recordPrefix L hL n z t = recordPrefix L hL n w t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      have he := ih (fun ix hi => hm ix (by omega))
      simp only [recordPrefix, he, hc]
      congr 1
      funext s
      rw [hm (t,s.active) (by simp)]

def Good (L : ℝ) (n : ℕ) (z : WongMarkedLaw.Sample) : Prop :=
  z.1.1 0 = n ∧ (∀ t, 0 < z.1.1 t) ∧ hitsOne z.1.1 ∧
  (∀ t, LegalStep (z.1.1 t) (z.1.1 (t + 1))) ∧
  (∀ ix, ValidSpatialMark L ix.2 (z.2 ix)) ∧ (∀ t, 0 < z.1.2 t)

theorem prefix_valid_count (L : ℝ) (hL : 0 < L) (n : ℕ)
    (z : WongMarkedLaw.Sample) (hz : Good L n z) (t : ℕ)
    (ht : t ≤ firstHit z.1.1) :
    ∃ s, recordPrefix L hL n z t = some s ∧ Valid n 0 L s ∧
      s.active.card = z.1.1 t ∧ s.events.length = t := by
  induction t with
  | zero =>
      refine ⟨initial n hL, rfl, initial_valid n hL, ?_, rfl⟩
      simpa [initial] using hz.1.symm
  | succ t ih =>
      obtain ⟨s, hp, hs, hc, he⟩ := ih (by omega)
      have hpre : t < firstHit z.1.1 := by omega
      have hk : 2 ≤ s.active.card := by
        rw [hc]
        exact prehit_count_ge_two z.1.1 hz.2.1 hz.2.2.1 t hpre
      have jump : LegalStep s.active.card (z.1.1 (t + 1)) := by
        rw [hc]; exact hz.2.2.2.1 t
      obtain ⟨out, ho, hv, hcount, hlen⟩ := step_valid_count hL hs hk
        (z.1.1 (t + 1)) jump (z.2 (t,s.active)) (hz.2.2.2.2.1 (t,s.active))
      refine ⟨out, ?_, hv, hcount, ?_⟩
      · simp only [recordPrefix, hp, Option.bind_some]; exact ho
      · omega

/-- Nonhitting paths and malformed starts are explicit failures. -/
def stoppedRecord (L : ℝ) (hL : 0 < L) (n : ℕ) (z : WongMarkedLaw.Sample) :
    Option (RawState ℝ) :=
  if 0 < n ∧ z.1.1 0 = n ∧ hitsOne z.1.1 then recordPrefix L hL n z (firstHit z.1.1)
  else none

theorem stoppedRecord_spec (L : ℝ) (hL : 0 < L) (n : ℕ) (hn : 0 < n)
    (z : WongMarkedLaw.Sample) (hz : Good L n z) :
    ∃ s, stoppedRecord L hL n z = some s ∧ Valid n 0 L s ∧
      s.active.card = 1 ∧ s.events.length = firstHit z.1.1 := by
  obtain ⟨s, hp, hs, hc, he⟩ := prefix_valid_count L hL n z hz (firstHit z.1.1) le_rfl
  refine ⟨s, ?_, hs, ?_, he⟩
  · simpa [stoppedRecord, hn, hz.1, hz.2.2.1] using hp
  · exact hc.trans (firstHit_spec z.1.1 hz.2.2.1)

theorem law_ae_good (L : ℝ) (hL : 0 < L) (θ : ℝ≥0) (n : ℕ) (hn : 0 < n) :
    ∀ᵐ z ∂law L hL θ n, Good L n z := by
  have h0 : ∀ᵐ z ∂law L hL θ n, z.1.1 0 = n :=
    ae_of_ae_map (μ := law L hL θ n) measurable_fst.aemeasurable (by
      rw [timed_count_marginal]; exact joint_ae_initial θ n)
  have hp : ∀ᵐ z ∂law L hL θ n, ∀ t, 0 < z.1.1 t :=
    ae_of_ae_map (μ := law L hL θ n) measurable_fst.aemeasurable (by
      rw [timed_count_marginal]; exact joint_ae_positive_counts θ n (by omega))
  have hh : ∀ᵐ z ∂law L hL θ n, hitsOne z.1.1 :=
    ae_of_ae_map (μ := law L hL θ n) measurable_fst.aemeasurable (by
      rw [timed_count_marginal]; exact joint_ae_hitsOne θ n)
  have hE : ∀ᵐ z ∂law L hL θ n, ∀ t, 0 < z.1.2 t :=
    ae_of_ae_map (μ := law L hL θ n) measurable_fst.aemeasurable (by
      rw [timed_count_marginal]; exact jointClocks_ae_all_positive θ n)
  filter_upwards [h0, hp, hh, hE, law_ae_legal L hL θ n,
    law_ae_all_marks_valid L hL θ n] with z h0 hp hh hE hlegal hmarks
  exact ⟨h0, hp, hh, hlegal, hmarks, hE⟩

/-- Arbitrary finite samples: almost every actual recorder run succeeds,
has valid interval graph data, stops at exactly one lineage after exactly
the checked count path's first-hit number of actual events. -/
theorem law_ae_stoppedRecord (L : ℝ) (hL : 0 < L) (θ : ℝ≥0)
    (n : ℕ) (hn : 0 < n) :
    ∀ᵐ z ∂law L hL θ n,
      ∃ s, stoppedRecord L hL n z = some s ∧ Valid n 0 L s ∧
        s.active.card = 1 ∧ s.events.length = firstHit z.1.1 := by
  filter_upwards [law_ae_good L hL θ n hn] with z hz
  exact stoppedRecord_spec L hL n hn z hz

theorem law_ae_finite_physical_graph (L : ℝ) (hL : 0 < L)
    (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (n : ℕ) (hn : 0 < n) :
    ∀ᵐ z ∂law L hL (WongBigARGAbsorption.normalizedRatio a b ha hb) n,
      (∃ s, stoppedRecord L hL n z = some s ∧ Valid n 0 L s ∧
        s.active.card = 1 ∧ s.events.length = firstHit z.1.1) ∧
      physicalAbsorptionTime a b z.1 ≠ ∞ ∧
      (∀ i < firstHit z.1.1, 0 < stoppedWait a b z.1 i) ∧
      (∀ i < firstHit z.1.1, eventTime a b z.1 i < eventTime a b z.1 (i+1)) := by
  filter_upwards [law_ae_good L hL (WongBigARGAbsorption.normalizedRatio a b ha hb) n hn]
    with z hz
  refine ⟨stoppedRecord_spec L hL n hn z hz,
    physicalAbsorptionTime_finite_of_hit a b z.1 hz.2.2.1, ?_, ?_⟩
  · intro i hi
    exact stoppedWait_pos_before_hit a b ha hb z.1 hz.2.1 hz.2.2.1 hz.2.2.2.2.2 i hi
  · intro i hi
    exact eventTime_strict_before_hit a b ha hb z.1 hz.2.1 hz.2.2.1 hz.2.2.2.2.2 i hi

theorem legal_path_absorbed (K : CountPath)
    (legal : ∀ t, LegalStep (K t) (K (t+1))) (hit : hitsOne K)
    (i : ℕ) (hi : firstHit K ≤ i) : K i = 1 := by
  have h : ∀ r, K (firstHit K + r) = 1 := by
    intro r
    induction r with
    | zero => simpa using firstHit_spec K hit
    | succ r ih =>
        have hj := legal (firstHit K + r)
        simpa [LegalStep, ih, Nat.add_assoc] using hj
  simpa [Nat.add_sub_of_le hi] using h (i - firstHit K)

/-- Counts are recomputed from the generated frontier, not copied into this
observation from the driving count coordinate. -/
def recordedCount (L : ℝ) (hL : 0 < L) (n : ℕ) (z : WongMarkedLaw.Sample)
    (i : ℕ) : ℕ :=
  ((recordPrefix L hL n z (min i (firstHit z.1.1))).map (fun s => s.active.card)).getD 0

theorem recordedCount_eq (L : ℝ) (hL : 0 < L) (n : ℕ)
    (z : WongMarkedLaw.Sample) (hz : Good L n z) (i : ℕ) :
    recordedCount L hL n z i = z.1.1 i := by
  obtain ⟨s, hp, _, hc, _⟩ := prefix_valid_count L hL n z hz
    (min i (firstHit z.1.1)) (min_le_right _ _)
  simp only [recordedCount, hp, Option.map_some, Option.getD_some, hc]
  by_cases hi : i ≤ firstHit z.1.1
  · rw [min_eq_left hi]
  · rw [min_eq_right (by omega), firstHit_spec z.1.1 hz.2.2.1,
      legal_path_absorbed z.1.1 hz.2.2.2.1 hz.2.2.1 i (by omega)]

theorem eventTime_min_firstHit (a b : ℝ) (z : WongWaitingTimes.Sample) (i : ℕ) :
    eventTime a b z (min i (firstHit z.1)) = eventTime a b z i := by
  induction i with
  | zero => simp
  | succ i ih =>
      by_cases hi : i < firstHit z.1
      · rw [min_eq_left (by omega)]
      · have hle : firstHit z.1 ≤ i := by omega
        rw [min_eq_right (by omega), eventTime_succ]
        have he := ih
        rw [min_eq_right hle] at he
        rw [he]
        simp [stoppedWait, hi]

/-- The time of each generated prefix is evaluated at its actual recorded
event count; indices after absorption represent the same final prefix. -/
def recordedTime (L : ℝ) (hL : 0 < L) (n : ℕ) (a b : ℝ)
    (z : WongMarkedLaw.Sample) (i : ℕ) : ℝ :=
  eventTime a b z.1
    (((recordPrefix L hL n z (min i (firstHit z.1.1))).map (fun s => s.events.length)).getD 0)

theorem recordedTime_eq (L : ℝ) (hL : 0 < L) (n : ℕ) (a b : ℝ)
    (z : WongMarkedLaw.Sample) (hz : Good L n z) (i : ℕ) :
    recordedTime L hL n a b z i = eventTime a b z.1 i := by
  obtain ⟨s, hp, _, _, he⟩ := prefix_valid_count L hL n z hz
    (min i (firstHit z.1.1)) (min_le_right _ _)
  simp only [recordedTime, hp, Option.map_some, Option.getD_some, he]
  exact eventTime_min_firstHit a b z.1 i

def countTimeObservation (a b : ℝ) (z : WongWaitingTimes.Sample) : CountPath × ClockPath :=
  (z.1, fun i => eventTime a b z i)

theorem measurable_countTimeObservation (a b : ℝ) : Measurable (countTimeObservation a b) :=
  measurable_fst.prodMk (measurable_pi_lambda _ (fun i => measurable_eventTime a b i))

def recordObservation (L : ℝ) (hL : 0 < L) (n : ℕ) (a b : ℝ)
    (z : WongMarkedLaw.Sample) : CountPath × ClockPath :=
  (recordedCount L hL n z, recordedTime L hL n a b z)

/-- Law of the actual recorder's computed frontier counts and input-clock
event times. This observes the random input and is not a projection of an
undated final raw graph. `WongMarkedDated.history_count_time_projection`
supplies the stronger factorization through a stored dated history. -/
theorem recorded_count_time_projection (L : ℝ) (hL : 0 < L) (θ : ℝ≥0)
    (n : ℕ) (hn : 0 < n) (a b : ℝ) :
    (law L hL θ n).map (recordObservation L hL n a b) =
      (jointLaw θ n).map (countTimeObservation a b) := by
  have heq : recordObservation L hL n a b =ᵐ[law L hL θ n]
      (fun z => countTimeObservation a b z.1) := by
    filter_upwards [law_ae_good L hL θ n hn] with z hz
    apply Prod.ext
    · funext i; exact recordedCount_eq L hL n z hz i
    · funext i; exact recordedTime_eq L hL n a b z hz i
  rw [Measure.map_congr heq]
  change (law L hL θ n).map
    (countTimeObservation a b ∘ (Prod.fst : WongMarkedLaw.Sample → WongWaitingTimes.Sample)) = _
  rw [← Measure.map_map (measurable_countTimeObservation a b) measurable_fst,
    timed_count_marginal]

theorem recordObservation_aemeasurable (L : ℝ) (hL : 0 < L) (θ : ℝ≥0)
    (n : ℕ) (hn : 0 < n) (a b : ℝ) :
    AEMeasurable (recordObservation L hL n a b) (law L hL θ n) := by
  apply ((measurable_countTimeObservation a b).comp measurable_fst).aemeasurable.congr
  filter_upwards [law_ae_good L hL θ n hn] with z hz
  apply Prod.ext
  · funext i; exact (recordedCount_eq L hL n z hz i).symm
  · funext i; exact (recordedTime_eq L hL n a b z hz i).symm

#print axioms step_valid_count
#print axioms recordPrefix_causal
#print axioms prefix_valid_count
#print axioms stoppedRecord_spec
#print axioms law_ae_good
#print axioms law_ae_stoppedRecord
#print axioms law_ae_finite_physical_graph
#print axioms recorded_count_time_projection
#print axioms recordObservation_aemeasurable
end
end WongMarkedProcess
