import WongMarkedMeasurable

set_option autoImplicit false

/-!
# A dated marked history and its intrinsic count-and-time projection

This deliberately redundant representation stores the actual recorder's
prefix states, event dates and stopping index. Both infinite sequences are
constant beyond that finite index. The explicit final result preserves the
recorder's failure totalization. No count coordinate or random seed is stored.
This is a faithful finite-history encoding, not a compact serialization claim.
-/
namespace WongMarkedDated
open MeasureTheory WongCountChain WongWaitingTimes
open WongMarkedLaw WongMarkedRecorder WongMarkedProcess WongMarkedMeasurable
open scoped NNReal Classical
noncomputable section

structure History where
  horizon : ℕ
  result : Option (RawState ℝ)
  states : ℕ → Option (RawState ℝ)
  times : ClockPath

def historyCode (h : History) :
    ℕ × Option (RawState ℝ) × (ℕ → Option (RawState ℝ)) × ClockPath :=
  (h.horizon,h.result,h.states,h.times)

instance : MeasurableSpace History := MeasurableSpace.comap historyCode inferInstance

theorem historyCode_injective : Function.Injective historyCode := by
  rintro ⟨a,b,c,d⟩ ⟨e,f,g,h⟩ he
  have he' : a=e ∧ b=f ∧ c=g ∧ d=h := by simpa [historyCode] using he
  rcases he' with ⟨rfl,rfl,rfl,rfl⟩
  rfl

theorem measurable_history_states : Measurable History.states :=
  measurable_fst.comp (measurable_snd.comp (measurable_snd.comp (comap_measurable historyCode)))

theorem measurable_history_times : Measurable History.times :=
  measurable_snd.comp (measurable_snd.comp (measurable_snd.comp (comap_measurable historyCode)))

def realize (L : ℝ) (hL : 0 < L) (n : ℕ) (a b : ℝ)
    (z : WongMarkedLaw.Sample) : History where
  horizon := firstHit z.1.1
  result := stoppedRecord L hL n z
  states := fun i => recordPrefix L hL n z (min i (firstHit z.1.1))
  times := fun i => eventTime a b z.1 i

theorem measurable_realize (L : ℝ) (hL : 0 < L) (n : ℕ) (a b : ℝ) :
    Measurable (realize L hL n a b) := by
  have ht : Measurable (fun z : WongMarkedLaw.Sample => firstHit z.1.1) :=
    measurable_firstHit.comp (measurable_fst.comp measurable_fst)
  have hp : Measurable (fun z : WongMarkedLaw.Sample => fun t => recordPrefix L hL n z t) :=
    measurable_pi_lambda _ (fun t => measurable_recordPrefix L hL n t)
  have hs : Measurable (fun z : WongMarkedLaw.Sample =>
      fun i => recordPrefix L hL n z (min i (firstHit z.1.1))) := by
    apply measurable_pi_lambda
    intro i
    exact measurable_dynamic hp ((measurable_of_countable (fun j : ℕ => min i j)).comp ht)
  apply measurable_comap_iff.mpr
  exact ht.prodMk ((measurable_stoppedRecord L hL n).prodMk
    (hs.prodMk (measurable_pi_lambda _ (fun i => (measurable_eventTime a b i).comp measurable_fst))))

/-- Reads only the stored state; failure has count zero. -/
def frontierSize (o : Option (RawState ℝ)) : ℕ :=
  (o.map (fun s => s.active.card)).getD 0

theorem measurable_frontierSize : Measurable frontierSize := by
  have hm := (measurable_of_countable (fun A : Finset ℕ => A.card)).comp
    (measurable_active.comp measurable_getD)
  convert hm using 1
  funext o
  cases o <;> simp [frontierSize,defaultState,initial]

/-- A function of the dated history alone, with no access to its input. -/
def project (h : History) : CountPath × ClockPath :=
  (fun i => frontierSize (h.states i), h.times)

theorem measurable_project : Measurable project := by
  apply Measurable.prodMk
  · exact measurable_pi_lambda _ (fun i => measurable_frontierSize.comp
      ((measurable_pi_apply i).comp measurable_history_states))
  · exact measurable_history_times

def historyLaw (L : ℝ) (hL : 0 < L) (θ : ℝ≥0) (n : ℕ) (a b : ℝ) : Measure History :=
  (law L hL θ n).map (realize L hL n a b)

instance historyLaw_probability (L : ℝ) (hL : 0 < L) (θ : ℝ≥0) (n : ℕ) (a b : ℝ) :
    IsProbabilityMeasure (historyLaw L hL θ n a b) :=
  Measure.isProbabilityMeasure_map (measurable_realize L hL n a b).aemeasurable

/-- The count/time law factors through the actual stored dated history. -/
theorem history_count_time_projection (L : ℝ) (hL : 0 < L) (θ : ℝ≥0)
    (n : ℕ) (hn : 0 < n) (a b : ℝ) :
    (historyLaw L hL θ n a b).map project =
      (jointLaw θ n).map (countTimeObservation a b) := by
  unfold historyLaw
  rw [Measure.map_map measurable_project (measurable_realize L hL n a b)]
  have heq : project ∘ realize L hL n a b =ᵐ[law L hL θ n]
      (fun z => countTimeObservation a b z.1) := by
    filter_upwards [law_ae_good L hL θ n hn] with z hz
    apply Prod.ext
    · funext i
      exact recordedCount_eq L hL n z hz i
    · rfl
  rw [Measure.map_congr heq]
  change (law L hL θ n).map
    (countTimeObservation a b ∘ (Prod.fst : WongMarkedLaw.Sample → WongWaitingTimes.Sample)) = _
  rw [← Measure.map_map (measurable_countTimeObservation a b) measurable_fst,
    timed_count_marginal]

theorem realize_constant_tail (L : ℝ) (hL : 0 < L) (n : ℕ) (a b : ℝ)
    (z : WongMarkedLaw.Sample) (i : ℕ) (hi : (realize L hL n a b z).horizon ≤ i) :
    (realize L hL n a b z).states i =
      (realize L hL n a b z).states (realize L hL n a b z).horizon ∧
    (realize L hL n a b z).times i =
      (realize L hL n a b z).times (realize L hL n a b z).horizon := by
  change firstHit z.1.1 ≤ i at hi
  constructor
  · simp [realize,min_eq_right hi]
  · have he := eventTime_min_firstHit a b z.1 i
    rw [min_eq_right hi] at he
    exact he.symm

theorem eventTime_strict_range (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    {L : ℝ} {n : ℕ} (z : WongMarkedLaw.Sample) (hz : Good L n z)
    (i j : ℕ) (hij : i < j) (hj : j ≤ firstHit z.1.1) :
    eventTime a b z.1 i < eventTime a b z.1 j := by
  induction j with
  | zero => omega
  | succ j ih =>
      have hstep := eventTime_strict_before_hit a b ha hb z.1 hz.2.1 hz.2.2.1
        hz.2.2.2.2.2 j (by omega)
      by_cases he : i=j
      · simpa [he] using hstep
      · exact lt_trans (ih (by omega) (by omega)) hstep

/-- Every completed interval edge receives strictly older parent dates from
the stored clock. The event created at vertex n+j is dated at time j+1. -/
theorem realized_edge_chronology (L : ℝ) (hL : 0 < L) (n : ℕ)
    (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (z : WongMarkedLaw.Sample) (hz : Good L n z)
    (s : RawState ℝ) (hs : Valid n 0 L s) (hlen : s.events.length = firstHit z.1.1)
    {i : ℕ} (hi : i ∈ s.completed) :
    vertexDate n (fun j => (realize L hL n a b z).times (j+1)) (s.slot i).child <
      vertexDate n (fun j => (realize L hL n a b z).times (j+1)) (s.parent i) := by
  apply dated_prefix_chronology_bounded hs _ _ _ hi
  · intro j hj
    have ht := eventTime_strict_range a b ha hb z hz 0 (j+1) (by omega) (by omega)
    simpa [realize,eventTime] using ht
  · intro j k hjk hk
    exact eventTime_strict_range a b ha hb z hz (j+1) (k+1) (by omega) (by omega)

/-- Successful finite histories have an explicit valid final graph, one live
lineage, the correct number of vertices, and chronological completed edges. -/
def ValidDated (L : ℝ) (n : ℕ) (h : History) : Prop :=
  ∃ s, h.result = some s ∧ h.states h.horizon = some s ∧ Valid n 0 L s ∧
    s.active.card = 1 ∧ s.events.length = h.horizon ∧ s.nextVertex = n + h.horizon ∧
    (∀ i, h.horizon ≤ i → h.states i = h.states h.horizon ∧ h.times i = h.times h.horizon) ∧
    (∀ i ∈ s.completed,
      vertexDate n (fun j => h.times (j+1)) (s.slot i).child <
        vertexDate n (fun j => h.times (j+1)) (s.parent i))

theorem realize_validDated (L : ℝ) (hL : 0 < L) (n : ℕ) (hn : 0 < n)
    (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (z : WongMarkedLaw.Sample) (hz : Good L n z) :
    ValidDated L n (realize L hL n a b z) := by
  obtain ⟨s,hrec,hs,hcount,hlen⟩ := stoppedRecord_spec L hL n hn z hz
  have hpref : recordPrefix L hL n z (firstHit z.1.1) = some s := by
    simpa [stoppedRecord,hn,hz.1,hz.2.2.1] using hrec
  refine ⟨s,hrec,?_,hs,hcount,hlen,?_,?_,?_⟩
  · simpa [realize] using hpref
  · simpa [realize,hlen] using hs.vertices
  · intro i hi
    exact realize_constant_tail L hL n a b z i hi
  · intro i hi
    exact realized_edge_chronology L hL n a b ha hb z hz s hs hlen hi

/-- Almost every random input produces a valid dated history. This statement
does not assume measurability of the quantified validity predicate on the
ambient History type; the law itself and its intrinsic projection are already
measurable and have the exact pushforward equality above. -/
theorem law_ae_realize_validDated (L : ℝ) (hL : 0 < L) (n : ℕ) (hn : 0 < n)
    (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) :
    ∀ᵐ z ∂law L hL (WongBigARGAbsorption.normalizedRatio a b ha hb) n,
      ValidDated L n (realize L hL n a b z) := by
  filter_upwards [law_ae_good L hL (WongBigARGAbsorption.normalizedRatio a b ha hb) n hn]
    with z hz
  exact realize_validDated L hL n hn a b ha hb z hz

#print axioms historyCode_injective
#print axioms measurable_realize
#print axioms measurable_project
#print axioms historyLaw_probability
#print axioms history_count_time_projection
#print axioms realize_constant_tail
#print axioms realized_edge_chronology
#print axioms law_ae_realize_validDated
end
end WongMarkedDated
