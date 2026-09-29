import WongMarkedSupport
import WongMarkedDated

set_option autoImplicit false

/-! Borel validity and almost-sure support of the intrinsic dated-history law.
No input coordinates are retained in the support predicate or projection. -/
namespace WongDatedSupport
open MeasureTheory WongGARG WongMarkedRecorder WongMarkedMeasurable WongMarkedSupport
open WongMarkedDated WongMarkedLaw WongMarkedProcess WongWaitingTimes
open scoped Classical NNReal
noncomputable section

instance prodMeasurableEq {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableEq α] [MeasurableEq β] : MeasurableEq (α × β) where
  measurableSet_diagonal := by
    have h : Measurable (fun p : (α×β)×(α×β) => p.1.1=p.2.1 ∧ p.1.2=p.2.2) :=
      (measurable_fst.fst.eq measurable_snd.fst).and
        (measurable_fst.snd.eq measurable_snd.snd)
    convert h.setOf using 1
    ext p
    exact Prod.ext_iff

instance natFunctionMeasurableEq {α : Type*} [MeasurableSpace α] [MeasurableEq α] :
    MeasurableEq (ℕ → α) where
  measurableSet_diagonal := by
    have h : Measurable (fun p : (ℕ→α)×(ℕ→α) => ∀ i, p.1 i=p.2 i) :=
      Measurable.forall (fun i => ((measurable_pi_apply i).comp measurable_fst).eq
        ((measurable_pi_apply i).comp measurable_snd))
    convert h.setOf using 1
    ext p
    exact funext_iff

def measurableEq_of_injective_code {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableEq β] (f : α → β) (hf : Measurable f) (hinj : Function.Injective f) :
    MeasurableEq α where
  measurableSet_diagonal := by
    have h := measurableSet_eq_fun (hf.comp measurable_fst) (hf.comp measurable_snd)
    convert h using 1
    ext p
    exact hinj.eq_iff.symm

instance : MeasurableEq (Interval ℝ) :=
  measurableEq_of_injective_code intervalCode (comap_measurable _) intervalCode_injective
instance : MeasurableEq (Slot ℝ) :=
  measurableEq_of_injective_code slotCode (comap_measurable _) slotCode_injective
instance : MeasurableEq (WongMarkedRecorder.EventKind ℝ) :=
  measurableEq_of_injective_code kindCode (comap_measurable _) kindCode_injective
instance : MeasurableEq (RawEvent ℝ) :=
  measurableEq_of_injective_code eventCode (comap_measurable _) eventCode_injective
instance : MeasurableEq (List (RawEvent ℝ)) :=
  measurableEq_of_injective_code eventListCode (comap_measurable _) eventListCode_injective
instance : MeasurableEq (RawState ℝ) :=
  measurableEq_of_injective_code stateCode (comap_measurable _) stateCode_injective
instance : MeasurableEq (Option (RawState ℝ)) :=
  measurableEq_of_injective_code optionCode (comap_measurable _) optionCode_injective

@[fun_prop] theorem measurable_history_horizon : Measurable History.horizon :=
  measurable_fst.comp (comap_measurable historyCode)
@[fun_prop] theorem measurable_history_result : Measurable History.result :=
  measurable_fst.comp (measurable_snd.comp (comap_measurable historyCode))

def decoded (h : History) : RawState ℝ := h.result.getD defaultState
@[fun_prop] theorem measurable_decoded : Measurable decoded :=
  measurable_getD.comp measurable_history_result

theorem result_eq_some_decoded (h : History) (hp : h.result.isSome = true) :
    h.result = some (decoded h) := by
  unfold decoded
  cases he : h.result <;> simp_all

theorem validDated_iff_decoded (L : ℝ) (n : ℕ) (h : History) :
    ValidDated L n h ↔
      h.result.isSome = true ∧ h.states h.horizon = some (decoded h) ∧
      Valid n 0 L (decoded h) ∧ (decoded h).active.card = 1 ∧
      (decoded h).events.length = h.horizon ∧ (decoded h).nextVertex = n+h.horizon ∧
      (∀ i, h.horizon ≤ i → h.states i=h.states h.horizon ∧ h.times i=h.times h.horizon) ∧
      (∀ i, i ∈ (decoded h).completed →
        vertexDate n (fun j => h.times (j+1)) ((decoded h).slot i).child <
          vertexDate n (fun j => h.times (j+1)) ((decoded h).parent i)) := by
  constructor
  · rintro ⟨s,hr,hs,hv,hc,he,hn,ht,hchron⟩
    have hd : decoded h = s := by simp [decoded,hr]
    exact ⟨by simp [hr],by simpa [hd] using hs,by simpa [hd] using hv,
      by simpa [hd] using hc,by simpa [hd] using he,by simpa [hd] using hn,
      ht,by simpa [hd] using hchron⟩
  · rintro ⟨hp,hs,hv,hc,he,hn,ht,hchron⟩
    exact ⟨decoded h,result_eq_some_decoded h hp,hs,hv,hc,he,hn,ht,hchron⟩

theorem measurable_vertexDate (n : ℕ) {v : History → ℕ} (hv : Measurable v) :
    Measurable (fun h => vertexDate n (fun j => h.times (j+1)) (v h)) := by
  unfold vertexDate
  apply Measurable.ite (measurableSet_lt hv measurable_const) measurable_const
  exact measurable_dynamic measurable_history_times
    ((measurable_of_countable (fun k : ℕ => (k-n)+1)).comp hv)

/-- The intrinsic dated validity predicate is Borel in the natural code. -/
theorem measurable_validDated (L : ℝ) (n : ℕ) : Measurable (ValidDated L n) := by
  have hfinal : Measurable (fun h : History => h.states h.horizon) :=
    measurable_dynamic measurable_history_states measurable_history_horizon
  have htime : Measurable (fun h : History => h.times h.horizon) :=
    measurable_dynamic measurable_history_times measurable_history_horizon
  have hdecoded := measurable_decoded
  have hactive : Measurable (fun h => (decoded h).active.card) :=
    (measurable_of_countable (fun A : Finset ℕ => A.card)).comp (measurable_active.comp hdecoded)
  have hlen : Measurable (fun h => (decoded h).events.length) :=
    measurable_events_length.comp (measurable_events.comp hdecoded)
  have hcount : Measurable (fun h : History => n+h.horizon) :=
    (measurable_of_countable (fun k : ℕ => n+k)).comp measurable_history_horizon
  change Measurable (fun h => ValidDated L n h)
  simp_rw [validDated_iff_decoded]
  apply Measurable.and ((measurable_isSome.comp measurable_history_result).eq_const true)
  apply Measurable.and (hfinal.eq (measurable_some.comp hdecoded))
  apply Measurable.and ((measurable_valid n L).comp hdecoded)
  apply Measurable.and (hactive.eq_const 1)
  apply Measurable.and (hlen.eq measurable_history_horizon)
  apply Measurable.and ((measurable_nextVertex.comp hdecoded).eq hcount)
  apply Measurable.and
  · apply Measurable.forall
    intro i
    apply Measurable.imp (measurableSet_le measurable_history_horizon measurable_const).mem
    exact (((measurable_pi_apply i).comp measurable_history_states).eq hfinal).and
      (((measurable_pi_apply i).comp measurable_history_times).eq htime)
  · apply Measurable.forall
    intro i
    apply Measurable.imp ((measurable_completed_mem i).comp hdecoded)
    exact (measurableSet_lt
      (measurable_vertexDate n ((measurable_slot_child_at i).comp hdecoded))
      (measurable_vertexDate n ((measurable_parent_at i).comp hdecoded))).mem

/-- The ACTUAL pushforward law is concentrated on valid chronological finite
histories. This is a statement about output histories, not merely inputs. -/
theorem historyLaw_ae_validDated (L : ℝ) (hL : 0 < L) (n : ℕ) (hn : 0 < n)
    (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) :
    ∀ᵐ h ∂historyLaw L hL (WongBigARGAbsorption.normalizedRatio a b ha hb) n a b,
      ValidDated L n h := by
  unfold historyLaw
  rw [ae_map_iff (measurable_realize L hL n a b).aemeasurable (measurable_validDated L n).setOf]
  exact law_ae_realize_validDated L hL n hn a b ha hb

#print axioms measurable_validDated
#print axioms historyLaw_ae_validDated
end
end WongDatedSupport
