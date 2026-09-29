import WongMarkedProcess

set_option autoImplicit false

/-!
# Faithful Borel coding and measurability of the actual marked recorder

All sigma algebras below come from the ordinary Borel real coordinates and
countable discrete data of the representation, independently of any process
or law. The full raw state is retained: stable identities, all interval
endpoints, parent assignments, active frontier, and complete event log.
-/
namespace WongMarkedMeasurable
open MeasureTheory WongGARG WongMarkedRecorder WongMarkedProcess WongMarkedLaw WongWaitingTimes
open scoped Classical NNReal
noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

def intervalCode (I : Interval ℝ) : ℝ × ℝ := (I.lo,I.hi)
instance intervalMeasurableSpace : MeasurableSpace (Interval ℝ) :=
  MeasurableSpace.comap intervalCode inferInstance

theorem intervalCode_injective : Function.Injective intervalCode := by
  rintro ⟨a,b,h⟩ ⟨c,d,k⟩ he
  have he' : a = c ∧ b = d := Prod.mk.inj he
  rcases he' with ⟨rfl,rfl⟩
  rfl

@[fun_prop] theorem measurable_interval_lo : Measurable (fun I : Interval ℝ => I.lo) :=
  measurable_fst.comp (comap_measurable intervalCode)
@[fun_prop] theorem measurable_interval_hi : Measurable (fun I : Interval ℝ => I.hi) :=
  measurable_snd.comp (comap_measurable intervalCode)

theorem measurable_interval_mk {a b : Ω → ℝ} (ha : Measurable a) (hb : Measurable b)
    (h : ∀ ω, a ω < b ω) : Measurable (fun ω => (⟨a ω,b ω,h ω⟩ : Interval ℝ)) := by
  apply measurable_comap_iff.mpr
  exact ha.prodMk hb

def slotCode (s : Slot ℝ) : ℕ × Interval ℝ := (s.child,s.interval)
instance slotMeasurableSpace : MeasurableSpace (Slot ℝ) :=
  MeasurableSpace.comap slotCode inferInstance

theorem slotCode_injective : Function.Injective slotCode := by
  rintro ⟨a,b⟩ ⟨c,d⟩ he
  have he' : a = c ∧ b = d := Prod.mk.inj he
  rcases he' with ⟨rfl,rfl⟩
  rfl

@[fun_prop] theorem measurable_slot_child : Measurable (fun s : Slot ℝ => s.child) :=
  measurable_fst.comp (comap_measurable slotCode)
@[fun_prop] theorem measurable_slot_interval : Measurable (fun s : Slot ℝ => s.interval) :=
  measurable_snd.comp (comap_measurable slotCode)

theorem measurable_slot_mk {child : Ω → ℕ} {interval : Ω → Interval ℝ}
    (hc : Measurable child) (hI : Measurable interval) :
    Measurable (fun ω => (⟨child ω,interval ω⟩ : Slot ℝ)) := by
  apply measurable_comap_iff.mpr
  exact hc.prodMk hI

def kindCode : WongMarkedRecorder.EventKind ℝ → Bool × ℝ
  | .split x => (true,x)
  | .merge => (false,0)
instance kindMeasurableSpace : MeasurableSpace (WongMarkedRecorder.EventKind ℝ) :=
  MeasurableSpace.comap kindCode inferInstance

theorem kindCode_injective : Function.Injective kindCode := by
  intro a b h
  cases a <;> cases b <;> simp_all [kindCode]

@[fun_prop] theorem measurable_kind_split :
    Measurable (WongMarkedRecorder.EventKind.split : ℝ → WongMarkedRecorder.EventKind ℝ) := by
  apply measurable_comap_iff.mpr
  exact measurable_const.prodMk measurable_id

def eventCode (e : RawEvent ℝ) : ℕ × WongMarkedRecorder.EventKind ℝ × Finset ℕ × Finset ℕ :=
  (e.vertex,e.kind,e.consumed,e.allocated)
instance eventMeasurableSpace : MeasurableSpace (RawEvent ℝ) :=
  MeasurableSpace.comap eventCode inferInstance

theorem eventCode_injective : Function.Injective eventCode := by
  rintro ⟨a,b,c,d⟩ ⟨e,f,g,h⟩ he
  have he' : a = e ∧ b = f ∧ c = g ∧ d = h := by simpa [eventCode] using he
  rcases he' with ⟨rfl,rfl,rfl,rfl⟩
  rfl

theorem measurable_event_mk {v : Ω → ℕ} {k : Ω → WongMarkedRecorder.EventKind ℝ}
    {c a : Ω → Finset ℕ} (hv : Measurable v) (hk : Measurable k)
    (hc : Measurable c) (ha : Measurable a) :
    Measurable (fun ω => (⟨v ω,k ω,c ω,a ω⟩ : RawEvent ℝ)) := by
  apply measurable_comap_iff.mpr
  exact hv.prodMk (hk.prodMk (hc.prodMk ha))

def defaultEvent : RawEvent ℝ := ⟨0,.merge,∅,∅⟩
def eventNth (es : List (RawEvent ℝ)) (i : ℕ) : RawEvent ℝ := es[i]?.getD defaultEvent

def eventListCode (es : List (RawEvent ℝ)) : ℕ × (ℕ → RawEvent ℝ) :=
  (es.length,eventNth es)
instance eventListMeasurableSpace : MeasurableSpace (List (RawEvent ℝ)) :=
  MeasurableSpace.comap eventListCode inferInstance

theorem eventListCode_injective : Function.Injective eventListCode := by
  intro es fs h
  have hlen : es.length = fs.length := congrArg Prod.fst h
  have hn : eventNth es = eventNth fs := congrArg Prod.snd h
  apply List.ext_getElem hlen
  intro i hi hj
  have he := congrFun hn i
  simpa [eventNth, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj] using he

@[fun_prop] theorem measurable_events_length : Measurable (fun es : List (RawEvent ℝ) => es.length) :=
  measurable_fst.comp (comap_measurable eventListCode)
@[fun_prop] theorem measurable_eventNth (i : ℕ) : Measurable (fun es => eventNth es i) :=
  (measurable_pi_apply i).comp (measurable_snd.comp (comap_measurable eventListCode))

/-- Evaluation at a random countable index is measurable. -/
theorem measurable_dynamic {ι β : Type*} [MeasurableSpace ι] [Countable ι]
    [MeasurableSingletonClass ι] [MeasurableSpace β] {f : Ω → ι → β} {i : Ω → ι}
    (hf : Measurable f) (hi : Measurable i) : Measurable (fun ω => f ω (i ω)) := by
  have heval : Measurable (fun p : (ι → β) × ι => p.1 p.2) :=
    measurable_from_prod_countable_left (fun j => measurable_pi_apply j)
  exact heval.comp (hf.prodMk hi)

theorem eventNth_append_single (es : List (RawEvent ℝ)) (e : RawEvent ℝ) (i : ℕ) :
    eventNth (es ++ [e]) i =
      if i < es.length then eventNth es i else if i = es.length then e else defaultEvent := by
  by_cases hlt : i < es.length
  · simp [eventNth, List.getElem?_append_left hlt, hlt]
  · rw [eventNth, List.getElem?_append_right (by omega)]
    by_cases heq : i = es.length
    · simp [hlt,heq]
    · have hn : i - es.length ≠ 0 := by omega
      simp [hlt,heq, List.getElem?_cons, hn]

theorem measurable_events_snoc {es : Ω → List (RawEvent ℝ)} {e : Ω → RawEvent ℝ}
    (hes : Measurable es) (he : Measurable e) : Measurable (fun ω => es ω ++ [e ω]) := by
  apply measurable_comap_iff.mpr
  change Measurable (fun ω => ((es ω ++ [e ω]).length, eventNth (es ω ++ [e ω])))
  apply Measurable.prodMk
  · simpa [Function.comp_def] using (measurable_of_countable (fun k : ℕ => k + 1)).comp
      (measurable_events_length.comp hes)
  · apply measurable_pi_lambda
    intro i
    simp only [eventNth_append_single]
    apply Measurable.ite (measurableSet_lt measurable_const (measurable_events_length.comp hes))
    · exact (measurable_eventNth i).comp hes
    · exact Measurable.ite
        (measurableSet_eq_fun measurable_const (measurable_events_length.comp hes)) he measurable_const

def stateCode (s : RawState ℝ) :
    ℕ × ℕ × (ℕ → Slot ℝ) × (ℕ → ℕ) × Finset ℕ × List (RawEvent ℝ) :=
  (s.nextVertex,s.nextLineage,s.slot,s.parent,s.active,s.events)
instance stateMeasurableSpace : MeasurableSpace (RawState ℝ) :=
  MeasurableSpace.comap stateCode inferInstance

theorem stateCode_injective : Function.Injective stateCode := by
  rintro ⟨a,b,c,d,e,f⟩ ⟨g,h,i,j,k,l⟩ he
  have he' : a=g ∧ b=h ∧ c=i ∧ d=j ∧ e=k ∧ f=l := by simpa [stateCode] using he
  rcases he' with ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
  rfl

@[fun_prop] theorem measurable_nextVertex : Measurable (fun s : RawState ℝ => s.nextVertex) :=
  measurable_fst.comp (comap_measurable stateCode)
@[fun_prop] theorem measurable_nextLineage : Measurable (fun s : RawState ℝ => s.nextLineage) :=
  measurable_fst.comp (measurable_snd.comp (comap_measurable stateCode))
@[fun_prop] theorem measurable_slots : Measurable (fun s : RawState ℝ => s.slot) :=
  measurable_fst.comp (measurable_snd.comp (measurable_snd.comp (comap_measurable stateCode)))
@[fun_prop] theorem measurable_parents : Measurable (fun s : RawState ℝ => s.parent) :=
  measurable_fst.comp (measurable_snd.comp (measurable_snd.comp
    (measurable_snd.comp (comap_measurable stateCode))))
@[fun_prop] theorem measurable_active : Measurable (fun s : RawState ℝ => s.active) :=
  measurable_fst.comp (measurable_snd.comp (measurable_snd.comp
    (measurable_snd.comp (measurable_snd.comp (comap_measurable stateCode)))))
@[fun_prop] theorem measurable_events : Measurable (fun s : RawState ℝ => s.events) :=
  measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
    (measurable_snd.comp (measurable_snd.comp (comap_measurable stateCode)))))

theorem measurable_state_mk {v l : Ω → ℕ} {slots : Ω → ℕ → Slot ℝ} {parents : Ω → ℕ → ℕ}
    {active : Ω → Finset ℕ} {events : Ω → List (RawEvent ℝ)}
    (hv : Measurable v) (hl : Measurable l) (hs : Measurable slots) (hp : Measurable parents)
    (ha : Measurable active) (he : Measurable events) :
    Measurable (fun ω => (⟨v ω,l ω,slots ω,parents ω,active ω,events ω⟩ : RawState ℝ)) := by
  apply measurable_comap_iff.mpr
  exact hv.prodMk (hl.prodMk (hs.prodMk (hp.prodMk (ha.prodMk he))))

def defaultState : RawState ℝ := initial 0 (show (0 : ℝ) < 1 from zero_lt_one)
def optionCode (s : Option (RawState ℝ)) : Bool × RawState ℝ :=
  (s.isSome,s.getD defaultState)
instance optionStateMeasurableSpace : MeasurableSpace (Option (RawState ℝ)) :=
  MeasurableSpace.comap optionCode inferInstance

theorem optionCode_injective : Function.Injective optionCode := by
  intro a b h
  cases a <;> cases b <;> simp_all [optionCode]

@[fun_prop] theorem measurable_isSome : Measurable (fun s : Option (RawState ℝ) => s.isSome) :=
  measurable_fst.comp (comap_measurable optionCode)
@[fun_prop] theorem measurable_getD : Measurable (fun s : Option (RawState ℝ) => s.getD defaultState) :=
  measurable_snd.comp (comap_measurable optionCode)
@[fun_prop] theorem measurable_some : Measurable (some : RawState ℝ → Option (RawState ℝ)) := by
  apply measurable_comap_iff.mpr
  exact measurable_const.prodMk measurable_id

theorem measurable_freshIds {s : Ω → RawState ℝ} {m : Ω → ℕ}
    (hs : Measurable s) (hm : Measurable m) : Measurable (fun ω => freshIds (s ω) (m ω)) :=
  (measurable_of_countable (fun p : ℕ × ℕ => Finset.Ico p.1 (p.1+p.2))).comp
    ((measurable_nextLineage.comp hs).prodMk hm)

theorem measurable_advance {s : Ω → RawState ℝ} {selected : Ω → Finset ℕ} {m : Ω → ℕ}
    {intervals : Ω → ℕ → Interval ℝ} {kind : Ω → WongMarkedRecorder.EventKind ℝ}
    (hs : Measurable s) (hsel : Measurable selected) (hm : Measurable m)
    (hI : Measurable intervals) (hk : Measurable kind) :
    Measurable (fun ω => advance (s ω) (selected ω) (m ω) (intervals ω) (kind ω)) := by
  apply measurable_state_mk
  · exact (measurable_of_countable (fun k : ℕ => k+1)).comp (measurable_nextVertex.comp hs)
  · exact (measurable_of_countable (fun p : ℕ×ℕ => p.1+p.2)).comp
      ((measurable_nextLineage.comp hs).prodMk hm)
  · apply measurable_pi_lambda
    intro i
    apply Measurable.ite (measurableSet_lt measurable_const (measurable_nextLineage.comp hs))
    · exact (measurable_pi_apply i).comp (measurable_slots.comp hs)
    · apply measurable_slot_mk (measurable_nextVertex.comp hs)
      apply measurable_dynamic hI
      exact (measurable_of_countable (fun k : ℕ => i-k)).comp (measurable_nextLineage.comp hs)
  · apply measurable_pi_lambda
    intro i
    have hmem : MeasurableSet {ω | i ∈ selected ω} :=
      hsel ((Set.to_countable {a : Finset ℕ | i ∈ a}).measurableSet)
    exact Measurable.ite hmem (measurable_nextVertex.comp hs)
      ((measurable_pi_apply i).comp (measurable_parents.comp hs))
  · exact (measurable_of_countable (fun p : (Finset ℕ × Finset ℕ) × Finset ℕ =>
      (p.1.1 \ p.1.2) ∪ p.2)).comp
        (((measurable_active.comp hs).prodMk hsel).prodMk (measurable_freshIds hs hm))
  · apply measurable_events_snoc (measurable_events.comp hs)
    exact measurable_event_mk (measurable_nextVertex.comp hs) hk hsel (measurable_freshIds hs hm)

theorem measurable_split {L : ℝ} {s : Ω → RawState ℝ} {i : Ω → ℕ} {cut : Ω → Cut (0 : ℝ) L}
    (hs : Measurable s) (hi : Measurable i) (hc : Measurable cut) :
    Measurable (fun ω => split (s ω) (i ω) (cut ω)) := by
  apply measurable_advance hs ((measurable_of_countable (fun j : ℕ => ({j} : Finset ℕ))).comp hi)
    measurable_const
  · apply measurable_pi_lambda
    intro j
    by_cases hj : j=0
    · simp only [splitIntervals,hj,if_pos rfl]
      exact measurable_interval_mk measurable_const hc.subtype_coe (fun ω => (cut ω).property.1)
    · simp only [splitIntervals,if_neg hj]
      exact measurable_interval_mk hc.subtype_coe measurable_const (fun ω => (cut ω).property.2)
  · exact measurable_kind_split.comp hc.subtype_coe

theorem measurable_merge {L : ℝ} (hL : 0 < L) {s : Ω → RawState ℝ} {i j : Ω → ℕ}
    (hs : Measurable s) (hi : Measurable i) (hj : Measurable j) :
    Measurable (fun ω => merge (s ω) (i ω) (j ω) hL) := by
  apply measurable_advance hs
    ((measurable_of_countable (fun p : ℕ×ℕ => ({p.1,p.2} : Finset ℕ))).comp (hi.prodMk hj))
    measurable_const measurable_const measurable_const

/-- A total countable lookup for the merger identities. Its off-domain value
is used only outside the guarded merger branch and creates no event. -/
def totalPair (p : Finset ℕ) : ℕ × ℕ :=
  if h : p.card = 2 then (pairIDs p h).val else (0,0)

theorem measurable_step {L : ℝ} (hL : 0 < L)
    {s : Ω → RawState ℝ} {next : Ω → ℕ} {mark : Ω → SpatialMark}
    (hs : Measurable s) (hn : Measurable next) (hm : Measurable mark) :
    Measurable (fun ω => step L hL (s ω) (next ω) (mark ω)) := by
  have hactive := measurable_active.comp hs
  have hcard : Measurable (fun ω => (s ω).active.card) :=
    (measurable_of_countable (fun A : Finset ℕ => A.card)).comp hactive
  have hup : MeasurableSet {ω | next ω = (s ω).active.card + 1} :=
    measurableSet_eq_fun hn ((measurable_of_countable (fun k : ℕ => k+1)).comp hcard)
  have hdown : MeasurableSet {ω | next ω + 1 = (s ω).active.card} :=
    measurableSet_eq_fun ((measurable_of_countable (fun k : ℕ => k+1)).comp hn) hcard
  have hlineage : MeasurableSet {ω | (mark ω).1 ∈ (s ω).active} :=
    (hm.fst.prodMk hactive) ((Set.to_countable {p : ℕ × Finset ℕ | p.1 ∈ p.2}).measurableSet)
  have hcutlo : MeasurableSet {ω | 0 < (mark ω).2.2} := measurableSet_lt measurable_const hm.snd.snd
  have hcuthi : MeasurableSet {ω | (mark ω).2.2 < L} := measurableSet_lt hm.snd.snd measurable_const
  have hsplitset : MeasurableSet {ω | (mark ω).1 ∈ (s ω).active ∧
      0 < (mark ω).2.2 ∧ (mark ω).2.2 < L} := hlineage.inter (hcutlo.inter hcuthi)
  have hmergeset : MeasurableSet {ω | (mark ω).2.1 ⊆ (s ω).active ∧ (mark ω).2.1.card = 2} :=
    (hm.snd.fst.prodMk hactive)
      ((Set.to_countable {p : Finset ℕ × Finset ℕ | p.1 ⊆ p.2 ∧ p.1.card = 2}).measurableSet)
  unfold step
  apply Measurable.ite hup
  · let A : Set Ω := {ω | (mark ω).1 ∈ (s ω).active ∧
        0 < (mark ω).2.2 ∧ (mark ω).2.2 < L}
    have hfunc : Measurable (fun ω : A => some (split (s ω.val) (mark ω.val).1
        (⟨(mark ω.val).2.2, ω.property.2⟩ : Cut (0 : ℝ) L))) := by
      apply measurable_some.comp
      apply measurable_split (hs.comp measurable_subtype_coe) (hm.fst.comp measurable_subtype_coe)
      exact (hm.snd.snd.comp measurable_subtype_coe).subtype_mk
    exact Measurable.dite hfunc (measurable_const (a := (none : Option (RawState ℝ)))) hsplitset
  · apply Measurable.ite hdown
    · let B : Set Ω := {ω | (mark ω).2.1 ⊆ (s ω).active ∧ (mark ω).2.1.card = 2}
      have hpair : Measurable (fun ω : B => totalPair (mark ω.val).2.1) :=
        (measurable_of_countable totalPair).comp (hm.snd.fst.comp measurable_subtype_coe)
      have hmerge := measurable_some.comp
        (measurable_merge hL (hs.comp measurable_subtype_coe) hpair.fst hpair.snd)
      have hfunc : Measurable (fun ω : B => some (merge (s ω.val)
          (pairIDs (mark ω.val).2.1 ω.property.2).val.1
          (pairIDs (mark ω.val).2.1 ω.property.2).val.2 hL)) := by
        convert hmerge using 1
        funext ω
        simp [totalPair, ω.property.2, Function.comp_def]
      exact Measurable.dite hfunc (measurable_const (a := (none : Option (RawState ℝ)))) hmergeset
    · exact measurable_const

/-- The totalized recursion is measurable from precisely the coordinates it
uses. Future innovation rows and all clock innovations are irrelevant here. -/
theorem measurable_recordPrefix_of_coordinates (L : ℝ) (hL : 0 < L) (n t : ℕ)
    (F : Ω → WongMarkedLaw.Sample)
    (hcounts : ∀ j, j ≤ t → Measurable (fun ω => (F ω).1.1 j))
    (hmarks : ∀ j, j < t → ∀ A : Finset ℕ, Measurable (fun ω => (F ω).2 (j,A))) :
    Measurable (fun ω => recordPrefix L hL n (F ω) t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
      have hprior := ih (fun j hj => hcounts j (by omega)) (fun j hj A => hmarks j (by omega) A)
      have hstate : Measurable (fun ω => (recordPrefix L hL n (F ω) t).getD defaultState) :=
        measurable_getD.comp hprior
      have hrow : Measurable (fun ω => fun A : Finset ℕ => (F ω).2 (t,A)) :=
        measurable_pi_lambda _ (fun A => hmarks t (by omega) A)
      have hselected := measurable_dynamic hrow (measurable_active.comp hstate)
      have hstep := measurable_step hL hstate (hcounts (t+1) le_rfl) hselected
      have hpresent : MeasurableSet {ω | (recordPrefix L hL n (F ω) t).isSome = true} :=
        measurableSet_eq_fun (measurable_isSome.comp hprior) measurable_const
      have hif : Measurable (fun ω =>
          if (recordPrefix L hL n (F ω) t).isSome = true then
            step L hL ((recordPrefix L hL n (F ω) t).getD defaultState) ((F ω).1.1 (t+1))
              ((F ω).2 (t, ((recordPrefix L hL n (F ω) t).getD defaultState).active))
          else none) :=
        Measurable.ite hpresent hstep measurable_const
      convert hif using 1
      funext ω
      cases he : recordPrefix L hL n (F ω) t <;> simp [recordPrefix,he]

theorem measurable_recordPrefix (L : ℝ) (hL : 0 < L) (n t : ℕ) :
    Measurable (fun z : WongMarkedLaw.Sample => recordPrefix L hL n z t) := by
  apply measurable_recordPrefix_of_coordinates L hL n t id
  · intro j hj
    exact (measurable_pi_apply j).comp (measurable_fst.comp measurable_fst)
  · intro j hj A
    exact (measurable_pi_apply (j,A)).comp measurable_snd

/-- Full stopped record measurability uses the countable first-hit index;
it retains every slot, interval endpoint, parent and event-log identity. -/
theorem measurable_stoppedRecord (L : ℝ) (hL : 0 < L) (n : ℕ) :
    Measurable (stoppedRecord L hL n) := by
  have htime : Measurable (fun z : WongMarkedLaw.Sample => firstHit z.1.1) :=
    measurable_firstHit.comp (measurable_fst.comp measurable_fst)
  have hprefixes : Measurable (fun z : WongMarkedLaw.Sample => fun t => recordPrefix L hL n z t) :=
    measurable_pi_lambda _ (fun t => measurable_recordPrefix L hL n t)
  have hfold := measurable_dynamic hprefixes htime
  have hstart : MeasurableSet {z : WongMarkedLaw.Sample | z.1.1 0 = n} :=
    measurableSet_eq_fun ((measurable_pi_apply 0).comp (measurable_fst.comp measurable_fst)) measurable_const
  have hhits : MeasurableSet {z : WongMarkedLaw.Sample | hitsOne z.1.1} :=
    measurableSet_hitsOne.preimage (measurable_fst.comp measurable_fst)
  have hgood : MeasurableSet {z : WongMarkedLaw.Sample | 0 < n ∧ z.1.1 0 = n ∧ hitsOne z.1.1} := by
    by_cases hn : 0 < n
    · convert hstart.inter hhits using 1
      ext z
      simp [hn]
    · simp [hn]
  exact Measurable.ite hgood hfold measurable_const

/-- The actual stopped graph-data law on its natural Borel coordinates. -/
def stoppedRecordLaw (L : ℝ) (hL : 0 < L) (θ : ℝ≥0) (n : ℕ) :
    Measure (Option (RawState ℝ)) := (law L hL θ n).map (stoppedRecord L hL n)

instance stoppedRecordLaw_probability (L : ℝ) (hL : 0 < L) (θ : ℝ≥0) (n : ℕ) :
    IsProbabilityMeasure (stoppedRecordLaw L hL θ n) :=
  Measure.isProbabilityMeasure_map (measurable_stoppedRecord L hL n).aemeasurable

#print axioms stateCode_injective
#print axioms eventListCode_injective
#print axioms measurable_advance
#print axioms measurable_step
#print axioms measurable_recordPrefix_of_coordinates
#print axioms measurable_stoppedRecord
#print axioms stoppedRecordLaw_probability
end
end WongMarkedMeasurable


