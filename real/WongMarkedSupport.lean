import WongMarkedMeasurable

set_option autoImplicit false

/-!
# Borel support of the finite marked recorder

Exact genomic coverage quantifies over every real coordinate. For a finite
family of half-open intervals, its membership pattern at x persists to the
right of x until the next endpoint. A rational witness in that interval
therefore detects every failure of exact coverage. This makes raw validity
a countable Borel condition in the existing natural coordinate sigma algebra.
-/
namespace WongMarkedSupport
open MeasureTheory WongGARG WongMarkedRecorder WongMarkedMeasurable WongMarkedLaw WongMarkedProcess
open scoped Classical NNReal
noncomputable section

/-- Stay below every one of finitely many thresholds that lies to the right
of x, while remaining strictly to its right and below L. -/
theorem finite_right_bound (S : Finset ℝ) (x L : ℝ) (hx : x < L) :
    ∃ y, x < y ∧ y < L ∧ ∀ b ∈ S, x < b → y < b := by
  induction S using Finset.induction_on generalizing L with
  | empty =>
      obtain ⟨y,hxy,hyL⟩ := exists_between hx
      exact ⟨y,hxy,hyL,by simp⟩
  | @insert b S hnot ih =>
      by_cases hxb : x < b
      · obtain ⟨y,hxy,hy,hyS⟩ := ih (min L b) (lt_min hx hxb)
        refine ⟨y,hxy,(lt_min_iff.mp hy).1,?_⟩
        intro c hc hxc
        rcases Finset.mem_insert.mp hc with rfl | hc
        · exact (lt_min_iff.mp hy).2
        · exact hyS c hc hxc
      · obtain ⟨y,hxy,hyL,hyS⟩ := ih L hx
        refine ⟨y,hxy,hyL,?_⟩
        intro c hc hxc
        rcases Finset.mem_insert.mp hc with rfl | hc
        · exact False.elim (hxb hxc)
        · exact hyS c hc hxc

/-- A rational coordinate preserves the simultaneous membership pattern of
all allocated lineage intervals, including points exactly on boundaries. -/
theorem rational_slot_pattern (s : RawState ℝ) (x L : ℝ) (hx : x < L) :
    ∃ q : ℚ, x < (q : ℝ) ∧ (q : ℝ) < L ∧
      ∀ i, i < s.nextLineage →
        ((s.slot i).interval.Contains x ↔ (s.slot i).interval.Contains (q : ℝ)) := by
  let endpoints : Finset ℝ := (Finset.range s.nextLineage).biUnion
    (fun i => {(s.slot i).interval.lo,(s.slot i).interval.hi})
  obtain ⟨y,hxy,hyL,hyS⟩ := finite_right_bound endpoints x L hx
  obtain ⟨q,hxq,hqy⟩ := exists_rat_btwn hxy
  refine ⟨q,hxq,lt_trans hqy hyL,?_⟩
  intro i hi
  have hlo : (s.slot i).interval.lo ∈ endpoints := by
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_range.mpr hi,by simp⟩
  have hhi : (s.slot i).interval.hi ∈ endpoints := by
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_range.mpr hi,by simp⟩
  have compare : ∀ b ∈ endpoints, x < b ↔ (q : ℝ) < b := by
    intro b hb
    constructor
    · intro hxb; exact lt_trans hqy (hyS b hb hxb)
    · intro hqb; exact lt_trans hxq hqb
  constructor
  · intro h
    exact ⟨le_trans h.1 (le_of_lt hxq), (compare _ hhi).mp h.2⟩
  · intro h
    refine ⟨?_,(compare _ hhi).mpr h.2⟩
    by_contra hn
    have hxl : x < (s.slot i).interval.lo := lt_of_not_ge hn
    exact (not_lt_of_ge h.1) ((compare _ hlo).mp hxl)

def RationalCoverage (L : ℝ) (s : RawState ℝ) : Prop :=
  ∀ v, v < s.nextVertex → ∀ q : ℚ, 0 ≤ (q : ℝ) ∧ (q : ℝ) < L →
    ∃! i, SlotAt s v (q : ℝ) i

theorem coverage_iff_rational (L : ℝ) (s : RawState ℝ) :
    (∀ v, v < s.nextVertex → ∀ x : ℝ, 0 ≤ x ∧ x < L → ∃! i, SlotAt s v x i) ↔
      RationalCoverage L s := by
  constructor
  · intro h v hv q hq; exact h v hv q hq
  · intro h v hv x hx
    obtain ⟨q,hxq,hqL,hpattern⟩ := rational_slot_pattern s x L hx.2
    obtain ⟨i,hi,hunique⟩ := h v hv q ⟨le_trans hx.1 (le_of_lt hxq),hqL⟩
    refine ⟨i,⟨hi.1,hi.2.1,(hpattern i hi.1).mpr hi.2.2⟩,?_⟩
    intro j hj
    exact hunique j ⟨hj.1,hj.2.1,(hpattern j hj.1).mp hj.2.2⟩

theorem valid_iff_rational (n : ℕ) (L : ℝ) (s : RawState ℝ) :
    Valid n 0 L s ↔
      s.nextVertex = n+s.events.length ∧
      (∀ i, i ∈ s.active → i < s.nextLineage) ∧
      (∀ i, i < s.nextLineage → (s.slot i).child < s.nextVertex ∧
        0 ≤ (s.slot i).interval.lo ∧ (s.slot i).interval.hi ≤ L) ∧
      (∀ i, i ∈ s.completed → (s.slot i).child < s.parent i ∧ s.parent i < s.nextVertex) ∧
      (∀ i, i ∈ s.completed → n ≤ s.parent i) ∧ RationalCoverage L s := by
  constructor
  · intro h
    exact ⟨h.vertices,h.active_bound,h.slot_bound,h.parent_order,h.parent_nonsample,
      (coverage_iff_rational L s).mp h.coverage⟩
  · rintro ⟨hv,ha,hs,hp,hn,hc⟩
    exact ⟨hv,ha,hs,hp,hn,(coverage_iff_rational L s).mpr hc⟩

@[fun_prop] theorem measurable_completed : Measurable (fun s : RawState ℝ => s.completed) :=
  (measurable_of_countable (fun p : ℕ × Finset ℕ => Finset.range p.1 \ p.2)).comp
    (measurable_nextLineage.prodMk measurable_active)

theorem measurable_active_mem (i : ℕ) : Measurable (fun s : RawState ℝ => i ∈ s.active) := by
  exact (measurable_active ((Set.to_countable {A : Finset ℕ | i ∈ A}).measurableSet)).mem

theorem measurable_completed_mem (i : ℕ) : Measurable (fun s : RawState ℝ => i ∈ s.completed) := by
  exact (measurable_completed ((Set.to_countable {A : Finset ℕ | i ∈ A}).measurableSet)).mem

@[fun_prop] theorem measurable_slot_child_at (i : ℕ) :
    Measurable (fun s : RawState ℝ => (s.slot i).child) :=
  measurable_slot_child.comp ((measurable_pi_apply i).comp measurable_slots)
@[fun_prop] theorem measurable_slot_lo_at (i : ℕ) :
    Measurable (fun s : RawState ℝ => (s.slot i).interval.lo) :=
  measurable_interval_lo.comp (measurable_slot_interval.comp
    ((measurable_pi_apply i).comp measurable_slots))
@[fun_prop] theorem measurable_slot_hi_at (i : ℕ) :
    Measurable (fun s : RawState ℝ => (s.slot i).interval.hi) :=
  measurable_interval_hi.comp (measurable_slot_interval.comp
    ((measurable_pi_apply i).comp measurable_slots))
@[fun_prop] theorem measurable_parent_at (i : ℕ) :
    Measurable (fun s : RawState ℝ => s.parent i) :=
  (measurable_pi_apply i).comp measurable_parents

theorem measurable_slotAt (v i : ℕ) (x : ℝ) : Measurable (fun s : RawState ℝ => SlotAt s v x i) := by
  exact ((measurableSet_lt measurable_const measurable_nextLineage).mem).and
    (((measurable_slot_child_at i).eq_const v).and
      (((measurableSet_le (measurable_slot_lo_at i) measurable_const).mem).and
        (measurableSet_lt measurable_const (measurable_slot_hi_at i)).mem))

theorem measurable_exactSlot (v : ℕ) (x : ℝ) :
    Measurable (fun s : RawState ℝ => ∃! i, SlotAt s v x i) := by
  apply Measurable.exists
  intro i
  apply Measurable.and (measurable_slotAt v i x)
  apply Measurable.forall
  intro j
  exact (measurable_slotAt v j x).imp measurable_const

theorem measurable_rationalCoverage (L : ℝ) : Measurable (RationalCoverage L) := by
  apply Measurable.forall
  intro v
  apply Measurable.imp (measurableSet_lt measurable_const measurable_nextVertex).mem
  apply Measurable.forall
  intro q
  exact Measurable.imp measurable_const (measurable_exactSlot v (q : ℝ))

/-- Full validity, including exact coverage at every real locus, is Borel in
the already fixed natural raw-state representation. -/
theorem measurable_valid (n : ℕ) (L : ℝ) : Measurable (fun s : RawState ℝ => Valid n 0 L s) := by
  simp_rw [valid_iff_rational]
  apply Measurable.and
  · exact (measurableSet_eq_fun measurable_nextVertex
      ((measurable_of_countable (fun k : ℕ => n+k)).comp
        (measurable_events_length.comp measurable_events))).mem
  · apply Measurable.and
    · apply Measurable.forall
      intro i
      exact (measurable_active_mem i).imp (measurableSet_lt measurable_const measurable_nextLineage).mem
    · apply Measurable.and
      · apply Measurable.forall
        intro i
        apply Measurable.imp (measurableSet_lt measurable_const measurable_nextLineage).mem
        exact ((measurableSet_lt (measurable_slot_child_at i) measurable_nextVertex).mem).and
          (((measurableSet_le measurable_const (measurable_slot_lo_at i)).mem).and
            (measurableSet_le (measurable_slot_hi_at i) measurable_const).mem)
      · apply Measurable.and
        · apply Measurable.forall
          intro i
          exact (measurable_completed_mem i).imp
            (((measurableSet_lt (measurable_slot_child_at i) (measurable_parent_at i)).mem).and
              (measurableSet_lt (measurable_parent_at i) measurable_nextVertex).mem)
        · apply Measurable.and
          · apply Measurable.forall
            intro i
            exact (measurable_completed_mem i).imp
              (measurableSet_le measurable_const (measurable_parent_at i)).mem
          · exact measurable_rationalCoverage L

theorem measurableSet_valid (n : ℕ) (L : ℝ) :
    MeasurableSet {s : RawState ℝ | Valid n 0 L s} := (measurable_valid n L).setOf

#print axioms rational_slot_pattern
#print axioms coverage_iff_rational
#print axioms measurableSet_valid
end
end WongMarkedSupport
