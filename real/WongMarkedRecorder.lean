import WongEventDecoding
import Mathlib.Order.Interval.Finset.Nat

/-!
# Deterministic marked Big-ARG recording with stable lineage identities

The raw recorder implements the pre-sample-resolution events of Wong et al.,
Appendix B. An allocated lineage is a stable rootward slot, not an endpoint
pair. Completion changes its parent status but preserves its identity and
interval. In particular two lineages with the same child may merge.

This file proves deterministic finite-history claims. No stochastic law,
uniform distribution, random finite stopping, or source correspondence of a
probability measure is inferred from these deterministic statements.
-/
namespace WongMarkedRecorder
open WongGARG WongEventEncoding AncestryViews
universe u
noncomputable section
local instance (α : Type*) : DecidableEq α := Classical.decEq α
local instance (P : Prop) : Decidable P := Classical.propDecidable P

variable {Coord : Type u} [LinearOrder Coord] {lo hi : Coord}

structure Slot (Coord : Type u) [LinearOrder Coord] where
  child : Nat
  interval : Interval Coord

inductive EventKind (Coord : Type u) where
  | split (cut : Coord)
  | merge
  deriving DecidableEq

structure RawEvent (Coord : Type u) where
  vertex : Nat
  kind : EventKind Coord
  consumed : Finset Nat
  allocated : Finset Nat

/-- Entries below `nextLineage` are allocated exactly once. `parent i` is
meaningful precisely when i is allocated and is no longer active. -/
structure RawState (Coord : Type u) [LinearOrder Coord] where
  nextVertex : Nat
  nextLineage : Nat
  slot : Nat → Slot Coord
  parent : Nat → Nat
  active : Finset Nat
  events : List (RawEvent Coord)

abbrev Cut (lo hi : Coord) := {x : Coord // lo < x ∧ x < hi}

def RawState.completed (s : RawState Coord) : Finset Nat :=
  Finset.range s.nextLineage \ s.active

def Bounded (I : Interval Coord) : Prop := lo ≤ I.lo ∧ I.hi ≤ hi

def SlotAt (s : RawState Coord) (v : Nat) (x : Coord) (i : Nat) : Prop :=
  i < s.nextLineage ∧ (s.slot i).child = v ∧ (s.slot i).interval.Contains x

/-- A separate predicate, proved for initialization and the actual updates.
Coverage counts stable lineage IDs across *both* resolved and active slots. -/
structure Valid (n : Nat) (lo hi : Coord) (s : RawState Coord) : Prop where
  vertices : s.nextVertex = n + s.events.length
  active_bound : ∀ i ∈ s.active, i < s.nextLineage
  slot_bound : ∀ i, i < s.nextLineage →
    (s.slot i).child < s.nextVertex ∧ Bounded (lo := lo) (hi := hi) (s.slot i).interval
  parent_order : ∀ i ∈ s.completed,
    (s.slot i).child < s.parent i ∧ s.parent i < s.nextVertex
  parent_nonsample : ∀ i ∈ s.completed, n ≤ s.parent i
  coverage : ∀ v, v < s.nextVertex → ∀ x, lo ≤ x ∧ x < hi →
    ∃! i, SlotAt s v x i

def initial (n : Nat) (hspan : lo < hi) : RawState Coord where
  nextVertex := n
  nextLineage := n
  slot := fun i => ⟨i, ⟨lo, hi, hspan⟩⟩
  parent := fun _ => 0
  active := Finset.range n
  events := []

theorem initial_valid (n : Nat) (hspan : lo < hi) : Valid n lo hi (initial n hspan) := by
  constructor
  · simp [initial]
  · intro i hi; exact Finset.mem_range.mp hi
  · intro i hi; exact ⟨hi, le_rfl, le_rfl⟩
  · simp [RawState.completed, initial]
  · simp [RawState.completed, initial]
  · intro v hv x hx
    refine ⟨v, ⟨hv, rfl, hx⟩, ?_⟩
    intro i hi
    exact hi.2.1

/-- The fresh IDs form an interval disjoint from all earlier allocated IDs. -/
def freshIds (s : RawState Coord) (m : Nat) : Finset Nat :=
  Finset.Ico s.nextLineage (s.nextLineage + m)

@[simp] theorem mem_freshIds (s : RawState Coord) (m i : Nat) :
    i ∈ freshIds s m ↔ s.nextLineage ≤ i ∧ i < s.nextLineage + m := by
  simp [freshIds]

@[simp] theorem card_freshIds (s : RawState Coord) (m : Nat) :
    (freshIds s m).card = m := by
  simp [freshIds]

/-- General allocation step. All selected slots keep the old child/interval;
their parent becomes the fresh vertex. Fresh slots cover the fresh genome. -/
def advance (s : RawState Coord) (selected : Finset Nat) (m : Nat)
    (intervals : Nat → Interval Coord) (kind : EventKind Coord) : RawState Coord where
  nextVertex := s.nextVertex + 1
  nextLineage := s.nextLineage + m
  slot := fun i => if i < s.nextLineage then s.slot i
    else ⟨s.nextVertex, intervals (i - s.nextLineage)⟩
  parent := fun i => if i ∈ selected then s.nextVertex else s.parent i
  active := (s.active \ selected) ∪ freshIds s m
  events := s.events ++ [⟨s.nextVertex, kind, selected, freshIds s m⟩]

@[simp] theorem advance_old_slot (s : RawState Coord) (selected : Finset Nat) (m : Nat)
    (intervals : Nat → Interval Coord) (kind : EventKind Coord) {i : Nat}
    (hi : i < s.nextLineage) :
    (advance s selected m intervals kind).slot i = s.slot i := by
  simp [advance, hi]

@[simp] theorem advance_fresh_slot (s : RawState Coord) (selected : Finset Nat) (m : Nat)
    (intervals : Nat → Interval Coord) (kind : EventKind Coord) (j : Nat) :
    (advance s selected m intervals kind).slot (s.nextLineage + j) =
      ⟨s.nextVertex, intervals j⟩ := by
  simp [advance]

@[simp] theorem advance_active_old (s : RawState Coord) (selected : Finset Nat) (m : Nat)
    (intervals : Nat → Interval Coord) (kind : EventKind Coord) {i : Nat}
    (hi : i < s.nextLineage) :
    i ∈ (advance s selected m intervals kind).active ↔ i ∈ s.active ∧ i ∉ selected := by
  simp [advance, Finset.mem_sdiff, mem_freshIds, not_le_of_gt hi]

@[simp] theorem advance_active_new (s : RawState Coord) (selected : Finset Nat) (m : Nat)
    (intervals : Nat → Interval Coord) (kind : EventKind Coord) (j : Nat) (hj : j < m) :
    s.nextLineage + j ∈ (advance s selected m intervals kind).active := by
  simp [advance, mem_freshIds, hj]

/-- Preservation uses only the small partition of intervals assigned to the
new node. It does not assume the resulting graph or complete state is valid. -/
theorem advance_valid {n : Nat} {s : RawState Coord} (hs : Valid n lo hi s)
    (selected : Finset Nat) (hselected : selected ⊆ s.active) (m : Nat)
    (intervals : Nat → Interval Coord) (kind : EventKind Coord)
    (hbounds : ∀ j, j < m → Bounded (lo := lo) (hi := hi) (intervals j))
    (hpartition : ∀ x, lo ≤ x ∧ x < hi → ∃! j, j < m ∧ (intervals j).Contains x) :
    Valid n lo hi (advance s selected m intervals kind) := by
  constructor
  · simp [advance, hs.vertices, Nat.add_assoc]
  · intro i hi
    change i < s.nextLineage + m
    simp only [advance, Finset.mem_union, Finset.mem_sdiff, mem_freshIds] at hi
    rcases hi with hi | hi
    · have := hs.active_bound i hi.1; omega
    · exact hi.2
  · intro i hi
    change i < s.nextLineage + m at hi
    by_cases hold : i < s.nextLineage
    · rw [advance_old_slot s selected m intervals kind hold]
      exact ⟨Nat.lt_succ_of_lt (hs.slot_bound i hold).1, (hs.slot_bound i hold).2⟩
    · have hnew : s.nextLineage ≤ i := Nat.le_of_not_gt hold
      have hj : i - s.nextLineage < m := by omega
      simp only [advance, if_neg hold]
      exact ⟨Nat.lt_succ_self _, hbounds _ hj⟩
  · intro i hi
    simp only [RawState.completed, Finset.mem_sdiff, Finset.mem_range] at hi
    have hold : i < s.nextLineage := by
      by_contra hn
      have hfresh : i ∈ freshIds s m := (mem_freshIds s m i).mpr ⟨by omega, hi.1⟩
      exact hi.2 (Finset.mem_union.mpr (Or.inr hfresh))
    rw [advance_old_slot s selected m intervals kind hold]
    by_cases hsel : i ∈ selected
    · simp only [advance, if_pos hsel]
      exact ⟨(hs.slot_bound i hold).1, Nat.lt_succ_self _⟩
    · have hnot : i ∉ s.active := by
        intro hact
        exact hi.2 ((advance_active_old s selected m intervals kind hold).mpr ⟨hact, hsel⟩)
      have hp := hs.parent_order i (by simp [RawState.completed, hold, hnot])
      simp only [advance, if_neg hsel]
      exact ⟨hp.1, Nat.lt_succ_of_lt hp.2⟩
  · intro i hi
    simp only [RawState.completed, Finset.mem_sdiff, Finset.mem_range] at hi
    have hold : i < s.nextLineage := by
      by_contra hn
      have hfresh : i ∈ freshIds s m := (mem_freshIds s m i).mpr ⟨by omega, hi.1⟩
      exact hi.2 (Finset.mem_union.mpr (Or.inr hfresh))
    by_cases hsel : i ∈ selected
    · simp only [advance, if_pos hsel]
      have hv := hs.vertices
      omega
    · have hnot : i ∉ s.active := by
        intro hact
        exact hi.2 ((advance_active_old s selected m intervals kind hold).mpr ⟨hact, hsel⟩)
      simpa only [advance, if_neg hsel] using
        hs.parent_nonsample i (by simp [RawState.completed, hold, hnot])
  · intro v hv x hx
    change v < s.nextVertex + 1 at hv
    by_cases hvold : v < s.nextVertex
    · obtain ⟨i, hi, huniq⟩ := hs.coverage v hvold x hx
      refine ⟨i, ?_, ?_⟩
      · exact ⟨by change i < s.nextLineage + m; have hil := hi.1; omega,
          by simpa only [advance_old_slot s selected m intervals kind hi.1] using hi.2⟩
      · intro j hj
        have hjold : j < s.nextLineage := by
          by_contra hn
          have hc : ((advance s selected m intervals kind).slot j).child = s.nextVertex := by
            simp [advance, hn]
          have hjchild := hj.2.1
          rw [hc] at hjchild
          omega
        exact huniq j ⟨hjold, by
          simpa only [advance_old_slot s selected m intervals kind hjold] using hj.2⟩
    · have hveq : v = s.nextVertex := by omega
      subst v
      obtain ⟨j, hj, huniq⟩ := hpartition x hx
      refine ⟨s.nextLineage + j, ?_, ?_⟩
      · refine ⟨by change s.nextLineage + j < s.nextLineage + m; omega, ?_⟩
        rw [advance_fresh_slot]
        exact ⟨rfl, hj.2⟩
      · intro i hi
        have hnew : s.nextLineage ≤ i := by
          by_contra hn
          have hold : i < s.nextLineage := by omega
          have hc := (hs.slot_bound i hold).1
          have hiceq := hi.2.1
          rw [advance_old_slot s selected m intervals kind hold] at hiceq
          omega
        have hidecomp : i = s.nextLineage + (i - s.nextLineage) := by omega
        have hji : i - s.nextLineage = j := by
          apply huniq
          refine ⟨by have := hi.1; change i < s.nextLineage + m at this; omega, ?_⟩
          have hcover := hi.2.2
          rw [hidecomp, advance_fresh_slot] at hcover
          exact hcover
        omega

theorem advance_count {n : Nat} {s : RawState Coord} (hs : Valid n lo hi s)
    (selected : Finset Nat) (hselected : selected ⊆ s.active) (m : Nat)
    (intervals : Nat → Interval Coord) (kind : EventKind Coord) :
    (advance s selected m intervals kind).active.card + selected.card = s.active.card + m := by
  have hd : Disjoint (s.active \ selected) (freshIds s m) := by
    apply Finset.disjoint_left.mpr
    intro i hi hf
    have ho := hs.active_bound i (Finset.mem_sdiff.mp hi).1
    have hn := (mem_freshIds s m i).mp hf
    omega
  change ((s.active \ selected) ∪ freshIds s m).card + selected.card = _
  rw [Finset.card_union_of_disjoint hd, card_freshIds]
  have hc := Finset.card_sdiff_add_card_eq_card hselected
  omega

def splitIntervals (cut : Cut lo hi) : Nat → Interval Coord :=
  fun j => if j = 0 then ⟨lo, cut.val, cut.property.1⟩ else ⟨cut.val, hi, cut.property.2⟩

def split (s : RawState Coord) (i : Nat) (cut : Cut lo hi) : RawState Coord :=
  advance s {i} 2 (splitIntervals cut) (.split cut.val)

def merge (s : RawState Coord) (i j : Nat) (hspan : lo < hi) : RawState Coord :=
  advance s {i,j} 1 (fun _ => ⟨lo, hi, hspan⟩) .merge

theorem split_preserves_valid {n : Nat} {s : RawState Coord} (hs : Valid n lo hi s)
    {i : Nat} (hia : i ∈ s.active) (cut : Cut lo hi) : Valid n lo hi (split s i cut) := by
  apply advance_valid hs {i} (by simpa using hia)
  · intro j hj
    simp only [splitIntervals]
    split_ifs
    · exact ⟨le_rfl, le_of_lt cut.property.2⟩
    · exact ⟨le_of_lt cut.property.1, le_rfl⟩
  · intro x hx
    by_cases hcut : x < cut.val
    · refine ⟨0, ⟨by decide, ?_⟩, ?_⟩
      · simp [splitIntervals, Interval.Contains, hx.1, hcut]
      · intro j hj
        by_contra hn
        have h := hj.2
        simp only [splitIntervals, if_neg hn, Interval.Contains] at h
        exact (not_le_of_gt hcut) h.1
    · refine ⟨1, ⟨by decide, ?_⟩, ?_⟩
      · simp [splitIntervals, Interval.Contains, le_of_not_gt hcut, hx.2]
      · intro j hj
        have hnot : j ≠ 0 := by
          intro heq
          have h := hj.2
          simp only [heq, splitIntervals, if_pos rfl, Interval.Contains] at h
          exact hcut h.2
        omega

theorem merge_preserves_valid {n : Nat} {s : RawState Coord} (hs : Valid n lo hi s)
    {i j : Nat} (hia : i ∈ s.active) (hja : j ∈ s.active) (different : i ≠ j)
    (hspan : lo < hi) : Valid n lo hi (merge s i j hspan) := by
  apply advance_valid hs {i,j} (by simp [Finset.insert_subset_iff, hia, hja])
  · intro a ha; exact ⟨le_rfl, le_rfl⟩
  · intro x hx
    exact ⟨0, ⟨by decide, hx⟩, fun a ha => by omega⟩

theorem split_frontier_count {n : Nat} {s : RawState Coord} (hs : Valid n lo hi s)
    {i : Nat} (hia : i ∈ s.active) (cut : Cut lo hi) :
    (split s i cut).active.card = s.active.card + 1 := by
  have hc := advance_count hs {i} (by simpa using hia) 2 (splitIntervals cut) (.split cut.val)
  simp only [Finset.card_singleton] at hc
  change (advance s {i} 2 (splitIntervals cut) (.split cut.val)).active.card = _
  omega

theorem merge_frontier_count {n : Nat} {s : RawState Coord} (hs : Valid n lo hi s)
    {i j : Nat} (hia : i ∈ s.active) (hja : j ∈ s.active) (different : i ≠ j)
    (hspan : lo < hi) : (merge s i j hspan).active.card + 1 = s.active.card := by
  have hc := advance_count hs {i,j} (by simp [Finset.insert_subset_iff, hia, hja]) 1
    (fun _ => (⟨lo, hi, hspan⟩ : Interval Coord)) .merge
  have hcard : ({i,j} : Finset Nat).card = 2 := by simp [different]
  rw [hcard] at hc
  change (advance s {i,j} 1 (fun _ => ⟨lo, hi, hspan⟩) .merge).active.card + 1 = _
  omega

/-- Stable allocated IDs split into disjoint completed and frontier sets. -/
theorem allocated_iff_completed_or_active {n : Nat} {s : RawState Coord}
    (hs : Valid n lo hi s) (i : Nat) :
    i < s.nextLineage ↔ i ∈ s.completed ∨ i ∈ s.active := by
  simp only [RawState.completed, Finset.mem_sdiff, Finset.mem_range]
  constructor
  · intro hi
    by_cases ha : i ∈ s.active
    · exact Or.inr ha
    · exact Or.inl ⟨hi, ha⟩
  · rintro (h | h)
    · exact h.1
    · exact hs.active_bound i h

theorem completed_frontier_disjoint (s : RawState Coord) :
    Disjoint s.completed s.active := Finset.sdiff_disjoint

/-- Exact combined completed-plus-frontier uniqueness, at lineage identity
level. Equal endpoints do not merge two slots in this invariant. -/
theorem completed_frontier_exact_slot {n : Nat} {s : RawState Coord}
    (hs : Valid n lo hi s) {v : Nat} (hv : v < s.nextVertex) {x : Coord}
    (hx : lo ≤ x ∧ x < hi) :
    ∃! i, (i ∈ s.completed ∨ i ∈ s.active) ∧
      (s.slot i).child = v ∧ (s.slot i).interval.Contains x := by
  simpa only [SlotAt, ← allocated_iff_completed_or_active hs] using hs.coverage v hv x hx

/-- Each raw completed record retains its original lineage ID. -/
structure CompletedRecord (Coord : Type u) [LinearOrder Coord] where
  lineage : Nat
  parent : Nat
  child : Nat
  interval : Interval Coord

def rawRecord (s : RawState Coord) (i : Nat) : CompletedRecord Coord :=
  ⟨i, s.parent i, (s.slot i).child, (s.slot i).interval⟩

theorem rawRecord_identity_injective (s : RawState Coord) : Function.Injective (rawRecord s) := by
  intro i j h
  exact congrArg CompletedRecord.lineage h

/-- Actual graph adapter; finite node IDs are precisely the created vertices. -/
def completedRecord {n : Nat} {s : RawState Coord} (hs : Valid n lo hi s)
    (i : {i : Nat // i ∈ s.completed}) : EdgeRecord (Fin s.nextVertex) Coord :=
  singletonRecord
    ⟨s.parent i.val, (hs.parent_order i.val i.property).2⟩
    ⟨(s.slot i.val).child,
      (hs.slot_bound i.val (Finset.mem_range.mp (Finset.mem_sdiff.mp i.property).1)).1⟩
    (s.slot i.val).interval.lo (s.slot i.val).interval.hi (s.slot i.val).interval.proper

def projectedRecords {n : Nat} {s : RawState Coord} (hs : Valid n lo hi s) :
    Finset (EdgeRecord (Fin s.nextVertex) Coord) :=
  Finset.univ.image (completedRecord hs)

theorem projected_topology_iff {n : Nat} {s : RawState Coord} (hs : Valid n lo hi s)
    (p c : Fin s.nextVertex) :
    RecordTopology (projectedRecords hs) p c ↔
      ∃ i ∈ s.completed, s.parent i = p.val ∧ (s.slot i).child = c.val := by
  constructor
  · rintro ⟨e, he, hp, hc⟩
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he
    exact ⟨i.val, i.property, congrArg Fin.val hp, congrArg Fin.val hc⟩
  · rintro ⟨i, hi, hp, hc⟩
    exact ⟨completedRecord hs ⟨i,hi⟩,
      Finset.mem_image.mpr ⟨⟨i,hi⟩, Finset.mem_univ _, rfl⟩,
      Fin.ext hp, Fin.ext hc⟩

theorem projected_edge_strict {n : Nat} {s : RawState Coord} (hs : Valid n lo hi s)
    {p c : Fin s.nextVertex} (h : RecordTopology (projectedRecords hs) p c) : c.val < p.val := by
  obtain ⟨i, hi, hp, hc⟩ := (projected_topology_iff hs p c).mp h
  have ho := (hs.parent_order i hi).1
  simpa only [hp, hc] using ho

theorem projected_path_strict {n : Nat} {s : RawState Coord} (hs : Valid n lo hi s)
    {p c : Fin s.nextVertex} (h : Reach (RecordTopology (projectedRecords hs)) p c) :
    c.val < p.val := by
  induction h with
  | edge h => exact projected_edge_strict hs h
  | snoc _ h ih => exact Nat.lt_trans (projected_edge_strict hs h) ih

def recorded_prefix_toGARG {n : Nat} {s : RawState Coord} (hs : Valid n lo hi s) :
    WongGARG.GARG (Fin s.nextVertex) Coord where
  samples := Finset.univ.filter (fun v => v.val < n)
  records := projectedRecords hs
  acyclic := fun a h => (Nat.lt_irrefl a.val) (projected_path_strict hs h)

@[simp] theorem recorded_samples {n : Nat} {s : RawState Coord} (hs : Valid n lo hi s)
    (v : Fin s.nextVertex) : v ∈ (recorded_prefix_toGARG hs).samples ↔ v.val < n := by
  simp [recorded_prefix_toGARG]

theorem projected_atLocus_iff {n : Nat} {s : RawState Coord} (hs : Valid n lo hi s)
    (x : Coord) (p c : Fin s.nextVertex) :
    (recorded_prefix_toGARG hs).AtLocus x p c ↔
      ∃ i ∈ s.completed, s.parent i = p.val ∧ (s.slot i).child = c.val ∧
        (s.slot i).interval.Contains x := by
  constructor
  · rintro ⟨e, he, hp, hc, hx⟩
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he
    refine ⟨i.val, i.property, congrArg Fin.val hp, congrArg Fin.val hc, ?_⟩
    simpa only [completedRecord, singletonRecord_covers, Interval.Contains] using hx
  · rintro ⟨i, hi, hp, hc, hx⟩
    refine ⟨completedRecord hs ⟨i,hi⟩,
      Finset.mem_image.mpr ⟨⟨i,hi⟩, Finset.mem_univ _, rfl⟩, Fin.ext hp, Fin.ext hc, ?_⟩
    simpa only [completedRecord, singletonRecord_covers, Interval.Contains] using hx

theorem projected_nonempty_annotations {n : Nat} {s : RawState Coord}
    (hs : Valid n lo hi s) : (recorded_prefix_toGARG hs).NonemptyAnnotations := by
  intro e he
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he
  exact Finset.singleton_nonempty _

theorem projected_unique_parent_at {n : Nat} {s : RawState Coord}
    (hs : Valid n lo hi s) (x : Coord) : (recorded_prefix_toGARG hs).UniqueParentAt x := by
  intro c a b ha hb
  obtain ⟨i, hi, hp, hc, hix⟩ := (projected_atLocus_iff hs x a c).mp ha
  obtain ⟨j, hj, hq, hd, hjx⟩ := (projected_atLocus_iff hs x b c).mp hb
  have hil : i < s.nextLineage := Finset.mem_range.mp (Finset.mem_sdiff.mp hi).1
  have hjl : j < s.nextLineage := Finset.mem_range.mp (Finset.mem_sdiff.mp hj).1
  have hib := (hs.slot_bound i hil).2
  have hx := And.intro (le_trans hib.1 hix.1) (lt_of_lt_of_le hix.2 hib.2)
  obtain ⟨k, _, hk⟩ := hs.coverage c.val c.isLt x hx
  have hik := hk i ⟨hil, hc, hix⟩
  have hjk := hk j ⟨hjl, hd, hjx⟩
  have hij : i = j := hik.trans hjk.symm
  exact Fin.ext (hp.symm.trans ((congrArg s.parent hij).trans hq))

/-- Valid marks cannot consume an absent ID, repeat one ID in a merger, or
supply a noninterior cut. Distinct children are deliberately not required. -/
inductive Mark (lo hi : Coord) (s : RawState Coord) where
  | split (i : Nat) (active : i ∈ s.active) (cut : Cut lo hi)
  | merge (i j : Nat) (first : i ∈ s.active) (second : j ∈ s.active) (different : i ≠ j)

def applyMark (hspan : lo < hi) (s : RawState Coord) : Mark lo hi s → RawState Coord
  | .split i _ cut => split s i cut
  | .merge i j _ _ _ => merge s i j hspan

theorem applyMark_valid {n : Nat} {s : RawState Coord} (hs : Valid n lo hi s)
    (hspan : lo < hi) (mark : Mark lo hi s) : Valid n lo hi (applyMark hspan s mark) := by
  cases mark with
  | split i h cut => exact split_preserves_valid hs h cut
  | merge i j h h' different => exact merge_preserves_valid hs h h' different hspan

/-- Proof-indexed finite histories use the actual raw updates. Random marks
must separately be proved to inhabit these valid input types. -/
inductive Trace (n : Nat) (hspan : lo < hi) : RawState Coord → Type u where
  | nil : Trace n hspan (initial n hspan)
  | snoc {s : RawState Coord} (prior : Trace n hspan s) (mark : Mark lo hi s) :
      Trace n hspan (applyMark hspan s mark)

theorem finite_prefix_valid {n : Nat} {hspan : lo < hi} {s : RawState Coord}
    (history : Trace n hspan s) : Valid n lo hi s := by
  induction history with
  | nil => exact initial_valid n hspan
  | snoc prior mark ih => exact applyMark_valid ih hspan mark

theorem fresh_event_vertex {n : Nat} {s : RawState Coord} (hs : Valid n lo hi s)
    (hspan : lo < hi) (mark : Mark lo hi s) :
    (applyMark hspan s mark).nextVertex = s.nextVertex + 1 ∧
      (applyMark hspan s mark).events.length = s.events.length + 1 := by
  cases mark <;> simp [applyMark, split, merge, advance]

theorem allocated_ids_never_reused (s : RawState Coord) (m : Nat)
    {old new : Nat} (hold : old < s.nextLineage) (hnew : new ∈ freshIds s m) : old ≠ new := by
  have hn := (mem_freshIds s m new).mp hnew
  omega

theorem samples_persist {n : Nat} {s : RawState Coord} (hs : Valid n lo hi s)
    {v : Nat} (hv : v < n) : v < s.nextVertex := by
  have := hs.vertices
  omega

/-- Positive, strictly increasing dates for event vertices, with all samples
at zero. Dates use backward time, so parents have larger dates. -/
def vertexDate {Time : Type*} [Zero Time] (n : Nat) (times : Nat → Time) (v : Nat) : Time :=
  if v < n then 0 else times (v - n)

theorem dated_prefix_chronology {Time : Type*} [LinearOrder Time] [Zero Time]
    {n : Nat} {s : RawState Coord} (hs : Valid n lo hi s) (times : Nat → Time)
    (positive : ∀ j, 0 < times j) (ordered : StrictMono times)
    {i : Nat} (hi : i ∈ s.completed) :
    vertexDate n times (s.slot i).child < vertexDate n times (s.parent i) := by
  have hp := hs.parent_nonsample i hi
  have ho := (hs.parent_order i hi).1
  simp only [vertexDate, if_neg (Nat.not_lt.mpr hp)]
  by_cases hc : (s.slot i).child < n
  · simp only [if_pos hc]
    exact positive _
  · simp only [if_neg hc]
    apply ordered
    omega

section RawDecoder
variable {Node : Type*}

/-- Interior raw interval boundaries survive endpoint equality. They are
forgotten by unioning adjacent records or retaining only local parents. -/
def interiorEndpoints (records : Finset (EdgeRecord Node Coord)) (lo hi : Coord) : Finset Coord :=
  (records.biUnion (fun e => e.regions.biUnion (fun I => {I.lo,I.hi}))).filter
    (fun x => lo < x ∧ x < hi)

@[simp] theorem root_interiorEndpoints (hspan : lo < hi) (child : Node) :
    interiorEndpoints (specRecords hspan child (.root : ParentSpec Node Coord lo hi)) lo hi = ∅ := by
  simp [interiorEndpoints, specRecords]

@[simp] theorem single_interiorEndpoints (hspan : lo < hi) (child p : Node) :
    interiorEndpoints (specRecords hspan child (.singleParent p)) lo hi = ∅ := by
  ext x
  simp [interiorEndpoints, specRecords, singletonRecord, and_or_left, or_and_right, and_assoc]
  constructor
  · rintro rfl h
    exact False.elim ((lt_irrefl _) h)
  · rintro rfl _
    exact le_rfl

@[simp] theorem crossover_interiorEndpoints (hspan : lo < hi) (child a b : Node)
    (cut : Cut lo hi) :
    interiorEndpoints (specRecords hspan child
      (.crossover a b cut.val cut.property.1 cut.property.2)) lo hi = {cut.val} := by
  ext x
  simp [interiorEndpoints, specRecords, singletonRecord, or_and_right]
  constructor
  · rintro (⟨rfl, h, _⟩ | ⟨h, _, _⟩ | ⟨rfl, _, h⟩)
    · exact False.elim ((lt_irrefl _) h)
    · exact h
    · exact False.elim ((lt_irrefl _) h)
  · rintro rfl
    exact Or.inr (Or.inl ⟨rfl, cut.property.1, cut.property.2⟩)

/-- Unrestricted injectivity of *raw* interval records. Unlike local-parent
semantics, this retains the cut even when both parent vertices coincide. -/
theorem raw_records_injective (hspan : lo < hi) (child : Node) :
    Function.Injective (specRecords hspan child : ParentSpec Node Coord lo hi → _) := by
  intro s t heq
  have sameLocal := WongEventDecoding.same_local_of_records_eq hspan child s t heq
  have endpoints := congrArg (fun records => interiorEndpoints records lo hi) heq
  cases s with
  | root =>
      cases t with
      | root => rfl
      | singleParent p =>
          exact False.elim ((sameLocal lo p).mpr ⟨rfl, le_rfl, hspan⟩)
      | crossover a b q hl hh =>
          exact False.elim ((sameLocal lo a).mpr (Or.inl ⟨rfl, le_rfl, hl⟩))
  | singleParent p =>
      cases t with
      | root => exact False.elim ((sameLocal lo p).mp ⟨rfl, le_rfl, hspan⟩)
      | singleParent q =>
          have h := ((sameLocal lo p).mp ⟨rfl, le_rfl, hspan⟩).1
          subst q
          rfl
      | crossover a b q hl hh =>
          rw [single_interiorEndpoints,
            crossover_interiorEndpoints hspan child a b ⟨q,hl,hh⟩] at endpoints
          have hmem := Finset.mem_singleton_self q
          rw [← endpoints] at hmem
          exact False.elim (by simpa using hmem)
  | crossover a b q hl hh =>
      cases t with
      | root => exact False.elim ((sameLocal lo a).mp (Or.inl ⟨rfl, le_rfl, hl⟩))
      | singleParent p =>
          rw [crossover_interiorEndpoints hspan child a b ⟨q,hl,hh⟩,
            single_interiorEndpoints] at endpoints
          have hmem := Finset.mem_singleton_self q
          rw [endpoints] at hmem
          exact False.elim (by simpa using hmem)
      | crossover c d r hl' hh' =>
          have hac := WongEventDecoding.crossover_left_identified a b c d q r hl hh hl' hh' sameLocal
          have hbd := WongEventDecoding.crossover_right_identified a b c d q r hl hh hl' hh' sameLocal
          rw [crossover_interiorEndpoints hspan child a b ⟨q,hl,hh⟩,
            crossover_interiorEndpoints hspan child c d ⟨r,hl',hh'⟩] at endpoints
          have hqr : q = r := Finset.singleton_injective endpoints
          subst c; subst d; subst r
          rfl

abbrev RawEncodedRecords (hspan : lo < hi) (child : Node) :=
  {r : Finset (EdgeRecord Node Coord) // ∃ s : ParentSpec Node Coord lo hi, specRecords hspan child s = r}

def rawEncode (hspan : lo < hi) (child : Node) (s : ParentSpec Node Coord lo hi) :
    RawEncodedRecords hspan child := ⟨specRecords hspan child s, s, rfl⟩

def rawDecode (hspan : lo < hi) (child : Node) (r : RawEncodedRecords hspan child) :
    ParentSpec Node Coord lo hi := Classical.choose r.property

theorem raw_decode_encode (hspan : lo < hi) (child : Node) (s : ParentSpec Node Coord lo hi) :
    rawDecode hspan child (rawEncode hspan child s) = s := by
  apply raw_records_injective hspan child
  exact Classical.choose_spec (rawEncode hspan child s).property

theorem raw_encode_decode (hspan : lo < hi) (child : Node) (r : RawEncodedRecords hspan child) :
    rawEncode hspan child (rawDecode hspan child r) = r := by
  apply Subtype.ext
  exact Classical.choose_spec r.property

/-- Bijection to the explicit raw encoding range, with no distinct-parent
hypothesis. This is a classical inverse, not an executable file parser. -/
def rawEncodingEquiv (hspan : lo < hi) (child : Node) :
    ParentSpec Node Coord lo hi ≃ RawEncodedRecords hspan child where
  toFun := rawEncode hspan child
  invFun := rawDecode hspan child
  left_inv := raw_decode_encode hspan child
  right_inv := raw_encode_decode hspan child

end RawDecoder

/-- A count-one output is returned as is: no synthetic final event is added. -/
def stop {n : Nat} {s : RawState Coord} (hs : Valid n lo hi s)
    (_one : s.active.card = 1) : WongGARG.GARG (Fin s.nextVertex) Coord :=
  recorded_prefix_toGARG hs

theorem count_one_stop {n : Nat} {s : RawState Coord} (hs : Valid n lo hi s)
    (hone : s.active.card = 1) : stop hs hone = recorded_prefix_toGARG hs := rfl

theorem start_one_no_event (hspan : lo < hi) :
    (initial 1 hspan).active.card = 1 ∧ (initial 1 hspan).events = [] ∧
      (recorded_prefix_toGARG (initial_valid 1 hspan)).records = ∅ := by
  refine ⟨by simp [initial], rfl, ?_⟩
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨i, _, _⟩ := Finset.mem_image.mp he
  have h := i.property
  simp [initial, RawState.completed] at h

theorem step_reaching_one_is_merge {n : Nat} {s : RawState Coord} (hs : Valid n lo hi s)
    (hspan : lo < hi) (hbefore : 2 ≤ s.active.card) (mark : Mark lo hi s)
    (hone : (applyMark hspan s mark).active.card = 1) :
    ∃ i j hfirst hsecond hdifferent, mark = Mark.merge i j hfirst hsecond hdifferent := by
  cases mark with
  | split i h cut =>
      have hc := split_frontier_count hs h cut
      change (split s i cut).active.card = 1 at hone
      omega
  | merge i j hfirst hsecond hdifferent => exact ⟨i,j,hfirst,hsecond,hdifferent,rfl⟩

theorem merge_terminal_root {n : Nat} {s : RawState Coord} (hs : Valid n lo hi s)
    {i j : Nat} (hfirst : i ∈ s.active) (hsecond : j ∈ s.active) (different : i ≠ j)
    (hspan : lo < hi) (hone : (merge s i j hspan).active.card = 1) :
    (merge s i j hspan).active = {s.nextLineage} ∧
      ((merge s i j hspan).slot s.nextLineage).child = s.nextVertex ∧
      ((merge s i j hspan).slot s.nextLineage).interval.lo = lo ∧
      ((merge s i j hspan).slot s.nextLineage).interval.hi = hi := by
  have hmem : s.nextLineage ∈ (merge s i j hspan).active := by
    simpa only [Nat.add_zero, merge] using
      advance_active_new s {i,j} 1 (fun _ => (⟨lo,hi,hspan⟩ : Interval Coord)) .merge 0 (by decide)
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hone
  have heq : a = s.nextLineage := by
    rw [ha] at hmem
    exact (Finset.mem_singleton.mp hmem).symm
  subst a
  refine ⟨ha, ?_⟩
  simp [merge, advance]

section Reunion
variable (hspan : lo < hi) (cut : Cut lo hi)

/-- Source-admitted immediate reunion; the two selected lineages share child 2. -/
def reunion : RawState Coord := merge (split (initial 2 hspan) 0 cut) 2 3 hspan

def finishedReunion : RawState Coord := merge (reunion hspan cut) 1 4 hspan

theorem reunion_valid : Valid 2 lo hi (reunion hspan cut) := by
  apply merge_preserves_valid
    (split_preserves_valid (initial_valid 2 hspan) (by simp [initial]) cut)
  · simp [split, advance, initial, freshIds]
  · simp [split, advance, initial, freshIds]
  · decide

theorem finishedReunion_valid : Valid 2 lo hi (finishedReunion hspan cut) := by
  apply merge_preserves_valid (reunion_valid hspan cut)
  · simp [reunion, split, merge, advance, initial, freshIds]
  · simp [reunion, split, merge, advance, initial, freshIds]
  · decide

theorem reunion_counts :
    (initial 2 hspan).active.card = 2 ∧
    (split (initial 2 hspan) 0 cut).active.card = 3 ∧
    (reunion hspan cut).active.card = 2 ∧
    (finishedReunion hspan cut).active.card = 1 := by
  have h0 : (initial 2 hspan).active.card = 2 := by simp [initial]
  have hsplit := split_frontier_count (initial_valid 2 hspan) (i := 0) (by simp [initial]) cut
  have hmerge := merge_frontier_count
    (split_preserves_valid (initial_valid 2 hspan) (i := 0) (by simp [initial]) cut)
    (i := 2) (j := 3) (by simp [split, advance, initial, freshIds])
    (by simp [split, advance, initial, freshIds]) (by decide) hspan
  have hfinish := merge_frontier_count (reunion_valid hspan cut)
    (i := 1) (j := 4) (by simp [reunion, split, merge, advance, initial, freshIds])
    (by simp [reunion, split, merge, advance, initial, freshIds]) (by decide) hspan
  change (reunion hspan cut).active.card + 1 = _ at hmerge
  change (finishedReunion hspan cut).active.card + 1 = _ at hfinish
  omega

/-- Two completed raw records have distinct stable IDs but equal endpoints.
They retain the complementary intervals and the crossover cut. -/
theorem reunion_shared_endpoints :
    rawRecord (reunion hspan cut) 2 = ⟨2,3,2,⟨lo,cut.val,cut.property.1⟩⟩ ∧
    rawRecord (reunion hspan cut) 3 = ⟨3,3,2,⟨cut.val,hi,cut.property.2⟩⟩ := by
  simp [rawRecord, reunion, split, merge, advance, initial, splitIntervals]

theorem reunion_distinct_lineages : rawRecord (reunion hspan cut) 2 ≠ rawRecord (reunion hspan cut) 3 := by
  intro h
  have heq := rawRecord_identity_injective (reunion hspan cut) h
  omega

def reunionParentSpec : ParentSpec Nat Coord lo hi :=
  .crossover 3 3 cut.val cut.property.1 cut.property.2

theorem reunion_not_normalized : ¬ WongEventDecoding.Normalized (reunionParentSpec cut) := by
  simp [reunionParentSpec, WongEventDecoding.Normalized]

/-- The raw two edge records from the recorder are precisely the crossover
encoding that the earlier normalized decoder excluded. -/
theorem reunion_encoded_records :
    let s := reunion hspan cut
    {singletonRecord (s.parent 2) (s.slot 2).child
        (s.slot 2).interval.lo (s.slot 2).interval.hi (s.slot 2).interval.proper,
     singletonRecord (s.parent 3) (s.slot 3).child
        (s.slot 3).interval.lo (s.slot 3).interval.hi (s.slot 3).interval.proper} =
      specRecords hspan 2 (reunionParentSpec cut) := by
  simp [reunion, split, merge, advance, initial, splitIntervals, reunionParentSpec, specRecords]

theorem reunion_raw_decode :
    rawDecode hspan 2 (rawEncode hspan 2 (reunionParentSpec cut)) = reunionParentSpec cut :=
  raw_decode_encode hspan 2 (reunionParentSpec cut)

/-- Different actual recorder outputs retain different raw cut metadata. -/
theorem reunion_cut_retained (other : Cut lo hi) (different : cut.val ≠ other.val) :
    reunion hspan cut ≠ reunion hspan other := by
  intro h
  have heq := congrArg (fun s : RawState Coord => (s.slot 2).interval.hi) h
  simp [reunion, split, merge, advance, initial, splitIntervals] at heq
  exact different heq

/-- Once raw interval boundaries are forgotten, both reunion cuts have the
same local-parent semantics. This is a proved information-loss boundary. -/
theorem reunion_local_cut_forgotten (other : Cut lo hi) :
    WongEventDecoding.SameLocal (reunionParentSpec cut) (reunionParentSpec other) := by
  intro x p
  exact (WongEventDecoding.equal_parent_crossover_same_local 3 cut.val
    cut.property.1 cut.property.2 x p).trans
    (WongEventDecoding.equal_parent_crossover_same_local 3 other.val
      other.property.1 other.property.2 x p).symm

/-- Split a left frontier at a later genomic cut: the second split is retained
although its cut lies beyond the selected slot's entire inherited interval. -/
theorem split_outside_inherited_interval (later : Cut lo hi) (beyond : cut.val < later.val) :
    let s := split (initial 2 hspan) 0 cut
    (s.slot 2).interval.hi < later.val ∧
      (split s 2 later).active.card = s.active.card + 1 ∧
      ((split s 2 later).slot s.nextLineage).interval.lo = lo ∧
      ((split s 2 later).slot (s.nextLineage + 1)).interval.hi = hi := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · simpa [split, advance, initial, splitIntervals] using beyond
  · exact split_frontier_count
      (split_preserves_valid (initial_valid 2 hspan) (i := 0) (by simp [initial]) cut)
      (by simp [split, advance, initial, freshIds]) later
  · simp [split, advance, initial, splitIntervals]

end Reunion/-- Consumed and allocated lineage identities are recorded by the actual
update, independently of endpoint equality. -/
theorem advance_event_log (s : RawState Coord) (selected : Finset Nat) (m : Nat)
    (intervals : Nat → Interval Coord) (kind : EventKind Coord) :
    (advance s selected m intervals kind).events =
      s.events ++ [⟨s.nextVertex, kind, selected, freshIds s m⟩] := rfl

theorem old_completed_record_preserved {n : Nat} {s : RawState Coord} (hs : Valid n lo hi s)
    (selected : Finset Nat) (hselected : selected ⊆ s.active) (m : Nat)
    (intervals : Nat → Interval Coord) (kind : EventKind Coord)
    {i : Nat} (hi : i ∈ s.completed) :
    rawRecord (advance s selected m intervals kind) i = rawRecord s i := by
  have hold := Finset.mem_range.mp (Finset.mem_sdiff.mp hi).1
  have hnot : i ∉ selected := fun h => (Finset.mem_sdiff.mp hi).2 (hselected h)
  simp [rawRecord, advance, hold, hnot]

/-- Every history event creates exactly its fresh vertex, in order; there are
no skipped, duplicate, or fabricated event vertices. -/
theorem trace_event_vertices {n : Nat} {hspan : lo < hi} {s : RawState Coord}
    (history : Trace n hspan s) :
    s.events.map RawEvent.vertex = (List.range s.events.length).map (fun j => n + j) := by
  induction history with
  | nil => simp [initial]
  | @snoc s prior mark ih =>
      have hv := (finite_prefix_valid prior).vertices
      cases mark <;>
        simp only [applyMark, split, merge, advance, List.map_append,
          List.map_cons, List.map_nil, List.length_append, List.length_cons,
          List.length_nil, Nat.zero_add, List.range_succ]
      all_goals rw [ih, hv]
      all_goals simp

/-- The stopped clock only needs positive, increasing dates on the actual
finite event prior. No order after its terminal plateau is required. -/
theorem dated_prefix_chronology_bounded {Time : Type*} [LinearOrder Time] [Zero Time]
    {n : Nat} {s : RawState Coord} (hs : Valid n lo hi s) (times : Nat → Time)
    (positive : ∀ j, j < s.events.length → 0 < times j)
    (ordered : ∀ j k, j < k → k < s.events.length → times j < times k)
    {i : Nat} (hrecord : i ∈ s.completed) :
    vertexDate n times (s.slot i).child < vertexDate n times (s.parent i) := by
  have hp := hs.parent_nonsample i hrecord
  have ho := hs.parent_order i hrecord
  have hv := hs.vertices
  have hpbound : s.parent i - n < s.events.length := by omega
  simp only [vertexDate, if_neg (Nat.not_lt.mpr hp)]
  by_cases hc : (s.slot i).child < n
  · simp only [if_pos hc]
    exact positive _ hpbound
  · simp only [if_neg hc]
    exact ordered _ _ (by omega) hpbound

/-- Projection to finite edge records cannot collapse two completed lineage
slots: equality of their child and interval would contradict exact coverage.
Endpoint equality alone is allowed and supplies no such collapse. -/
theorem completedRecord_injective {n : Nat} {s : RawState Coord}
    (hs : Valid n lo hi s) : Function.Injective (completedRecord hs) := by
  intro i j heq
  have hil : i.val < s.nextLineage := Finset.mem_range.mp (Finset.mem_sdiff.mp i.property).1
  have hjl : j.val < s.nextLineage := Finset.mem_range.mp (Finset.mem_sdiff.mp j.property).1
  have hc := congrArg (fun e : EdgeRecord (Fin s.nextVertex) Coord => e.child.val) heq
  change (s.slot i.val).child = (s.slot j.val).child at hc
  have hr := congrArg EdgeRecord.regions heq
  change ({(s.slot i.val).interval} : Finset (Interval Coord)) = {(s.slot j.val).interval} at hr
  have hiq : (s.slot i.val).interval = (s.slot j.val).interval := Finset.singleton_injective hr
  have hib := hs.slot_bound i.val hil
  have hx : lo ≤ (s.slot i.val).interval.lo ∧ (s.slot i.val).interval.lo < hi :=
    ⟨hib.2.1, lt_of_lt_of_le (s.slot i.val).interval.proper hib.2.2⟩
  obtain ⟨k, _, hk⟩ := hs.coverage (s.slot i.val).child hib.1 (s.slot i.val).interval.lo hx
  apply Subtype.ext
  have hik := hk i.val ⟨hil, rfl, le_rfl, (s.slot i.val).interval.proper⟩
  have hjk := hk j.val ⟨hjl, hc.symm, by
    rw [← hiq]
    exact ⟨le_rfl, (s.slot i.val).interval.proper⟩⟩
  exact hik.trans hjk.symm

/-- A merger depends on an unordered pair of lineage IDs. -/
theorem merge_comm (s : RawState Coord) (i j : Nat) (hspan : lo < hi) :
    merge s i j hspan = merge s j i hspan := by
  unfold merge
  rw [Finset.pair_comm i j]

/-- Stable-ID record completion is exact for every selected lineage. -/
theorem selected_record_completed {n : Nat} {s : RawState Coord} (hs : Valid n lo hi s)
    (selected : Finset Nat) (hselected : selected ⊆ s.active) (m : Nat)
    (intervals : Nat → Interval Coord) (kind : EventKind Coord)
    {i : Nat} (hselectedi : i ∈ selected) :
    i ∈ (advance s selected m intervals kind).completed ∧
      rawRecord (advance s selected m intervals kind) i =
        ⟨i, s.nextVertex, (s.slot i).child, (s.slot i).interval⟩ := by
  have hold := hs.active_bound i (hselected hselectedi)
  constructor
  · simp only [RawState.completed, Finset.mem_sdiff, Finset.mem_range]
    refine ⟨by change i < s.nextLineage + m; omega, ?_⟩
    rw [advance_active_old s selected m intervals kind hold]
    exact fun h => h.2 hselectedi
  · simp [rawRecord, advance, hold, hselectedi]

end
end WongMarkedRecorder


