import WongGARG

/-!
# Ordered event-parent specifications encoded as genome intervals

Wong et al. (2024), journal pp. 2–4: a single ancestral parent receives the
whole genome interval, while an ordered crossover sends the left and right
intervals to its designated parents. This module constructs an actual finite
gARG and checks local traversal and topology preservation.

This is the event-edge conversion, not a stochastic coalescent process.
SingleParent may describe a sampling, pass-through, or common-ancestor
node. Binary child-arity conventions and event metadata are not reconstructed.
No unary suppression, sample resolution, or storage round-trip is asserted.
-/

namespace WongEventEncoding

open AncestryViews WongGARG

universe u v
noncomputable section

local instance (α : Type*) : DecidableEq α := Classical.decEq α
local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- Parent orientation is explicit: the first crossover parent supplies [lo,cut). -/
inductive ParentSpec (Node : Type u) (Coord : Type v) [LinearOrder Coord]
    (lo hi : Coord) where
  | root
  | singleParent (parent : Node)
  | crossover (leftParent rightParent : Node) (cut : Coord)
      (leftInterior : lo < cut) (rightInterior : cut < hi)

namespace ParentSpec
variable {Node : Type u} {Coord : Type v} [LinearOrder Coord]
variable {lo hi : Coord}

/-- Event topology in the ancestor-to-descendant orientation used by the package. -/
def Parent (spec : ParentSpec Node Coord lo hi) (p : Node) : Prop :=
  match spec with
  | .root => False
  | .singleParent a => p = a
  | .crossover a b _ _ _ => p = a ∨ p = b

/-- Local traversal semantics, independently of the interval-record construction. -/
def At (spec : ParentSpec Node Coord lo hi) (x : Coord) (p : Node) : Prop :=
  match spec with
  | .root => False
  | .singleParent a => p = a ∧ lo ≤ x ∧ x < hi
  | .crossover a b cut _ _ =>
      (p = a ∧ lo ≤ x ∧ x < cut) ∨ (p = b ∧ cut ≤ x ∧ x < hi)

/-- Follow one event backwards at a position already known to be in [lo,hi). -/
def routeInside (spec : ParentSpec Node Coord lo hi) (x : Coord) : Option Node :=
  match spec with
  | .root => none
  | .singleParent a => some a
  | .crossover a b cut _ _ => if x < cut then some a else some b

theorem at_iff_routeInside (spec : ParentSpec Node Coord lo hi) (x : Coord)
    (hx : lo ≤ x ∧ x < hi) (p : Node) :
    spec.At x p ↔ spec.routeInside x = some p := by
  cases spec with
  | root => simp [At, routeInside]
  | singleParent a => simp [At, routeInside, hx.1, hx.2, eq_comm]
  | crossover a b cut hl hr =>
      by_cases hc : x < cut
      · simp [At, routeInside, hc, hx.1, hx.2, not_le_of_gt hc, eq_comm]
      · simp [At, routeInside, hc, hx.1, hx.2, le_of_not_gt hc, eq_comm]

theorem at_in_span (spec : ParentSpec Node Coord lo hi) {x : Coord} {p : Node}
    (h : spec.At x p) : lo ≤ x ∧ x < hi := by
  cases spec with
  | root => exact False.elim h
  | singleParent a => exact h.2
  | crossover a b cut hl hr =>
      rcases h with h | h
      · exact ⟨h.2.1, lt_trans h.2.2 hr⟩
      · exact ⟨le_trans (le_of_lt hl) h.2.1, h.2.2⟩

theorem unique_at (spec : ParentSpec Node Coord lo hi) {x : Coord} {a b : Node}
    (ha : spec.At x a) (hb : spec.At x b) : a = b := by
  have hx := spec.at_in_span ha
  have h1 := (spec.at_iff_routeInside x hx a).mp ha
  have h2 := (spec.at_iff_routeInside x hx b).mp hb
  exact Option.some.inj (h1.symm.trans h2)

theorem at_parent (spec : ParentSpec Node Coord lo hi) {x : Coord} {p : Node}
    (h : spec.At x p) : spec.Parent p := by
  cases spec with
  | root => exact False.elim h
  | singleParent a => exact h.1
  | crossover a b cut hl hr => exact h.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)

/-- Strictly interior crossover points make both branches visible at some locus. -/
theorem parent_iff_exists_at (hspan : lo < hi) (spec : ParentSpec Node Coord lo hi)
    (p : Node) : spec.Parent p ↔ ∃ x, spec.At x p := by
  constructor
  · intro h
    cases spec with
    | root => exact False.elim h
    | singleParent a => exact ⟨lo, h, le_rfl, hspan⟩
    | crossover a b cut hl hr =>
        rcases h with h | h
        · exact ⟨lo, Or.inl ⟨h, le_rfl, hl⟩⟩
        · exact ⟨cut, Or.inr ⟨h, le_rfl, hr⟩⟩
  · rintro ⟨x, hx⟩
    exact spec.at_parent hx

/-- With fixed ordered distinct parent identities, the full local relation
determines an interior crossover point. This is not event-metadata decoding. -/
theorem crossover_cut_identified (a b : Node) (different : a ≠ b)
    (cut1 cut2 : Coord) (hlo1 : lo < cut1) (hhi1 : cut1 < hi)
    (hlo2 : lo < cut2) (hhi2 : cut2 < hi)
    (same : ∀ x, lo ≤ x ∧ x < hi → ∀ p,
      (ParentSpec.crossover a b cut1 hlo1 hhi1).At x p ↔
      (ParentSpec.crossover a b cut2 hlo2 hhi2).At x p) :
    cut1 = cut2 := by
  rcases lt_trichotomy cut1 cut2 with hlt | heq | hgt
  · exfalso
    have first : (ParentSpec.crossover a b cut1 hlo1 hhi1).At cut1 b :=
      Or.inr ⟨rfl, le_rfl, hhi1⟩
    have second := (same cut1 ⟨le_of_lt hlo1, hhi1⟩ b).mp first
    rcases second with left | right
    · exact different left.1.symm
    · exact (not_le_of_gt hlt) right.2.1
  · exact heq
  · exfalso
    have second : (ParentSpec.crossover a b cut2 hlo2 hhi2).At cut2 b :=
      Or.inr ⟨rfl, le_rfl, hhi2⟩
    have first := (same cut2 ⟨le_of_lt hlo2, hhi2⟩ b).mpr second
    rcases first with left | right
    · exact different left.1.symm
    · exact (not_le_of_gt hgt) right.2.1

end ParentSpec

/-- One proper interval per record; interval disjointness is immediate. -/
def singletonRecord {Node : Type u} {Coord : Type v} [LinearOrder Coord]
    (parent child : Node) (lo hi : Coord) (h : lo < hi) : EdgeRecord Node Coord where
  parent := parent
  child := child
  regions := {⟨lo, hi, h⟩}
  disjoint := by
    intro I hI J hJ hne
    have hIe : I = ⟨lo, hi, h⟩ := Finset.mem_singleton.mp hI
    have hJe : J = ⟨lo, hi, h⟩ := Finset.mem_singleton.mp hJ
    exact False.elim (hne (hIe.trans hJe.symm))

theorem singletonRecord_covers {Node : Type u} {Coord : Type v} [LinearOrder Coord]
    (p c : Node) (lo hi : Coord) (h : lo < hi) (x : Coord) :
    (singletonRecord p c lo hi h).Covers x ↔ lo ≤ x ∧ x < hi := by
  simp [singletonRecord, EdgeRecord.Covers, Interval.Contains]

/-- Encode the ordered event-parent description into full or split intervals. -/
def specRecords {Node : Type u} {Coord : Type v} [LinearOrder Coord]
    {lo hi : Coord} (hspan : lo < hi) (child : Node)
    (spec : ParentSpec Node Coord lo hi) : Finset (EdgeRecord Node Coord) :=
  match spec with
  | .root => ∅
  | .singleParent parent => {singletonRecord parent child lo hi hspan}
  | .crossover a b cut hl hr =>
      {singletonRecord a child lo cut hl, singletonRecord b child cut hi hr}

theorem specRecords_topology {Node : Type u} {Coord : Type v} [LinearOrder Coord]
    {lo hi : Coord} (hspan : lo < hi) (child : Node)
    (spec : ParentSpec Node Coord lo hi) (p c : Node) :
    RecordTopology (specRecords hspan child spec) p c ↔
      c = child ∧ spec.Parent p := by
  cases spec with
  | root => simp [specRecords, RecordTopology, ParentSpec.Parent]
  | singleParent a =>
      simp [specRecords, RecordTopology, singletonRecord, ParentSpec.Parent,
        eq_comm, and_comm]
  | crossover a b cut hl hr =>
      constructor
      · rintro ⟨e, he, hp, hc⟩
        simp only [specRecords, Finset.mem_insert, Finset.mem_singleton] at he
        rcases he with rfl | rfl
        · exact ⟨hc.symm, Or.inl hp.symm⟩
        · exact ⟨hc.symm, Or.inr hp.symm⟩
      · rintro ⟨rfl, hp | hp⟩
        · exact ⟨singletonRecord a c lo cut hl, by simp [specRecords], hp.symm, rfl⟩
        · exact ⟨singletonRecord b c cut hi hr, by simp [specRecords], hp.symm, rfl⟩

theorem specRecords_at {Node : Type u} {Coord : Type v} [LinearOrder Coord]
    {lo hi : Coord} (hspan : lo < hi) (child : Node)
    (spec : ParentSpec Node Coord lo hi) (x : Coord) (p c : Node) :
    (∃ e ∈ specRecords hspan child spec,
      e.parent = p ∧ e.child = c ∧ e.Covers x) ↔ c = child ∧ spec.At x p := by
  cases spec <;>
    simp [specRecords, singletonRecord, EdgeRecord.Covers, Interval.Contains,
      ParentSpec.At, or_and_right, and_or_left, exists_or, eq_comm,
      and_comm, and_left_comm, and_assoc]

theorem specRecords_nonempty_annotations {Node : Type u} {Coord : Type v}
    [LinearOrder Coord] {lo hi : Coord} (hspan : lo < hi) (child : Node)
    (spec : ParentSpec Node Coord lo hi) {e : EdgeRecord Node Coord}
    (he : e ∈ specRecords hspan child spec) : e.regions.Nonempty := by
  cases spec with
  | root => simp [specRecords] at he
  | singleParent a =>
      simp only [specRecords, Finset.mem_singleton] at he
      subst e
      exact Finset.singleton_nonempty _
  | crossover a b cut hl hr =>
      simp only [specRecords, Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl <;> exact Finset.singleton_nonempty _

/-- A finite acyclic event-parent graph on a common genomic coordinate span.
It does not impose binary coalescent child arities or a stochastic law. -/
structure EventGraph (Node : Type u) (Coord : Type v) [Fintype Node] [LinearOrder Coord]
    (lo hi : Coord) where
  span : lo < hi
  parents : Node → ParentSpec Node Coord lo hi
  acyclic : ∀ a, ¬ Reach (fun p c => (parents c).Parent p) a a

namespace EventGraph
variable {Node : Type u} {Coord : Type v} [Fintype Node] [LinearOrder Coord]
variable {lo hi : Coord} (G : EventGraph Node Coord lo hi)

def Topology (p c : Node) : Prop := (G.parents c).Parent p

def AtLocus (x : Coord) (p c : Node) : Prop := (G.parents c).At x p

def records : Finset (EdgeRecord Node Coord) :=
  Finset.univ.biUnion (fun c => specRecords G.span c (G.parents c))

theorem records_topology (p c : Node) :
    RecordTopology G.records p c ↔ G.Topology p c := by
  constructor
  · rintro ⟨e, he, hp, hc⟩
    obtain ⟨child, _, hmem⟩ := Finset.mem_biUnion.mp he
    obtain ⟨hchild, hparent⟩ :=
      (specRecords_topology G.span child (G.parents child) p c).mp ⟨e, hmem, hp, hc⟩
    subst child
    exact hparent
  · intro h
    obtain ⟨e, he, hp, hc⟩ :=
      (specRecords_topology G.span c (G.parents c) p c).mpr ⟨rfl, h⟩
    exact ⟨e, Finset.mem_biUnion.mpr ⟨c, Finset.mem_univ _, he⟩, hp, hc⟩

/-- Actual finite gARG construction, preserving arbitrary chosen sample nodes. -/
def toGARG (samples : Finset Node) : WongGARG.GARG Node Coord where
  samples := samples
  records := G.records
  acyclic := by
    intro a h
    exact G.acyclic a (reach_mono (fun p c he => (G.records_topology p c).mp he) h)

theorem encoded_topology (samples : Finset Node) (p c : Node) :
    (G.toGARG samples).Topology p c ↔ G.Topology p c :=
  G.records_topology p c

theorem encoded_atLocus (samples : Finset Node) (x : Coord) (p c : Node) :
    (G.toGARG samples).AtLocus x p c ↔ G.AtLocus x p c := by
  constructor
  · rintro ⟨e, he, hp, hc, hx⟩
    obtain ⟨child, _, hmem⟩ := Finset.mem_biUnion.mp he
    obtain ⟨hchild, hparent⟩ :=
      (specRecords_at G.span child (G.parents child) x p c).mp ⟨e, hmem, hp, hc, hx⟩
    subst child
    exact hparent
  · intro h
    obtain ⟨e, he, hp, hc, hx⟩ :=
      (specRecords_at G.span c (G.parents c) x p c).mpr ⟨rfl, h⟩
    exact ⟨e, Finset.mem_biUnion.mpr ⟨c, Finset.mem_univ _, he⟩, hp, hc, hx⟩

theorem encoded_nonempty_annotations (samples : Finset Node) :
    (G.toGARG samples).NonemptyAnnotations := by
  intro e he
  obtain ⟨c, _, hmem⟩ := Finset.mem_biUnion.mp he
  exact specRecords_nonempty_annotations G.span c (G.parents c) hmem

theorem encoded_unique_parent (samples : Finset Node) (x : Coord) :
    (G.toGARG samples).UniqueParentAt x := by
  intro c a b ha hb
  exact (G.parents c).unique_at
    ((G.encoded_atLocus samples x a c).mp ha)
    ((G.encoded_atLocus samples x b c).mp hb)

/-- Exact one-step traversal at an in-domain locus, with the parent-side convention. -/
theorem encoded_route (samples : Finset Node) (x : Coord) (hx : lo ≤ x ∧ x < hi)
    (p c : Node) :
    (G.toGARG samples).AtLocus x p c ↔ (G.parents c).routeInside x = some p :=
  (G.encoded_atLocus samples x p c).trans ((G.parents c).at_iff_routeInside x hx p)

/-- The parent-to-child relation induced by rootward pointers and the gARG
have exactly the same finite paths at this fixed coordinate. -/
theorem encoded_path_iff (samples : Finset Node) (x : Coord) (hx : lo ≤ x ∧ x < hi)
    (a b : Node) :
    Reach ((G.toGARG samples).AtLocus x) a b ↔
      Reach (fun p c => (G.parents c).routeInside x = some p) a b := by
  constructor
  · exact reach_mono (fun p c he => (G.encoded_route samples x hx p c).mp he)
  · exact reach_mono (fun p c he => (G.encoded_route samples x hx p c).mpr he)

/-- No event-topology branch disappears on erasing interval labels. -/
theorem erased_encoded_topology (samples : Finset Node) (a b : Node) :
    EraseIndex (G.toGARG samples).AtLocus a b ↔ G.Topology a b :=
  ((G.toGARG samples).topology_iff_erased (G.encoded_nonempty_annotations samples) a b).symm.trans
    (G.encoded_topology samples a b)

/-- The general parent-pointer representation agrees with ordered event routing. -/
theorem encoded_parent_pointer (samples : Finset Node) (x : Coord)
    (hx : lo ≤ x ∧ x < hi) (c : Node) (p : Node) :
    (G.toGARG samples).localParent x c = some p ↔
      (G.parents c).routeInside x = some p :=
  ((G.toGARG samples).localParent_eq_some_iff x (G.encoded_unique_parent samples x) c p).trans
    (G.encoded_route samples x hx p c)

end EventGraph
end
end WongEventEncoding

#print axioms WongEventEncoding.ParentSpec.parent_iff_exists_at
#print axioms WongEventEncoding.EventGraph.encoded_topology
#print axioms WongEventEncoding.EventGraph.encoded_atLocus
#print axioms WongEventEncoding.EventGraph.encoded_nonempty_annotations
#print axioms WongEventEncoding.EventGraph.encoded_unique_parent
#print axioms WongEventEncoding.EventGraph.encoded_route
#print axioms WongEventEncoding.EventGraph.encoded_path_iff
#print axioms WongEventEncoding.EventGraph.erased_encoded_topology
#print axioms WongEventEncoding.EventGraph.encoded_parent_pointer
#print axioms WongEventEncoding.ParentSpec.crossover_cut_identified

