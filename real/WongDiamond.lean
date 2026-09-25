import WongEventEncoding
import SamuelAlexanderResearch.AncestryContraction

/-!
# A valid finite diamond loses its crossover cutoff under contraction

A formal instance for Wong et al. (2024), Appendix G/H, journal pp. 16–17.
The two raw gARGs have the same four nodes, one sample, and diamond topology.
Both are sample-supported and locally single-parent. Their interval labels
differ, but contracting to nodes 0 and 3 yields the same labelled relation.

This is a mathematical instance of relation-level node elimination, not a
correctness theorem for the tskit simplify implementation.
-/

namespace WongDiamond
open WongGARG WongEventEncoding AncestryViews AncestryContraction

noncomputable section
local instance (α : Type*) : DecidableEq α := Classical.decEq α
local instance (P : Prop) : Decidable P := Classical.propDecidable P

abbrev Genome := Fin 4

def r01 (cut : Nat) (hl : 0 < cut) : EdgeRecord Genome Nat :=
  singletonRecord 0 1 0 cut hl

def r13 (cut : Nat) (hl : 0 < cut) : EdgeRecord Genome Nat :=
  singletonRecord 1 3 0 cut hl

def r02 (cut : Nat) (hh : cut < 3) : EdgeRecord Genome Nat :=
  singletonRecord 0 2 cut 3 hh

def r23 (cut : Nat) (hh : cut < 3) : EdgeRecord Genome Nat :=
  singletonRecord 2 3 cut 3 hh

def records (cut : Nat) (hl : 0 < cut) (hh : cut < 3) :
    Finset (EdgeRecord Genome Nat) := {r01 cut hl, r13 cut hl, r02 cut hh, r23 cut hh}

theorem mem_records (cut : Nat) (hl : 0 < cut) (hh : cut < 3)
    (e : EdgeRecord Genome Nat) :
    e ∈ records cut hl hh ↔
      e = r01 cut hl ∨ e = r13 cut hl ∨ e = r02 cut hh ∨ e = r23 cut hh := by
  simp [records]

def DiamondTopology (a b : Genome) : Prop :=
  (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 3) ∨ (a = 0 ∧ b = 2) ∨ (a = 2 ∧ b = 3)

theorem topology_iff (cut : Nat) (hl : 0 < cut) (hh : cut < 3) (a b : Genome) :
    RecordTopology (records cut hl hh) a b ↔ DiamondTopology a b := by
  constructor
  · rintro ⟨e, he, hp, hc⟩
    rcases (mem_records cut hl hh e).mp he with rfl | rfl | rfl | rfl
    · exact Or.inl ⟨hp.symm, hc.symm⟩
    · exact Or.inr (Or.inl ⟨hp.symm, hc.symm⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hp.symm, hc.symm⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hp.symm, hc.symm⟩))
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨r01 cut hl, by simp [records], rfl, rfl⟩
    · exact ⟨r13 cut hl, by simp [records], rfl, rfl⟩
    · exact ⟨r02 cut hh, by simp [records], rfl, rfl⟩
    · exact ⟨r23 cut hh, by simp [records], rfl, rfl⟩

theorem diamond_strict {a b : Genome} (h : DiamondTopology a b) : a.val < b.val := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals decide

def garg (cut : Nat) (hl : 0 < cut) (hh : cut < 3) : GARG Genome Nat where
  samples := {3}
  records := records cut hl hh
  acyclic := by
    intro a path
    have h := reach_time_increases (fun v : Genome => v.val)
      (fun p c he => diamond_strict ((topology_iff cut hl hh p c).mp he)) path
    exact (Nat.lt_irrefl _) h

theorem locus_iff (cut : Nat) (hl : 0 < cut) (hh : cut < 3)
    (x : Nat) (a b : Genome) :
    (garg cut hl hh).AtLocus x a b ↔
      (x < cut ∧ a = 0 ∧ b = 1) ∨
      (x < cut ∧ a = 1 ∧ b = 3) ∨
      (cut ≤ x ∧ x < 3 ∧ a = 0 ∧ b = 2) ∨
      (cut ≤ x ∧ x < 3 ∧ a = 2 ∧ b = 3) := by
  constructor
  · rintro ⟨e, he, hp, hc, hx⟩
    rcases (mem_records cut hl hh e).mp he with rfl | rfl | rfl | rfl
    · have h := (singletonRecord_covers (0 : Genome) 1 0 cut hl x).mp hx
      exact Or.inl ⟨h.2, hp.symm, hc.symm⟩
    · have h := (singletonRecord_covers (1 : Genome) 3 0 cut hl x).mp hx
      exact Or.inr (Or.inl ⟨h.2, hp.symm, hc.symm⟩)
    · have h := (singletonRecord_covers (0 : Genome) 2 cut 3 hh x).mp hx
      exact Or.inr (Or.inr (Or.inl ⟨h.1, h.2, hp.symm, hc.symm⟩))
    · have h := (singletonRecord_covers (2 : Genome) 3 cut 3 hh x).mp hx
      exact Or.inr (Or.inr (Or.inr ⟨h.1, h.2, hp.symm, hc.symm⟩))
  · rintro (⟨hx, rfl, rfl⟩ | ⟨hx, rfl, rfl⟩ |
      ⟨hx, hx3, rfl, rfl⟩ | ⟨hx, hx3, rfl, rfl⟩)
    · exact ⟨r01 cut hl, by simp [garg, records], rfl, rfl,
        (singletonRecord_covers (0 : Genome) 1 0 cut hl x).mpr ⟨Nat.zero_le _, hx⟩⟩
    · exact ⟨r13 cut hl, by simp [garg, records], rfl, rfl,
        (singletonRecord_covers (1 : Genome) 3 0 cut hl x).mpr ⟨Nat.zero_le _, hx⟩⟩
    · exact ⟨r02 cut hh, by simp [garg, records], rfl, rfl,
        (singletonRecord_covers (0 : Genome) 2 cut 3 hh x).mpr ⟨hx, hx3⟩⟩
    · exact ⟨r23 cut hh, by simp [garg, records], rfl, rfl,
        (singletonRecord_covers (2 : Genome) 3 cut 3 hh x).mpr ⟨hx, hx3⟩⟩

theorem nonempty_annotations (cut : Nat) (hl : 0 < cut) (hh : cut < 3) :
    (garg cut hl hh).NonemptyAnnotations := by
  intro e he
  rcases (mem_records cut hl hh e).mp he with rfl | rfl | rfl | rfl
  all_goals exact Finset.singleton_nonempty _

theorem canonical_records (cut : Nat) (hl : 0 < cut) (hh : cut < 3) :
    (garg cut hl hh).CanonicalRecords := by
  intro e he f hf hp hc
  rcases (mem_records cut hl hh e).mp he with rfl | rfl | rfl | rfl
  all_goals rcases (mem_records cut hl hh f).mp hf with rfl | rfl | rfl | rfl
  all_goals first | rfl | simp [r01, r13, r02, r23, singletonRecord] at hp hc

theorem unique_parent (cut : Nat) (hl : 0 < cut) (hh : cut < 3) (x : Nat) :
    (garg cut hl hh).UniqueParentAt x := by
  intro c a b ha hb
  rcases (locus_iff cut hl hh x a c).mp ha with
    ⟨hx, ha, hc⟩ | ⟨hx, ha, hc⟩ | ⟨hx, hx3, ha, hc⟩ | ⟨hx, hx3, ha, hc⟩
  all_goals
    rcases (locus_iff cut hl hh x b c).mp hb with
      ⟨hy, hb, hc'⟩ | ⟨hy, hb, hc'⟩ | ⟨hy, hy3, hb, hc'⟩ | ⟨hy, hy3, hb, hc'⟩
  all_goals
    subst a
    subst b
    simp_all
  all_goals omega

theorem sample_supported (cut : Nat) (hl : 0 < cut) (hh : cut < 3) :
    (garg cut hl hh).SampleSupported := by
  intro x a b h
  rcases (locus_iff cut hl hh x a b).mp h with
    ⟨hx, _, hb⟩ | ⟨hx, _, hb⟩ | ⟨hx, hx3, _, hb⟩ | ⟨hx, hx3, _, hb⟩
  · refine ⟨3, by simp [garg], Or.inr ?_⟩
    subst b
    exact .edge ((locus_iff cut hl hh x 1 3).mpr (Or.inr (Or.inl ⟨hx, rfl, rfl⟩)))
  · exact ⟨3, by simp [garg], Or.inl hb⟩
  · refine ⟨3, by simp [garg], Or.inr ?_⟩
    subst b
    exact .edge ((locus_iff cut hl hh x 2 3).mpr
      (Or.inr (Or.inr (Or.inr ⟨hx, hx3, rfl, rfl⟩))))
  · exact ⟨3, by simp [garg], Or.inl hb⟩

def Keep (a : Genome) : Prop := a = 0 ∨ a = 3

theorem locus_in_span (cut : Nat) (hl : 0 < cut) (hh : cut < 3)
    {x : Nat} {a b : Genome} (h : (garg cut hl hh).AtLocus x a b) : x < 3 := by
  rcases (locus_iff cut hl hh x a b).mp h with
    ⟨hx, _, _⟩ | ⟨hx, _, _⟩ | ⟨_, hx, _, _⟩ | ⟨_, hx, _, _⟩
  all_goals omega

theorem path_in_span (cut : Nat) (hl : 0 < cut) (hh : cut < 3)
    {x : Nat} {a b : Genome} (h : Reach ((garg cut hl hh).AtLocus x) a b) : x < 3 := by
  cases h with
  | edge he => exact locus_in_span cut hl hh he
  | snoc _ he => exact locus_in_span cut hl hh he

theorem locus_strict (cut : Nat) (hl : 0 < cut) (hh : cut < 3)
    {x : Nat} {a b : Genome} (h : (garg cut hl hh).AtLocus x a b) : a.val < b.val :=
  diamond_strict ((topology_iff cut hl hh a b).mp ((garg cut hl hh).locus_edge_topology h))

/-- Eliminating the two internal diamond nodes erases which branch carries x. -/
theorem contracted_relation_iff (cut : Nat) (hl : 0 < cut) (hh : cut < 3)
    (x : Nat) (a b : Genome) :
    Contract ((garg cut hl hh).AtLocus x) Keep a b ↔ x < 3 ∧ a = 0 ∧ b = 3 := by
  constructor
  · rintro ⟨ha, hb, hidden⟩
    have path := hidden_path_original hidden
    have hx := path_in_span cut hl hh path
    have strict := reach_time_increases (fun v : Genome => v.val)
      (fun p c he => locus_strict cut hl hh he) path
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    all_goals first | exact ⟨hx, rfl, rfl⟩ | omega
  · rintro ⟨hx, rfl, rfl⟩
    refine ⟨Or.inl rfl, Or.inr rfl, ?_⟩
    by_cases hleft : x < cut
    · apply HiddenPath.snoc
        (HiddenPath.edge ((locus_iff cut hl hh x 0 1).mpr (Or.inl ⟨hleft, rfl, rfl⟩)))
        (by simp [Keep])
      exact (locus_iff cut hl hh x 1 3).mpr (Or.inr (Or.inl ⟨hleft, rfl, rfl⟩))
    · have hright : cut ≤ x := by omega
      apply HiddenPath.snoc
        (HiddenPath.edge ((locus_iff cut hl hh x 0 2).mpr
          (Or.inr (Or.inr (Or.inl ⟨hright, hx, rfl, rfl⟩)))))
        (by simp [Keep])
      exact (locus_iff cut hl hh x 2 3).mpr
        (Or.inr (Or.inr (Or.inr ⟨hright, hx, rfl, rfl⟩)))

/-- The retained-node simplification preserves exactly the old ancestry on those nodes. -/
theorem retained_ancestry_iff (cut : Nat) (hl : 0 < cut) (hh : cut < 3)
    (x : Nat) {a b : Genome} (ha : Keep a) (hb : Keep b) :
    Reach (Contract ((garg cut hl hh).AtLocus x) Keep) a b ↔
      Reach ((garg cut hl hh).AtLocus x) a b :=
  AncestryContraction.retained_path_iff ha hb

theorem sample_ancestry_iff (cut : Nat) (hl : 0 < cut) (hh : cut < 3)
    (x : Nat) {a : Genome} (ha : Keep a) :
    Reach (Contract ((garg cut hl hh).AtLocus x) Keep) a 3 ↔
      Reach ((garg cut hl hh).AtLocus x) a 3 :=
  retained_ancestry_iff cut hl hh x ha (Or.inr rfl)

def cutOne : GARG Genome Nat := garg 1 (by omega) (by omega)
def cutTwo : GARG Genome Nat := garg 2 (by omega) (by omega)

theorem contracted_relations_agree (x : Nat) (a b : Genome) :
    Contract (cutOne.AtLocus x) Keep a b ↔ Contract (cutTwo.AtLocus x) Keep a b :=
  (contracted_relation_iff 1 (by omega) (by omega) x a b).trans
    (contracted_relation_iff 2 (by omega) (by omega) x a b).symm

/-- At nucleotide 1, the second raw graph uses the left branch and the first does not. -/
theorem raw_relations_differ :
    cutTwo.AtLocus 1 1 3 ∧ ¬ cutOne.AtLocus 1 1 3 := by
  constructor
  · exact (locus_iff 2 (by omega) (by omega) 1 1 3).mpr
      (Or.inr (Or.inl ⟨by omega, rfl, rfl⟩))
  · intro h
    have h' := (locus_iff 1 (by omega) (by omega) 1 1 3).mp h
    simpa using h'

/-- A collision within fully sample-supported, admissible finite interval gARGs:
diamond contraction preserves retained ancestry but hides the crossover cutoff. -/
theorem diamond_cutoff_information_loss :
    cutOne.samples = cutTwo.samples ∧
    cutOne.NonemptyAnnotations ∧ cutTwo.NonemptyAnnotations ∧
    cutOne.CanonicalRecords ∧ cutTwo.CanonicalRecords ∧
    (∀ x, cutOne.UniqueParentAt x ∧ cutTwo.UniqueParentAt x) ∧
    cutOne.SampleSupported ∧ cutTwo.SampleSupported ∧
    (∀ x a b, Contract (cutOne.AtLocus x) Keep a b ↔
      Contract (cutTwo.AtLocus x) Keep a b) ∧
    cutTwo.AtLocus 1 1 3 ∧ ¬ cutOne.AtLocus 1 1 3 :=
  ⟨rfl, nonempty_annotations 1 (by omega) (by omega),
    nonempty_annotations 2 (by omega) (by omega),
    canonical_records 1 (by omega) (by omega),
    canonical_records 2 (by omega) (by omega),
    fun x => ⟨unique_parent 1 (by omega) (by omega) x,
      unique_parent 2 (by omega) (by omega) x⟩,
    sample_supported 1 (by omega) (by omega),
    sample_supported 2 (by omega) (by omega),
    contracted_relations_agree, raw_relations_differ.1, raw_relations_differ.2⟩

/-- A common concrete output with one full-span interval, retaining the same node catalogue. -/
def collapsedRecord : EdgeRecord Genome Nat :=
  singletonRecord 0 3 0 3 (by omega)

theorem collapsed_topology_iff (a b : Genome) :
    RecordTopology {collapsedRecord} a b ↔ a = 0 ∧ b = 3 := by
  constructor
  · rintro ⟨e, he, hp, hc⟩
    have he' : e = collapsedRecord := Finset.mem_singleton.mp he
    subst e
    exact ⟨hp.symm, hc.symm⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨collapsedRecord, Finset.mem_singleton_self _, rfl, rfl⟩

def collapsedGARG : GARG Genome Nat where
  samples := {3}
  records := {collapsedRecord}
  acyclic := by
    intro a path
    have h := reach_time_increases (fun v : Genome => v.val)
      (fun p c he => show p.val < c.val from by
        rcases (collapsed_topology_iff p c).mp he with ⟨rfl, rfl⟩
        decide) path
    exact (Nat.lt_irrefl _) h

theorem collapsed_locus_iff (x : Nat) (a b : Genome) :
    collapsedGARG.AtLocus x a b ↔ x < 3 ∧ a = 0 ∧ b = 3 := by
  constructor
  · rintro ⟨e, he, hp, hc, hx⟩
    have he' : e = collapsedRecord := Finset.mem_singleton.mp he
    subst e
    have h := (singletonRecord_covers (0 : Genome) 3 0 3 (by omega) x).mp hx
    exact ⟨h.2, hp.symm, hc.symm⟩
  · rintro ⟨hx, rfl, rfl⟩
    exact ⟨collapsedRecord, Finset.mem_singleton_self _, rfl, rfl,
      (singletonRecord_covers (0 : Genome) 3 0 3 (by omega) x).mpr ⟨Nat.zero_le _, hx⟩⟩

/-- Every proper interior cutoff has this same actual finite interval representation
of its contracted local relations. This does not identify automatic cell segmentations. -/
theorem collapsed_represents_contraction (cut : Nat) (hl : 0 < cut) (hh : cut < 3)
    (x : Nat) (a b : Genome) :
    collapsedGARG.AtLocus x a b ↔ Contract ((garg cut hl hh).AtLocus x) Keep a b :=
  (collapsed_locus_iff x a b).trans (contracted_relation_iff cut hl hh x a b).symm

/-- One explicitly chosen valid finite output represents both different raw inputs.
The unused internal node identifiers remain in the finite catalogue as isolated nodes. -/
theorem same_finite_output_hides_cutoff :
    collapsedGARG.samples = cutOne.samples ∧
    collapsedGARG.samples = cutTwo.samples ∧
    collapsedGARG.records = {collapsedRecord} ∧
    collapsedGARG.NonemptyAnnotations ∧ collapsedGARG.CanonicalRecords ∧
    (∀ x, collapsedGARG.UniqueParentAt x) ∧ collapsedGARG.SampleSupported ∧
    (∀ x a b, (collapsedGARG.AtLocus x a b ↔ Contract (cutOne.AtLocus x) Keep a b) ∧
      (collapsedGARG.AtLocus x a b ↔ Contract (cutTwo.AtLocus x) Keep a b)) ∧
    cutTwo.AtLocus 1 1 3 ∧ ¬ cutOne.AtLocus 1 1 3 := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, raw_relations_differ.1,
    raw_relations_differ.2⟩
  · intro e he
    have he' : e = collapsedRecord := Finset.mem_singleton.mp he
    subst e
    exact Finset.singleton_nonempty _
  · intro e he f hf _ _
    have he' : e = collapsedRecord := Finset.mem_singleton.mp he
    have hf' : f = collapsedRecord := Finset.mem_singleton.mp hf
    exact he'.trans hf'.symm
  · intro x c a b ha hb
    exact ((collapsed_locus_iff x a c).mp ha).2.1.trans
      ((collapsed_locus_iff x b c).mp hb).2.1.symm
  · intro x a b h
    exact ⟨3, by simp [collapsedGARG], Or.inl ((collapsed_locus_iff x a b).mp h).2.2⟩
  · intro x a b
    exact ⟨collapsed_represents_contraction 1 (by omega) (by omega) x a b,
      collapsed_represents_contraction 2 (by omega) (by omega) x a b⟩

end
end WongDiamond

#print axioms WongDiamond.garg
#print axioms WongDiamond.nonempty_annotations
#print axioms WongDiamond.canonical_records
#print axioms WongDiamond.unique_parent
#print axioms WongDiamond.sample_supported
#print axioms WongDiamond.contracted_relation_iff
#print axioms WongDiamond.retained_ancestry_iff
#print axioms WongDiamond.sample_ancestry_iff
#print axioms WongDiamond.contracted_relations_agree
#print axioms WongDiamond.raw_relations_differ
#print axioms WongDiamond.diamond_cutoff_information_loss


#print axioms WongDiamond.collapsed_represents_contraction
#print axioms WongDiamond.same_finite_output_hides_cutoff
