import WongGARG

/-!
# A finite, interval-valid gARG reconstruction boundary

The two graphs have exactly the same three genome identifiers and the same
sample. They have nonempty disjoint annotations, canonical records, and one
local parent. Sample-extracted local relations agree at every Nat coordinate,
while the raw graphs differ by a nonancestral edge. This pinpoints the
sample-support qualification in reconstruction; it is not a claim about
biological ownership, inferred real data, or a new scientific discovery.
-/

namespace WongExamples
open WongGARG AncestryViews

noncomputable section
local instance (α : Type*) : DecidableEq α := Classical.decEq α
local instance (P : Prop) : Decidable P := Classical.propDecidable P

abbrev Genome := Fin 3

def leftInterval : Interval Nat := ⟨0, 1, by omega⟩
def rightInterval : Interval Nat := ⟨1, 2, by omega⟩

def leftRecord : EdgeRecord Genome Nat where
  parent := 0
  child := 1
  regions := {leftInterval}
  disjoint := by
    intro I hI J hJ hne
    have hI' : I = leftInterval := Finset.mem_singleton.mp hI
    have hJ' : J = leftInterval := Finset.mem_singleton.mp hJ
    exact False.elim (hne (hI'.trans hJ'.symm))

def rightRecord : EdgeRecord Genome Nat where
  parent := 1
  child := 2
  regions := {rightInterval}
  disjoint := by
    intro I hI J hJ hne
    have hI' : I = rightInterval := Finset.mem_singleton.mp hI
    have hJ' : J = rightInterval := Finset.mem_singleton.mp hJ
    exact False.elim (hne (hI'.trans hJ'.symm))

def splitRecords : Finset (EdgeRecord Genome Nat) := {leftRecord, rightRecord}
def tailRecords : Finset (EdgeRecord Genome Nat) := {rightRecord}

theorem leftRecord_covers (x : Nat) : leftRecord.Covers x ↔ x = 0 := by
  simp only [EdgeRecord.Covers, leftRecord, Finset.mem_singleton]
  constructor
  · rintro ⟨I, rfl, h⟩
    change 0 ≤ x ∧ x < 1 at h
    omega
  · intro h
    subst x
    exact ⟨leftInterval, rfl, by change 0 ≤ 0 ∧ 0 < 1; omega⟩

theorem rightRecord_covers (x : Nat) : rightRecord.Covers x ↔ x = 1 := by
  simp only [EdgeRecord.Covers, rightRecord, Finset.mem_singleton]
  constructor
  · rintro ⟨I, rfl, h⟩
    change 1 ≤ x ∧ x < 2 at h
    omega
  · intro h
    subst x
    exact ⟨rightInterval, rfl, by change 1 ≤ 1 ∧ 1 < 2; omega⟩

theorem split_record_topology (a b : Genome) :
    RecordTopology splitRecords a b ↔ (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 2) := by
  constructor
  · rintro ⟨e, he, hp, hc⟩
    have : e = leftRecord ∨ e = rightRecord := by simpa [splitRecords] using he
    rcases this with rfl | rfl
    · exact Or.inl ⟨hp.symm, hc.symm⟩
    · exact Or.inr ⟨hp.symm, hc.symm⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨leftRecord, by simp [splitRecords], rfl, rfl⟩
    · exact ⟨rightRecord, by simp [splitRecords], rfl, rfl⟩

theorem tail_record_topology (a b : Genome) :
    RecordTopology tailRecords a b ↔ a = 1 ∧ b = 2 := by
  constructor
  · rintro ⟨e, he, hp, hc⟩
    have : e = rightRecord := by simpa [tailRecords] using he
    subst e
    exact ⟨hp.symm, hc.symm⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨rightRecord, by simp [tailRecords], rfl, rfl⟩

def splitGARG : GARG Genome Nat where
  samples := {2}
  records := splitRecords
  acyclic := by
    intro a path
    have h := reach_time_increases (fun v : Genome => v.val) (fun p c he => by
      rcases (split_record_topology p c).mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      all_goals omega) path
    exact (Nat.lt_irrefl _) h

def tailGARG : GARG Genome Nat where
  samples := {2}
  records := tailRecords
  acyclic := by
    intro a path
    have h := reach_time_increases (fun v : Genome => v.val) (fun p c he => by
      obtain ⟨rfl, rfl⟩ := (tail_record_topology p c).mp he
      omega) path
    exact (Nat.lt_irrefl _) h

theorem split_locus_iff (x : Nat) (a b : Genome) :
    splitGARG.AtLocus x a b ↔
      (x = 0 ∧ a = 0 ∧ b = 1) ∨ (x = 1 ∧ a = 1 ∧ b = 2) := by
  constructor
  · rintro ⟨e, he, hp, hc, hx⟩
    have : e = leftRecord ∨ e = rightRecord := by simpa [splitGARG, splitRecords] using he
    rcases this with rfl | rfl
    · exact Or.inl ⟨(leftRecord_covers x).mp hx, hp.symm, hc.symm⟩
    · exact Or.inr ⟨(rightRecord_covers x).mp hx, hp.symm, hc.symm⟩
  · rintro (⟨hx, rfl, rfl⟩ | ⟨hx, rfl, rfl⟩)
    · exact ⟨leftRecord, by simp [splitGARG, splitRecords], rfl, rfl,
        (leftRecord_covers x).mpr hx⟩
    · exact ⟨rightRecord, by simp [splitGARG, splitRecords], rfl, rfl,
        (rightRecord_covers x).mpr hx⟩

theorem tail_locus_iff (x : Nat) (a b : Genome) :
    tailGARG.AtLocus x a b ↔ x = 1 ∧ a = 1 ∧ b = 2 := by
  constructor
  · rintro ⟨e, he, hp, hc, hx⟩
    have : e = rightRecord := by simpa [tailGARG, tailRecords] using he
    subst e
    exact ⟨(rightRecord_covers x).mp hx, hp.symm, hc.symm⟩
  · rintro ⟨hx, rfl, rfl⟩
    exact ⟨rightRecord, by simp [tailGARG, tailRecords], rfl, rfl,
      (rightRecord_covers x).mpr hx⟩

theorem split_nonempty : splitGARG.NonemptyAnnotations := by
  intro e he
  have : e = leftRecord ∨ e = rightRecord := by simpa [splitGARG, splitRecords] using he
  rcases this with rfl | rfl
  · exact ⟨leftInterval, by simp [leftRecord]⟩
  · exact ⟨rightInterval, by simp [rightRecord]⟩

theorem tail_nonempty : tailGARG.NonemptyAnnotations := by
  intro e he
  have : e = rightRecord := by simpa [tailGARG, tailRecords] using he
  subst e
  exact ⟨rightInterval, by simp [rightRecord]⟩

theorem split_canonical : splitGARG.CanonicalRecords := by
  intro e he f hf hp hc
  have he' : e = leftRecord ∨ e = rightRecord := by simpa [splitGARG, splitRecords] using he
  have hf' : f = leftRecord ∨ f = rightRecord := by simpa [splitGARG, splitRecords] using hf
  rcases he' with rfl | rfl <;> rcases hf' with rfl | rfl
  · rfl
  · simp [leftRecord, rightRecord] at hp
  · simp [leftRecord, rightRecord] at hp
  · rfl

theorem tail_canonical : tailGARG.CanonicalRecords := by
  intro e he f hf _ _
  have he' : e = rightRecord := by simpa [tailGARG, tailRecords] using he
  have hf' : f = rightRecord := by simpa [tailGARG, tailRecords] using hf
  exact he'.trans hf'.symm

theorem split_unique_parent (x : Nat) : splitGARG.UniqueParentAt x := by
  intro c a b ha hb
  rcases (split_locus_iff x a c).mp ha with ⟨hx, ha, hc⟩ | ⟨hx, ha, hc⟩
  · rcases (split_locus_iff x b c).mp hb with ⟨_, hb, _⟩ | ⟨hx', _, _⟩
    · exact ha.trans hb.symm
    · omega
  · rcases (split_locus_iff x b c).mp hb with ⟨hx', _, _⟩ | ⟨_, hb, _⟩
    · omega
    · exact ha.trans hb.symm

theorem tail_unique_parent (x : Nat) : tailGARG.UniqueParentAt x := by
  intro c a b ha hb
  exact ((tail_locus_iff x a c).mp ha).2.1.trans
    ((tail_locus_iff x b c).mp hb).2.1.symm

private theorem split_zero_path_starts_zero {a b : Genome}
    (path : Reach (splitGARG.AtLocus 0) a b) : a = 0 := by
  induction path with
  | edge he =>
    rcases (split_locus_iff 0 _ _).mp he with ⟨_, ha, _⟩ | ⟨hbad, _, _⟩
    · exact ha
    · omega
  | snoc _ _ ih => exact ih

private theorem one_not_ancestral_at_zero : ¬ splitGARG.SampleAncestral 0 1 := by
  rintro ⟨s, hs, same | path⟩
  · have hs' : s = 2 := by simpa [splitGARG] using hs
    have bad := congrArg Fin.val (same.trans hs')
    change (1 : Nat) = 2 at bad
    omega
  · have bad := split_zero_path_starts_zero path
    have badVal := congrArg Fin.val bad
    change (1 : Nat) = 0 at badVal
    omega

theorem split_extracted_iff (x : Nat) (a b : Genome) :
    splitGARG.ExtractedAt x a b ↔ x = 1 ∧ a = 1 ∧ b = 2 := by
  constructor
  · rintro ⟨edge, anc⟩
    rcases (split_locus_iff x a b).mp edge with ⟨hx, _, hb⟩ | hright
    · subst x
      subst b
      exact False.elim (one_not_ancestral_at_zero anc)
    · exact hright
  · intro h
    refine ⟨(split_locus_iff x a b).mpr (Or.inr h), ?_⟩
    exact ⟨2, by simp [splitGARG], Or.inl h.2.2⟩

theorem tail_extracted_iff (x : Nat) (a b : Genome) :
    tailGARG.ExtractedAt x a b ↔ x = 1 ∧ a = 1 ∧ b = 2 := by
  constructor
  · intro h
    exact (tail_locus_iff x a b).mp h.1
  · intro h
    refine ⟨(tail_locus_iff x a b).mpr h, ?_⟩
    exact ⟨2, by simp [tailGARG], Or.inl h.2.2⟩

theorem all_extracted_relations_equal (x : Nat) (a b : Genome) :
    splitGARG.ExtractedAt x a b ↔ tailGARG.ExtractedAt x a b :=
  (split_extracted_iff x a b).trans (tail_extracted_iff x a b).symm

theorem raw_topologies_differ :
    splitGARG.Topology 0 1 ∧ ¬ tailGARG.Topology 0 1 := by
  constructor
  · exact (split_record_topology 0 1).mpr (Or.inl ⟨rfl, rfl⟩)
  · intro h
    have bad := ((tail_record_topology 0 1).mp h).1
    have badVal := congrArg Fin.val bad
    change (0 : Nat) = 1 at badVal
    omega

theorem raw_locus_relations_differ :
    splitGARG.AtLocus 0 0 1 ∧ ¬ tailGARG.AtLocus 0 0 1 := by
  constructor
  · exact (split_locus_iff 0 0 1).mpr (Or.inl ⟨rfl, rfl, rfl⟩)
  · intro h
    have bad := ((tail_locus_iff 0 0 1).mp h).1
    omega

theorem split_not_sampleSupported : ¬ splitGARG.SampleSupported := by
  intro h
  exact one_not_ancestral_at_zero (h 0 0 1 raw_locus_relations_differ.1)

theorem tail_sampleSupported : tailGARG.SampleSupported := by
  intro x a b h
  have hb := ((tail_locus_iff x a b).mp h).2.2
  exact ⟨2, by simp [tailGARG], Or.inl hb⟩

/-- A counterexample inside actual finite interval-annotated gARG structures,
with identical genome catalog and sample set and no empty/duplicate-edge trick. -/
theorem finite_garg_sample_reconstruction_boundary :
    splitGARG.samples = tailGARG.samples ∧
    splitGARG.NonemptyAnnotations ∧ tailGARG.NonemptyAnnotations ∧
    splitGARG.CanonicalRecords ∧ tailGARG.CanonicalRecords ∧
    (∀ x, splitGARG.UniqueParentAt x ∧ tailGARG.UniqueParentAt x) ∧
    (∀ x a b, splitGARG.ExtractedAt x a b ↔ tailGARG.ExtractedAt x a b) ∧
    splitGARG.Topology 0 1 ∧ ¬ tailGARG.Topology 0 1 ∧
    ¬ splitGARG.SampleSupported ∧ tailGARG.SampleSupported :=
  ⟨rfl, split_nonempty, tail_nonempty, split_canonical, tail_canonical,
    fun x => ⟨split_unique_parent x, tail_unique_parent x⟩,
    all_extracted_relations_equal, raw_topologies_differ.1, raw_topologies_differ.2,
    split_not_sampleSupported, tail_sampleSupported⟩

end
end WongExamples

#print axioms WongExamples.splitGARG
#print axioms WongExamples.tailGARG
#print axioms WongExamples.all_extracted_relations_equal
#print axioms WongExamples.raw_locus_relations_differ
#print axioms WongExamples.finite_garg_sample_reconstruction_boundary



