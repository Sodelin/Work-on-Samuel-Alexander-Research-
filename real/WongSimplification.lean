import WongBreakpointCells
import WongIntervalNormalization

/-!
# Automatically re-encoded finite ancestry transformations

Adjacent cells are derived from actual annotation
endpoints. This closes the explicit-cell precondition of the representation
lemma. The mathematics is noncomputable; no external software or runtime
complexity claim is made. Unretained node identifiers remain in the catalog.
-/

namespace WongSimplification
open WongGARG AncestryViews AncestryContraction WongIntervalNormalization
universe u v
noncomputable section
local instance (α : Type*) : DecidableEq α := Classical.decEq α
local instance (P : Prop) : Decidable P := Classical.propDecidable P

variable {Node : Type u} {Coord : Type v} [Fintype Node] [LinearOrder Coord]

/-- The cell decomposition is derived from this actual input gARG. -/
def automaticPresentation (G : GARG Node Coord) : CellPresentation G.AtLocus where
  cells := WongBreakpointCells.cells G.breakpoints
  disjoint := WongBreakpointCells.cells_pairwise_disjoint G.breakpoints
  constant := by
    intro I hI x hx a b
    exact WongBreakpointCells.locus_constant_on_cell G hI hx a b
  covered := by
    intro x a b he
    exact WongBreakpointCells.locus_covered G he

/-- Re-encode sample ancestry with no user-supplied cell decomposition. -/
theorem automatic_sample_restriction (G : GARG Node Coord) :
    ∃ H : GARG Node Coord, H.samples = G.samples ∧ H.NonemptyAnnotations ∧
      H.CanonicalRecords ∧ (∀ x a b, H.AtLocus x a b ↔ G.ExtractedAt x a b) :=
  sample_restriction_representable G (automaticPresentation G)

/-- In a single-parent graph, two hidden paths from retained starts into the
same target cannot begin at different retained ancestors. -/
theorem hidden_kept_sources_unique {R : Node → Node → Prop} {K : Node → Prop}
    (unique : ∀ c a b, R a c → R b c → a = b)
    {a b c : Node} (ha : K a) (hb : K b)
    (left : HiddenPath R K a c) (right : HiddenPath R K b c) : a = b := by
  induction left generalizing b with
  | edge he =>
    cases right with
    | edge hf => exact unique _ _ _ he hf
    | snoc _ hhidden hf =>
      have same := unique _ _ _ he hf
      exact False.elim (hhidden (same ▸ ha))
  | snoc _ hhidden he ih =>
    cases right with
    | edge hf =>
      have same := unique _ _ _ he hf
      exact False.elim (hhidden (same.symm ▸ hb))
    | snoc hiddenPrefix _ hf =>
      have same := unique _ _ _ he hf
      subst_vars
      exact ih hb hiddenPrefix

/-- Contraction preserves the unique-parent property, not just acyclicity. -/
theorem contraction_unique_parent {R : Node → Node → Prop}
    (unique : ∀ c a b, R a c → R b c → a = b) (K : Node → Prop) :
    ∀ c a b, Contract R K a c → Contract R K b c → a = b := by
  intro c a b ha hb
  exact hidden_kept_sources_unique unique ha.1 hb.1 ha.2.2 hb.2.2

/-- A hidden path in sample-extracted edges ends in original ancestral material. -/
theorem hidden_extracted_target_ancestral (G : GARG Node Coord) (K : Node → Prop)
    {x : Coord} {a b : Node} (h : HiddenPath (G.ExtractedAt x) K a b) :
    G.SampleAncestral x b := by
  cases h with
  | edge he => exact he.2
  | snoc _ _ he => exact he.2

/-- Grouping active cells into records introduces no new coordinate endpoint. -/
theorem reencoding_breakpoints_subset {R : Coord → Node → Node → Prop}
    (C : CellPresentation R) (samples : Finset Node) (acyclic : UnionAcyclic R)
    (B : Finset Coord)
    (endpoints : ∀ I ∈ C.cells, I.lo ∈ B ∧ I.hi ∈ B) :
    (C.toGARG samples acyclic).breakpoints ⊆ B := by
  intro z hz
  change z ∈ C.records.biUnion (fun e => e.regions.biUnion (fun I => {I.lo, I.hi})) at hz
  obtain ⟨e, he, hRecordRegions⟩ := Finset.mem_biUnion.mp hz
  obtain ⟨pair, _, rfl⟩ := Finset.mem_image.mp he
  obtain ⟨I, hI, hEndpoint⟩ := Finset.mem_biUnion.mp hRecordRegions
  have cell := ((C.mem_record_regions pair.1 pair.2 I).mp hI).1
  have bounds := endpoints I cell
  have hz' : z = I.lo ∨ z = I.hi := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hEndpoint
  rcases hz' with rfl | rfl
  · exact bounds.1
  · exact bounds.2
/-- Actual finite gARG output after sample restriction and fixed-node
contraction. All input cells are generated from the real annotation endpoints.
The exact sample-path guarantee concerns retained starting and sample nodes.
Unique local parents are inherited whenever the original local relation has
that property. Output sample support additionally follows if all samples stay. -/
theorem automatic_reencoded_simplification (G : GARG Node Coord) (K : Node → Prop) :
    ∃ H : GARG Node Coord,
      H.samples = G.samples ∧ H.NonemptyAnnotations ∧ H.CanonicalRecords ∧
      (∀ x a b, H.AtLocus x a b ↔ Contract (G.ExtractedAt x) K a b) ∧
      (∀ x a s, K a → K s → s ∈ G.samples →
        (Reach (H.AtLocus x) a s ↔ Reach (G.AtLocus x) a s)) ∧
      (∀ x, G.UniqueParentAt x → H.UniqueParentAt x) ∧
      ((∀ s ∈ G.samples, K s) → H.SampleSupported) ∧
      H.breakpoints ⊆ G.breakpoints := by
  let C := (extractedPresentation G (automaticPresentation G)).contract K
  let acyclic := contraction_union_acyclic (extracted_union_acyclic G) K
  let H := C.toGARG G.samples acyclic
  have hs : H.samples = G.samples := rfl
  have hn : H.NonemptyAnnotations := C.toGARG_nonempty G.samples acyclic
  have hc : H.CanonicalRecords := C.toGARG_canonical G.samples acyclic
  have he : ∀ x a b, H.AtLocus x a b ↔ Contract (G.ExtractedAt x) K a b :=
    C.toGARG_at_iff G.samples acyclic
  have hp : ∀ x a s, K a → K s → s ∈ G.samples →
      (Reach (H.AtLocus x) a s ↔ Reach (G.AtLocus x) a s) := by
    intro x a s ha hks hsample
    have eq : Reach (H.AtLocus x) a s ↔ Reach (Contract (G.ExtractedAt x) K) a s := by
      constructor
      · exact reach_mono (fun p c h => (he x p c).mp h)
      · exact reach_mono (fun p c h => (he x p c).mpr h)
    exact eq.trans (WongAlexander.extracted_contracted_sample_path_iff G x K ha hks hsample)
  refine ⟨H, hs, hn, hc, he, hp, ?_, ?_, ?_⟩
  · intro x unique c a b ha hb
    apply contraction_unique_parent (R := G.ExtractedAt x)
      (fun c p q hp hq => unique c p q hp.1 hq.1) K c a b
    · exact (he x a c).mp ha
    · exact (he x b c).mp hb
  · intro keepSamples x a b edge
    have contracted := (he x a b).mp edge
    have anc := hidden_extracted_target_ancestral G K contracted.2.2
    obtain ⟨s, sample, same | path⟩ := anc
    · refine ⟨s, ?_, Or.inl same⟩
      simpa only [hs] using sample
    · refine ⟨s, ?_, Or.inr ?_⟩
      · simpa only [hs] using sample
      · exact (hp x b s contracted.2.1 (keepSamples s sample) sample).mpr path

  · apply reencoding_breakpoints_subset C G.samples acyclic G.breakpoints
    intro I hI
    change I ∈ WongBreakpointCells.cells G.breakpoints at hI
    have bounds := (WongBreakpointCells.mem_cells_iff G.breakpoints I).mp hI
    exact ⟨bounds.1, bounds.2.1⟩

end
end WongSimplification

#print axioms WongSimplification.automaticPresentation
#print axioms WongSimplification.automatic_sample_restriction
#print axioms WongSimplification.contraction_unique_parent
#print axioms WongSimplification.automatic_reencoded_simplification

#print axioms WongSimplification.reencoding_breakpoints_subset


