import WongSimplification

/-!
Coordinate-dependent local simplification with an actual finite interval-gARG output.
The retained predicate may vary across source breakpoint cells. The useful instance
keeps samples and nodes having two distinct children in the sample-extracted local
relation. Original finite node identifiers are preserved; unused identifiers remain.
This is noncomputable model verification, not tskit implementation certification.
-/
namespace WongLocalSimplification
open WongGARG AncestryViews AncestryContraction WongIntervalNormalization
open WongSimplification
universe u v
noncomputable section
local instance (α : Type*) : DecidableEq α := Classical.decEq α
local instance (P : Prop) : Decidable P := Classical.propDecidable P

variable {Node : Type u} {Coord : Type v} [Fintype Node] [LinearOrder Coord]

/-- Both the original edges and the retained set can be transported exactly. -/
theorem contraction_congr_both {R Q : Node → Node → Prop}
    {K L : Node → Prop} (hR : ∀ a b, R a b ↔ Q a b)
    (hK : ∀ a, K a ↔ L a) (a b : Node) :
    Contract R K a b ↔ Contract Q L a b := by
  have same : K = L := funext (fun a => propext (hK a))
  subst L
  exact contraction_congr K hR a b

/-- Cell constancy is sufficient; no single global retained set is required. -/
def coordinatePresentation {R : Coord → Node → Node → Prop}
    (C : CellPresentation R) (K : Coord → Node → Prop)
    (hK : ∀ I ∈ C.cells, ∀ x, I.Contains x → ∀ a, K x a ↔ K I.lo a) :
    CellPresentation (fun x => Contract (R x) (K x)) where
  cells := C.cells
  disjoint := C.disjoint
  constant := by
    intro I hI x hx a b
    exact contraction_congr_both (C.constant I hI x hx) (hK I hI x hx) a b
  covered := by
    intro x a b h
    obtain ⟨p, c, he⟩ := hidden_path_has_edge h.2.2
    exact C.covered x p c he

/- Every new edge expands into a path in the original union graph. -/
omit [LinearOrder Coord] in
theorem coordinate_contraction_union_acyclic
    {R : Coord → Node → Node → Prop} (acyclic : UnionAcyclic R)
    (K : Coord → Node → Prop) :
    UnionAcyclic (fun x => Contract (R x) (K x)) := by
  intro a path
  apply acyclic a
  apply reach_substitute (R := EraseIndex (fun x => Contract (R x) (K x))) ?_ path
  intro p c edge
  obtain ⟨x, he⟩ := edge
  exact fixed_index_path_survives (hidden_path_original he.2.2)

/-- A retention rule is constant on each automatically generated source cell.
There is no condition outside these cells, where no contracted edge can exist. -/
def CellwiseRetained (G : GARG Node Coord) (K : Coord → Node → Prop) : Prop :=
  ∀ I ∈ WongBreakpointCells.cells G.breakpoints, ∀ x, I.Contains x →
    ∀ a, K x a ↔ K I.lo a

/-- Finite interval output, exact local semantics and sample paths, inherited
single-parent inheritance and sample support, with no added breakpoints.
The output has precisely the original finite Node type and sample identifiers. -/
theorem automatic_reencoded_local_simplification (G : GARG Node Coord)
    (K : Coord → Node → Prop) (hK : CellwiseRetained G K) :
    ∃ H : GARG Node Coord,
      H.samples = G.samples ∧ H.NonemptyAnnotations ∧ H.CanonicalRecords ∧
      (∀ x a b, H.AtLocus x a b ↔ Contract (G.ExtractedAt x) (K x) a b) ∧
      (∀ x a s, K x a → K x s → s ∈ G.samples →
        (Reach (H.AtLocus x) a s ↔ Reach (G.AtLocus x) a s)) ∧
      (∀ x, G.UniqueParentAt x → H.UniqueParentAt x) ∧
      ((∀ x s, s ∈ G.samples → K x s) → H.SampleSupported) ∧
      H.breakpoints ⊆ G.breakpoints := by
  let C0 := extractedPresentation G (automaticPresentation G)
  let C := coordinatePresentation C0 K hK
  let acyclic := coordinate_contraction_union_acyclic (extracted_union_acyclic G) K
  let H := C.toGARG G.samples acyclic
  have hs : H.samples = G.samples := rfl
  have hn : H.NonemptyAnnotations := C.toGARG_nonempty G.samples acyclic
  have hc : H.CanonicalRecords := C.toGARG_canonical G.samples acyclic
  have he : ∀ x a b, H.AtLocus x a b ↔ Contract (G.ExtractedAt x) (K x) a b :=
    C.toGARG_at_iff G.samples acyclic
  have hp : ∀ x a s, K x a → K x s → s ∈ G.samples →
      (Reach (H.AtLocus x) a s ↔ Reach (G.AtLocus x) a s) := by
    intro x a s ha hks hsample
    have eq : Reach (H.AtLocus x) a s ↔
        Reach (Contract (G.ExtractedAt x) (K x)) a s := by
      constructor
      · exact reach_mono (fun p c h => (he x p c).mp h)
      · exact reach_mono (fun p c h => (he x p c).mpr h)
    exact eq.trans
      (WongAlexander.extracted_contracted_sample_path_iff G x (K x) ha hks hsample)
  refine ⟨H, hs, hn, hc, he, hp, ?_, ?_, ?_⟩
  · intro x unique c a b ha hb
    apply contraction_unique_parent (R := G.ExtractedAt x)
      (fun c p q hp hq => unique c p q hp.1 hq.1) (K x) c a b
    · exact (he x a c).mp ha
    · exact (he x b c).mp hb
  · intro keepSamples x a b edge
    have contracted := (he x a b).mp edge
    have anc := hidden_extracted_target_ancestral G (K x) contracted.2.2
    obtain ⟨s, sample, same | path⟩ := anc
    · refine ⟨s, ?_, Or.inl same⟩
      simpa only [hs] using sample
    · refine ⟨s, ?_, Or.inr ?_⟩
      · simpa only [hs] using sample
      · exact (hp x b s contracted.2.1 (keepSamples x s sample) sample).mpr path
  · apply reencoding_breakpoints_subset C G.samples acyclic G.breakpoints
    intro I hI
    change I ∈ WongBreakpointCells.cells G.breakpoints at hI
    have bounds := (WongBreakpointCells.mem_cells_iff G.breakpoints I).mp hI
    exact ⟨bounds.1, bounds.2.1⟩

/-- Retain every sample and every branching point of the extracted local graph.
Branching means two distinct immediate child nodes, not two interval fragments
or two records. The predicate is evaluated BEFORE local contraction. -/
def KeepSamplesAndBranching (G : GARG Node Coord) (x : Coord) (a : Node) : Prop :=
  a ∈ G.samples ∨
    ∃ b c : Node, b ≠ c ∧ G.ExtractedAt x a b ∧ G.ExtractedAt x a c

theorem samples_kept (G : GARG Node Coord) (x : Coord) {s : Node}
    (hs : s ∈ G.samples) : KeepSamplesAndBranching G x s := Or.inl hs

/-- This biologically relevant constancy premise is derived from the source
relation's constancy, rather than required as an extra hypothesis. -/
theorem samples_and_branching_cellwise (G : GARG Node Coord) :
    CellwiseRetained G (KeepSamplesAndBranching G) := by
  intro I hI x hx a
  have hrel := (extractedPresentation G (automaticPresentation G)).constant I hI x hx
  constructor
  · rintro (sample | ⟨b, c, hne, hb, hc⟩)
    · exact Or.inl sample
    · exact Or.inr ⟨b, c, hne, (hrel a b).mp hb, (hrel a c).mp hc⟩
  · rintro (sample | ⟨b, c, hne, hb, hc⟩)
    · exact Or.inl sample
    · exact Or.inr ⟨b, c, hne, (hrel a b).mpr hb, (hrel a c).mpr hc⟩

/-- A suppressed node has at most one child in the extracted graph at that locus. -/
theorem suppressed_at_most_one_child (G : GARG Node Coord) (x : Coord)
    {a : Node} (ha : ¬ KeepSamplesAndBranching G x a)
    {b c : Node} (hb : G.ExtractedAt x a b) (hc : G.ExtractedAt x a c) : b = c := by
  by_contra hne
  exact ha (Or.inr ⟨b, c, hne, hb, hc⟩)

/-- An unretained node has no incident edges in the contracted local relation.
This is locuswise isolation, not deletion from the finite Node catalog. -/
theorem unretained_locally_isolated (G : GARG Node Coord)
    (K : Coord → Node → Prop) (x : Coord) {a : Node} (ha : ¬ K x a) :
    ∀ b, ¬ Contract (G.ExtractedAt x) (K x) a b ∧
      ¬ Contract (G.ExtractedAt x) (K x) b a := by
  intro b
  exact ⟨fun h => ha h.1, fun h => ha h.2.1⟩

/-- Source-relevant finite output with samples plus local branching retained.
No caller-supplied retention constancy or sample-retention hypothesis remains. -/
theorem samples_and_branching_representable (G : GARG Node Coord) :
    ∃ H : GARG Node Coord,
      H.samples = G.samples ∧ H.NonemptyAnnotations ∧ H.CanonicalRecords ∧
      (∀ x a b, H.AtLocus x a b ↔
        Contract (G.ExtractedAt x) (KeepSamplesAndBranching G x) a b) ∧
      (∀ x a s, KeepSamplesAndBranching G x a → s ∈ G.samples →
        (Reach (H.AtLocus x) a s ↔ Reach (G.AtLocus x) a s)) ∧
      (∀ x, G.UniqueParentAt x → H.UniqueParentAt x) ∧
      H.SampleSupported ∧ H.breakpoints ⊆ G.breakpoints ∧
      (∀ x a, ¬ KeepSamplesAndBranching G x a →
        ∀ b, ¬ H.AtLocus x a b ∧ ¬ H.AtLocus x b a) := by
  obtain ⟨H, hs, hn, hc, he, hp, hu, hsupport, hbreak⟩ :=
    automatic_reencoded_local_simplification G (KeepSamplesAndBranching G)
      (samples_and_branching_cellwise G)
  refine ⟨H, hs, hn, hc, he, ?_, hu, ?_, hbreak, ?_⟩
  · intro x a s ha hs
    exact hp x a s ha (samples_kept G x hs) hs
  · exact hsupport (fun x s hs => samples_kept G x hs)
  · intro x a ha b
    have isolated := unretained_locally_isolated G (KeepSamplesAndBranching G) x ha b
    exact ⟨fun h => isolated.1 ((he x a b).mp h),
      fun h => isolated.2 ((he x b a).mp h)⟩

end
end WongLocalSimplification
