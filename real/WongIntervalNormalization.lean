import WongAlexander
import Mathlib.Data.Fintype.Prod

/-!
# Finite-cell re-encoding of ancestry transformations

A supplied finite disjoint family of proper half-open
cells is required; no automatic breakpoint extraction or software algorithm is
claimed. Global acyclicity concerns the union across coordinates, not merely
each local graph. Records are grouped canonically by their endpoint pair.
-/

namespace WongIntervalNormalization
open WongGARG AncestryViews AncestralRestriction AncestryContraction
universe u v
noncomputable section
local instance (α : Type*) : DecidableEq α := Classical.decEq α
local instance (P : Prop) : Decidable P := Classical.propDecidable P

variable {Node : Type u} {Coord : Type v} [Fintype Node] [LinearOrder Coord]

/-- An explicit finite cell decomposition on which an indexed relation is
constant, covering every coordinate at which an edge is present. The family
need not cover unused coordinate gaps. Its intervals are already ordered
geometric objects; storage order is irrelevant. -/
structure CellPresentation (R : Coord → Node → Node → Prop) where
  cells : Finset (Interval Coord)
  disjoint : ∀ I ∈ cells, ∀ J ∈ cells, I ≠ J → I.Disjoint J
  constant : ∀ I ∈ cells, ∀ x, I.Contains x → ∀ a b, R x a b ↔ R I.lo a b
  covered : ∀ x a b, R x a b → ∃ I ∈ cells, I.Contains x

/-- Local DAGs alone do not imply this condition: different coordinates can
orient an edge in opposite directions. -/
def UnionAcyclic (R : Coord → Node → Node → Prop) : Prop :=
  ∀ a, ¬ Reach (EraseIndex R) a a

namespace CellPresentation
variable {R : Coord → Node → Node → Prop} (C : CellPresentation R)

/-- One record groups every active cell for a fixed ordered endpoint pair. -/
def record (a b : Node) : EdgeRecord Node Coord where
  parent := a
  child := b
  regions := C.cells.filter (fun I => R I.lo a b)
  disjoint := by
    intro I hI J hJ hne
    exact C.disjoint I (Finset.mem_filter.mp hI).1 J (Finset.mem_filter.mp hJ).1 hne

def activePairs : Finset (Node × Node) :=
  Finset.univ.filter (fun pair => (C.record pair.1 pair.2).regions.Nonempty)

def records : Finset (EdgeRecord Node Coord) :=
  C.activePairs.image (fun pair => C.record pair.1 pair.2)

theorem mem_record_regions (a b : Node) (I : Interval Coord) :
    I ∈ (C.record a b).regions ↔ I ∈ C.cells ∧ R I.lo a b := by
  simp only [record, Finset.mem_filter]

theorem records_nonempty {e : EdgeRecord Node Coord} (he : e ∈ C.records) :
    e.regions.Nonempty := by
  obtain ⟨pair, hp, rfl⟩ := Finset.mem_image.mp he
  exact (Finset.mem_filter.mp hp).2

/-- The finite record construction represents exactly the given relation. -/
theorem records_at_iff (x : Coord) (a b : Node) :
    (∃ e ∈ C.records, e.parent = a ∧ e.child = b ∧ e.Covers x) ↔ R x a b := by
  constructor
  · rintro ⟨e, he, ha, hb, I, hI, hx⟩
    obtain ⟨⟨p, c⟩, _, rfl⟩ := Finset.mem_image.mp he
    change p = a at ha
    change c = b at hb
    subst p
    subst c
    obtain ⟨hcell, hR⟩ := (C.mem_record_regions a b I).mp hI
    exact (C.constant I hcell x hx a b).mpr hR
  · intro hR
    obtain ⟨I, hI, hx⟩ := C.covered x a b hR
    have hRI : R I.lo a b := (C.constant I hI x hx a b).mp hR
    have hmem : I ∈ (C.record a b).regions := (C.mem_record_regions a b I).mpr ⟨hI, hRI⟩
    refine ⟨C.record a b, ?_, rfl, rfl, I, hmem, hx⟩
    apply Finset.mem_image.mpr
    refine ⟨(a, b), ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, I, hmem⟩

theorem records_topology_iff (a b : Node) :
    RecordTopology C.records a b ↔ EraseIndex R a b := by
  constructor
  · rintro ⟨e, he, ha, hb⟩
    obtain ⟨I, hI⟩ := C.records_nonempty he
    refine ⟨I.lo, (C.records_at_iff I.lo a b).mp ?_⟩
    exact ⟨e, he, ha, hb, I, hI, le_rfl, I.proper⟩
  · rintro ⟨x, hx⟩
    obtain ⟨e, he, ha, hb, _⟩ := (C.records_at_iff x a b).mpr hx
    exact ⟨e, he, ha, hb⟩

/-- Acyclicity is discharged against the union of coordinate relations. -/
def toGARG (samples : Finset Node) (acyclic : UnionAcyclic R) : GARG Node Coord where
  samples := samples
  records := C.records
  acyclic := by
    intro a h
    exact acyclic a (reach_mono (fun p c he => (C.records_topology_iff p c).mp he) h)

theorem toGARG_at_iff (samples : Finset Node) (acyclic : UnionAcyclic R)
    (x : Coord) (a b : Node) :
    (C.toGARG samples acyclic).AtLocus x a b ↔ R x a b := C.records_at_iff x a b

theorem toGARG_topology_iff (samples : Finset Node) (acyclic : UnionAcyclic R)
    (a b : Node) :
    (C.toGARG samples acyclic).Topology a b ↔ EraseIndex R a b := C.records_topology_iff a b

theorem toGARG_nonempty (samples : Finset Node) (acyclic : UnionAcyclic R) :
    (C.toGARG samples acyclic).NonemptyAnnotations := by
  intro e he
  exact C.records_nonempty he

theorem toGARG_canonical (samples : Finset Node) (acyclic : UnionAcyclic R) :
    (C.toGARG samples acyclic).CanonicalRecords := by
  intro e he f hf hp hc
  obtain ⟨⟨a, b⟩, _, rfl⟩ := Finset.mem_image.mp he
  obtain ⟨⟨c, d⟩, _, rfl⟩ := Finset.mem_image.mp hf
  change a = c at hp
  change b = d at hc
  subst c
  subst d
  rfl

theorem finite_cell_representation (C : CellPresentation R) (samples : Finset Node) (acyclic : UnionAcyclic R) :
    ∃ H : GARG Node Coord, H.samples = samples ∧ H.NonemptyAnnotations ∧
      H.CanonicalRecords ∧ (∀ x a b, H.AtLocus x a b ↔ R x a b) ∧
      (∀ a b, H.Topology a b ↔ EraseIndex R a b) :=
  ⟨C.toGARG samples acyclic, rfl, C.toGARG_nonempty samples acyclic,
    C.toGARG_canonical samples acyclic, C.toGARG_at_iff samples acyclic,
    C.toGARG_topology_iff samples acyclic⟩

end CellPresentation

/-- Relational substitution preserves paths without asserting edge equality. -/
theorem reach_substitute {R Q : Node → Node → Prop}
    (sound : ∀ a b, R a b → Reach Q a b) {a b : Node} (path : Reach R a b) :
    Reach Q a b := by
  induction path with
  | edge he => exact sound _ _ he
  | snoc _ he ih => exact AncestralRestriction.reach_trans ih (sound _ _ he)

theorem hidden_path_mono {R Q : Node → Node → Prop} {K : Node → Prop}
    (hRQ : ∀ a b, R a b → Q a b) {a b : Node} (path : HiddenPath R K a b) :
    HiddenPath Q K a b := by
  induction path with
  | edge he => exact .edge (hRQ _ _ he)
  | snoc _ hn he ih => exact .snoc ih hn (hRQ _ _ he)

theorem hidden_path_has_edge {R : Node → Node → Prop} {K : Node → Prop}
    {a b : Node} (path : HiddenPath R K a b) : ∃ p c, R p c := by
  cases path with
  | edge he => exact ⟨_, _, he⟩
  | snoc _ _ he => exact ⟨_, _, he⟩

theorem restriction_congr {R Q : Node → Node → Prop} (S : Node → Prop)
    (heq : ∀ a b, R a b ↔ Q a b) (a b : Node) :
    Restrict R S a b ↔ Restrict Q S a b := by
  constructor
  · intro h
    exact ⟨(heq a b).mp h.1, ancestral_mono_edges (fun p c he => (heq p c).mp he) h.2⟩
  · intro h
    exact ⟨(heq a b).mpr h.1, ancestral_mono_edges (fun p c he => (heq p c).mpr he) h.2⟩

theorem contraction_congr {R Q : Node → Node → Prop} (K : Node → Prop)
    (heq : ∀ a b, R a b ↔ Q a b) (a b : Node) :
    Contract R K a b ↔ Contract Q K a b := by
  constructor
  · intro h
    exact ⟨h.1, h.2.1, hidden_path_mono (fun p c he => (heq p c).mp he) h.2.2⟩
  · intro h
    exact ⟨h.1, h.2.1, hidden_path_mono (fun p c he => (heq p c).mpr he) h.2.2⟩

namespace CellPresentation
variable {R : Coord → Node → Node → Prop} (C : CellPresentation R)

/-- Transport a cell presentation through exact indexed relation equality. -/
def congr {Q : Coord → Node → Node → Prop} (eq : ∀ x a b, R x a b ↔ Q x a b) :
    CellPresentation Q where
  cells := C.cells
  disjoint := C.disjoint
  constant := by
    intro I hI x hx a b
    exact (eq x a b).symm.trans ((C.constant I hI x hx a b).trans (eq I.lo a b))
  covered := by
    intro x a b h
    exact C.covered x a b ((eq x a b).mpr h)

/-- Ancestral-material filtering does not introduce new coordinate breakpoints. -/
def restrict (S : Node → Prop) : CellPresentation (fun x => Restrict (R x) S) where
  cells := C.cells
  disjoint := C.disjoint
  constant := by
    intro I hI x hx a b
    exact restriction_congr S (C.constant I hI x hx) a b
  covered := by
    intro x a b h
    exact C.covered x a b h.1

/-- With a fixed retention predicate, contraction introduces no new coordinate
breakpoints. The original node catalog is retained; discarded nodes are isolated. -/
def contract (K : Node → Prop) : CellPresentation (fun x => Contract (R x) K) where
  cells := C.cells
  disjoint := C.disjoint
  constant := by
    intro I hI x hx a b
    exact contraction_congr K (C.constant I hI x hx) a b
  covered := by
    intro x a b h
    obtain ⟨p, c, he⟩ := hidden_path_has_edge h.2.2
    exact C.covered x p c he

end CellPresentation

theorem restriction_union_acyclic {R : Coord → Node → Node → Prop}
    (acyclic : UnionAcyclic R) (S : Node → Prop) :
    UnionAcyclic (fun x => Restrict (R x) S) := by
  intro a path
  apply acyclic a
  apply reach_mono (R := EraseIndex (fun x => Restrict (R x) S)) ?_ path
  intro p c edge
  obtain ⟨x, he⟩ := edge
  exact ⟨x, he.1⟩

theorem contraction_union_acyclic {R : Coord → Node → Node → Prop}
    (acyclic : UnionAcyclic R) (K : Node → Prop) :
    UnionAcyclic (fun x => Contract (R x) K) := by
  intro a path
  apply acyclic a
  apply reach_substitute (R := EraseIndex (fun x => Contract (R x) K)) ?_ path
  intro p c edge
  obtain ⟨x, he⟩ := edge
  exact fixed_index_path_survives (hidden_path_original he.2.2)

theorem garg_union_acyclic (G : GARG Node Coord) : UnionAcyclic G.AtLocus := by
  intro a path
  apply G.acyclic a
  apply reach_mono (R := EraseIndex G.AtLocus) ?_ path
  intro p c edge
  obtain ⟨x, he⟩ := edge
  exact G.locus_edge_topology he

/-- Convert a supplied finite gARG cell presentation into one for actual
sample-extracted edges. This uses the already checked semantic adapter. -/
def extractedPresentation (G : GARG Node Coord) (C : CellPresentation G.AtLocus) :
    CellPresentation G.ExtractedAt :=
  (C.restrict (fun s => s ∈ G.samples)).congr
    (fun x a b => (WongAlexander.extracted_edge_iff_restrict G x a b).symm)

theorem extracted_union_acyclic (G : GARG Node Coord) : UnionAcyclic G.ExtractedAt := by
  intro a path
  apply G.acyclic a
  apply reach_mono (R := EraseIndex G.ExtractedAt) ?_ path
  intro p c edge
  obtain ⟨x, he⟩ := edge
  exact G.locus_edge_topology he.1

/-- Actual finite interval output for sample restriction, with exact indexed
edge semantics and canonical nonempty records. The finite cells are supplied. -/
theorem sample_restriction_representable (G : GARG Node Coord)
    (C : CellPresentation G.AtLocus) :
    ∃ H : GARG Node Coord, H.samples = G.samples ∧ H.NonemptyAnnotations ∧
      H.CanonicalRecords ∧ (∀ x a b, H.AtLocus x a b ↔ G.ExtractedAt x a b) := by
  obtain ⟨H, hs, hn, hc, he, _⟩ :=
    (extractedPresentation G C).finite_cell_representation G.samples (extracted_union_acyclic G)
  exact ⟨H, hs, hn, hc, he⟩

/-- Actual finite interval output after sample restriction and contraction.
K is fixed across coordinates, and unretained vertices remain isolated in the
same finite node catalog. No minimality or automatic cell extraction is claimed. -/
theorem extracted_contraction_representable (G : GARG Node Coord)
    (C : CellPresentation G.AtLocus) (K : Node → Prop) :
    ∃ H : GARG Node Coord, H.samples = G.samples ∧ H.NonemptyAnnotations ∧
      H.CanonicalRecords ∧
      (∀ x a b, H.AtLocus x a b ↔ Contract (G.ExtractedAt x) K a b) := by
  obtain ⟨H, hs, hn, hc, he, _⟩ :=
    ((extractedPresentation G C).contract K).finite_cell_representation G.samples
      (contraction_union_acyclic (extracted_union_acyclic G) K)
  exact ⟨H, hs, hn, hc, he⟩

/-- The re-encoded output retains exactly the original fixed-coordinate
ancestry between retained starting nodes and retained sample nodes. -/
theorem reencoded_contraction_sample_paths (G : GARG Node Coord)
    (C : CellPresentation G.AtLocus) (K : Node → Prop) :
    ∃ H : GARG Node Coord, H.samples = G.samples ∧ H.NonemptyAnnotations ∧
      H.CanonicalRecords ∧
      (∀ x a b, H.AtLocus x a b ↔ Contract (G.ExtractedAt x) K a b) ∧
      (∀ x a s, K a → K s → s ∈ G.samples →
        (Reach (H.AtLocus x) a s ↔ Reach (G.AtLocus x) a s)) := by
  obtain ⟨H, hs, hn, hc, he⟩ := extracted_contraction_representable G C K
  refine ⟨H, hs, hn, hc, he, ?_⟩
  intro x a s ha hks hsample
  have pathEq : Reach (H.AtLocus x) a s ↔ Reach (Contract (G.ExtractedAt x) K) a s := by
    constructor
    · exact reach_mono (fun p c hp => (he x p c).mp hp)
    · exact reach_mono (fun p c hp => (he x p c).mpr hp)
  exact pathEq.trans (WongAlexander.extracted_contracted_sample_path_iff G x K ha hks hsample)

end
end WongIntervalNormalization

#print axioms WongIntervalNormalization.CellPresentation.finite_cell_representation
#print axioms WongIntervalNormalization.restriction_union_acyclic
#print axioms WongIntervalNormalization.contraction_union_acyclic
#print axioms WongIntervalNormalization.sample_restriction_representable
#print axioms WongIntervalNormalization.extracted_contraction_representable
#print axioms WongIntervalNormalization.reencoded_contraction_sample_paths

