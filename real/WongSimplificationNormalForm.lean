import WongMRCATruncation
import WongLocalSimplification
import WongIntervalCanonicalization

/-!
Appendix G normal form: nonsample nodes retained in a single-parent local
ancestry have at least two children after contraction. The final theorem
composes local-MRCA truncation with sample/branch retention and finite
interval re-encoding. Original node IDs and samples are preserved.
-/
set_option autoImplicit false
namespace WongSimplificationNormalForm
open WongGARG AncestryViews AncestryContraction AncestralRestriction
open WongLocalSimplification WongMRCATruncation
universe u v
noncomputable section
local instance (α : Type*) : DecidableEq α := Classical.decEq α
local instance (P : Prop) : Decidable P := Classical.propDecidable P
variable {Node : Type u} {Coord : Type v} [Fintype Node] [LinearOrder Coord]

omit [Fintype Node] in
/-- Along an initial edge followed by a path, either a first retained node has
been reached or the whole prefix is still hidden. -/
private theorem first_kept_or_hidden {R : Node → Node → Prop} {K : Node → Prop}
    {a b s : Node} (edge : R a b) (path : Reach R b s) :
    (∃ c, K c ∧ HiddenPath R K a c ∧ (b = c ∨ Reach R b c)) ∨
      (¬ K s ∧ HiddenPath R K a s) := by
  induction path with
  | @edge c e =>
    by_cases hb : K b
    · exact Or.inl ⟨b,hb,.edge edge,Or.inl rfl⟩
    · by_cases hs : K c
      · exact Or.inl ⟨_,hs,.snoc (.edge edge) hb e,Or.inr (.edge e)⟩
      · exact Or.inr ⟨hs,.snoc (.edge edge) hb e⟩
  | @snoc c d hp e ih =>
    rcases ih with found | ⟨hc,hidden⟩
    · exact Or.inl found
    · by_cases hd : K d
      · exact Or.inl ⟨d,hd,.snoc hidden hc e,Or.inr (.snoc hp e)⟩
      · exact Or.inr ⟨hd,.snoc hidden hc e⟩

/-- Each outgoing supported branch reaches a first retained child. -/
theorem first_kept_child (G : GARG Node Coord) (x : Coord)
    (K : Node → Prop) (keepSamples : ∀ s ∈ G.samples, K s)
    {a b : Node} (ha : K a) (edge : G.ExtractedAt x a b) :
    ∃ c, Contract (G.ExtractedAt x) K a c ∧ Anc G x b c := by
  obtain ⟨s,hs,same | path⟩ := edge.2
  · subst s
    exact ⟨b,⟨ha,keepSamples b hs,.edge edge⟩,Or.inl rfl⟩
  · have restricted : Reach (G.ExtractedAt x) b s :=
      (WongAlexander.extracted_sample_path_iff G x hs).mpr path
    rcases first_kept_or_hidden edge restricted with ⟨c,hc,hpath,hbc⟩ | ⟨hn,_⟩
    · refine ⟨c,⟨ha,hc,hpath⟩,?_⟩
      rcases hbc with same | path
      · exact Or.inl same
      · exact Or.inr (reach_mono (fun _ _ he => he.1) path)
    · exact False.elim (hn (keepSamples s hs))

/-- Different immediate children in a local tree have disjoint descendants. -/
theorem siblings_disjoint (G : GARG Node Coord) (x : Coord)
    (unique : G.UniqueParentAt x) {a b c z : Node}
    (different : b ≠ c) (ab : G.AtLocus x a b) (ac : G.AtLocus x a c)
    (bz : Anc G x b z) (cz : Anc G x c z) : False := by
  rcases anc_comparable G x unique bz cz with bc | cb
  · rcases bc with same | path
    · exact different same
    · exact strict_not_reverse G x (.edge ab) (ancestor_of_parent G x unique path ac)
  · rcases cb with same | path
    · exact different same.symm
    · exact strict_not_reverse G x (.edge ac) (ancestor_of_parent G x unique path ab)

/-- A nonsample branching node remains branching after all unary paths are
contracted. Unique local parenthood prevents its branches from rejoining. -/
theorem retained_nonsample_branches (G : GARG Node Coord) (x : Coord)
    (unique : G.UniqueParentAt x) {a : Node}
    (kept : KeepSamplesAndBranching G x a) (nonsample : a ∉ G.samples) :
    ∃ b c, b ≠ c ∧
      Contract (G.ExtractedAt x) (KeepSamplesAndBranching G x) a b ∧
      Contract (G.ExtractedAt x) (KeepSamplesAndBranching G x) a c := by
  rcases kept with sample | ⟨b,c,different,ab,ac⟩
  · exact False.elim (nonsample sample)
  · obtain ⟨p,hp,bp⟩ := first_kept_child G x (KeepSamplesAndBranching G x)
      (fun s hs => samples_kept G x hs) (Or.inr ⟨b,c,different,ab,ac⟩) ab
    obtain ⟨q,hq,cq⟩ := first_kept_child G x (KeepSamplesAndBranching G x)
      (fun s hs => samples_kept G x hs) (Or.inr ⟨b,c,different,ab,ac⟩) ac
    refine ⟨p,q,?_,hp,hq⟩
    intro same
    subst q
    exact siblings_disjoint G x unique different ab.1 ac.1 bp cq

omit [Fintype Node] in
private theorem first_edge {R : Node → Node → Prop} {a s : Node}
    (path : Reach R a s) : ∃ b, R a b ∧ (b = s ∨ Reach R b s) := by
  induction path with
  | edge e => exact ⟨_,e,Or.inl rfl⟩
  | snoc hp e ih =>
    obtain ⟨b,ab,same | tail⟩ := ih
    · subst b
      exact ⟨_,ab,Or.inr (.edge e)⟩
    · exact ⟨b,ab,Or.inr (.snoc tail e)⟩

/-- An MRCA is a designated sample or genuinely branches in sample ancestry.
This proof uses the actual latest-common-ancestor property and nonempty samples. -/
theorem mrca_kept (G : GARG Node Coord) (x : Coord)
    (nonempty : G.samples.Nonempty) {m : Node} (hm : IsMRCA G x m) :
    KeepSamplesAndBranching G x m := by
  by_cases sample : m ∈ G.samples
  · exact Or.inl sample
  by_contra absent
  have pathTo : ∀ s ∈ G.samples, Reach (G.ExtractedAt x) m s := by
    intro s hs
    rcases hm.1 s hs with same | path
    · exact False.elim (sample (same ▸ hs))
    · exact (WongAlexander.extracted_sample_path_iff G x hs).mpr path
  obtain ⟨s,hs⟩ := nonempty
  obtain ⟨b,ab,_⟩ := first_edge (pathTo s hs)
  have common : Common G x b := by
    intro t ht
    obtain ⟨c,ac,tail⟩ := first_edge (pathTo t ht)
    have same : b = c := by
      by_contra different
      exact absent (Or.inr ⟨b,c,different,ab,ac⟩)
    subst c
    rcases tail with same | path
    · exact Or.inl same
    · exact Or.inr (reach_mono (fun _ _ he => he.1) path)
  exact strict_not_reverse G x (.edge ab.1) (hm.2 b common)

/-- Retiring fully-coalesced ancestry retains the local MRCA as a sample or
branch point, including the ancestral-sample boundary case. -/
theorem truncated_mrca_kept (G : GARG Node Coord) (x : Coord)
    (nonempty : G.samples.Nonempty) {m : Node} (hm : IsMRCA G x m) :
    KeepSamplesAndBranching (truncate G) x m := by
  rcases mrca_kept G x nonempty hm with sample | ⟨b,c,different,ab,ac⟩
  · exact Or.inl sample
  · have survives : ∀ z, G.ExtractedAt x m z → (truncate G).ExtractedAt x m z := by
      intro z edge
      have he : (truncate G).AtLocus x m z := (truncate_at_iff G x m z).mpr
        ⟨edge,fun common => strict_not_reverse G x (.edge edge.1) (hm.2 z common)⟩
      exact ⟨he,truncate_sample_supported G x m z he⟩
    exact Or.inr ⟨b,c,different,survives b ab,survives c ac⟩

/-- All incident nonsample nodes have at least two outgoing children.
Unused catalogue IDs may remain isolated; sampled ancestral nodes may be unary. -/
def NoNonsampleUnary (G : GARG Node Coord) (x : Coord) : Prop :=
  ∀ a, a ∉ G.samples → (∃ b, G.AtLocus x a b ∨ G.AtLocus x b a) →
    ∃ b c, b ≠ c ∧ G.AtLocus x a b ∧ G.AtLocus x a c

theorem represented_contraction_normal (G H : GARG Node Coord)
    (samples : H.samples = G.samples)
    (edges : ∀ x a b, H.AtLocus x a b ↔
      Contract (G.ExtractedAt x) (KeepSamplesAndBranching G x) a b)
    (x : Coord) (unique : G.UniqueParentAt x) : NoNonsampleUnary H x := by
  intro a hn ⟨b,incident⟩
  have kept : KeepSamplesAndBranching G x a := by
    rcases incident with edge | edge
    · exact ((edges x a b).mp edge).1
    · exact ((edges x b a).mp edge).2.1
  have notSample : a ∉ G.samples := by simpa only [samples] using hn
  obtain ⟨p,q,different,hp,hq⟩ := retained_nonsample_branches G x unique kept notSample
  exact ⟨p,q,different,(edges x a p).mpr hp,(edges x a q).mpr hq⟩

/-- Normal-form consequence of the existing actual finite interval output. -/
theorem finite_local_normal_form (G : GARG Node Coord) :
    ∃ H : GARG Node Coord,
      H.samples = G.samples ∧ H.NonemptyAnnotations ∧ H.CanonicalRecords ∧
      (∀ x a b, H.AtLocus x a b ↔
        Contract (G.ExtractedAt x) (KeepSamplesAndBranching G x) a b) ∧
      (∀ x, G.UniqueParentAt x → H.UniqueParentAt x ∧ NoNonsampleUnary H x) ∧
      H.SampleSupported ∧ H.breakpoints ⊆ G.breakpoints ∧
      (∀ x a s, KeepSamplesAndBranching G x a → s ∈ G.samples →
        (Reach (H.AtLocus x) a s ↔ Reach (G.AtLocus x) a s)) := by
  obtain ⟨H,hs,hn,hc,he,hpath,hu,hsup,hbp,_⟩ :=
    samples_and_branching_representable G
  refine ⟨H,hs,hn,hc,he,?_,hsup,hbp,?_⟩
  · intro x unique
    exact ⟨hu x unique,represented_contraction_normal G H hs he x unique⟩
  · exact hpath

/-- Source-composed stopping and contraction semantics, in an actual finite
interval gARG. This is Fig.3 local-MRCA truncation followed by the final
Appendix G sample/branching retention. It assumes no dates or mutation model. -/
theorem finite_resolved_normal_form (G : GARG Node Coord) :
    ∃ H : GARG Node Coord,
      H.samples = G.samples ∧ H.NonemptyAnnotations ∧ H.CanonicalRecords ∧
      (∀ x a b, H.AtLocus x a b ↔
        Contract ((truncate G).ExtractedAt x)
          (KeepSamplesAndBranching (truncate G) x) a b) ∧
      (∀ x, G.UniqueParentAt x → H.UniqueParentAt x ∧ NoNonsampleUnary H x) ∧
      H.SampleSupported ∧ H.breakpoints ⊆ G.breakpoints ∧
      (∀ x a s, a ∈ G.samples → s ∈ G.samples →
        (Reach (H.AtLocus x) a s ↔ Reach (G.AtLocus x) a s)) ∧
      (∀ x m s, G.samples.Nonempty → IsMRCA G x m → s ∈ G.samples →
        (Reach (H.AtLocus x) m s ↔ Reach (G.AtLocus x) m s)) := by
  obtain ⟨H,hs,hn,hc,he,hu,hsup,hbp,hpath⟩ := finite_local_normal_form (truncate G)
  refine ⟨H,hs,hn,hc,he,?_,hsup,?_,?_,?_⟩
  · intro x unique
    exact hu x (truncate_unique_parent G x unique)
  · exact Finset.Subset.trans hbp (truncate_breakpoints G)
  · intro x a s ha hsample
    exact (hpath x a s (samples_kept (truncate G) x ha) hsample).trans
      (truncate_sample_paths G x ha hsample)
  · intro x m s nonempty hm hsample
    exact (hpath x m s (truncated_mrca_kept G x nonempty hm) hsample).trans
      (truncate_mrca_paths G x hm hsample)

/-- Canonical interval storage preserves all local paths. -/
theorem canonicalize_paths (G : GARG Node Coord) (x : Coord) (a b : Node) :
    Reach ((WongIntervalCanonicalization.canonicalize G).AtLocus x) a b ↔
      Reach (G.AtLocus x) a b :=
  ⟨reach_mono (fun p c he => (WongIntervalCanonicalization.canonicalize_at G x p c).mp he),
   reach_mono (fun p c he => (WongIntervalCanonicalization.canonicalize_at G x p c).mpr he)⟩

/-- Combined source-faithful deterministic pipeline. The final actual graph has
maximal interval annotations, no nonsample unary vertices where local parents
are unique, the same samples and relevant paths, and no added breakpoints.
The final fixed-point clause concerns interval storage, not stochastic laws. -/
theorem canonical_resolved_normal_form (G : GARG Node Coord) :
    ∃ H : GARG Node Coord,
      H.samples = G.samples ∧ H.NonemptyAnnotations ∧ H.CanonicalRecords ∧
      (∀ x a b, H.AtLocus x a b ↔
        Contract ((truncate G).ExtractedAt x)
          (KeepSamplesAndBranching (truncate G) x) a b) ∧
      (∀ x, G.UniqueParentAt x → H.UniqueParentAt x ∧ NoNonsampleUnary H x) ∧
      H.SampleSupported ∧ H.breakpoints ⊆ G.breakpoints ∧
      (∀ x a s, a ∈ G.samples → s ∈ G.samples →
        (Reach (H.AtLocus x) a s ↔ Reach (G.AtLocus x) a s)) ∧
      (∀ x m s, G.samples.Nonempty → IsMRCA G x m → s ∈ G.samples →
        (Reach (H.AtLocus x) m s ↔ Reach (G.AtLocus x) m s)) ∧
      (∀ e ∈ H.records, ∀ I ∈ e.regions, ∀ J ∈ e.regions,
        I ≠ J → I.hi < J.lo ∨ J.hi < I.lo) ∧
      WongIntervalCanonicalization.canonicalize H = H := by
  obtain ⟨H,hs,_,_,he,hu,hsup,hbp,hss,hms⟩ := finite_resolved_normal_form G
  let C := WongIntervalCanonicalization.canonicalize H
  have edge : ∀ x a b, C.AtLocus x a b ↔ H.AtLocus x a b :=
    WongIntervalCanonicalization.canonicalize_at H
  refine ⟨C,hs,WongIntervalCanonicalization.canonicalize_nonempty H,
    WongIntervalCanonicalization.canonicalize_canonical H,?_,?_,?_,?_,?_,?_,
    WongIntervalCanonicalization.canonicalize_maximal H,
    WongIntervalCanonicalization.canonicalize_idempotent H⟩
  · intro x a b
    exact (edge x a b).trans (he x a b)
  · intro x unique
    obtain ⟨parent,normal⟩ := hu x unique
    constructor
    · intro c a b ha hb
      exact parent c a b ((edge x a c).mp ha) ((edge x b c).mp hb)
    · intro a hn ⟨b,incident⟩
      have hi : ∃ b, H.AtLocus x a b ∨ H.AtLocus x b a :=
        ⟨b,incident.elim (fun h => Or.inl ((edge x a b).mp h))
          (fun h => Or.inr ((edge x b a).mp h))⟩
      obtain ⟨p,q,different,hp,hq⟩ := normal a hn hi
      exact ⟨p,q,different,(edge x a p).mpr hp,(edge x a q).mpr hq⟩
  · intro x a b hb
    obtain ⟨s,hs,same | path⟩ := hsup x a b ((edge x a b).mp hb)
    · exact ⟨s,hs,Or.inl same⟩
    · exact ⟨s,hs,Or.inr ((canonicalize_paths H x b s).mpr path)⟩
  · exact Finset.Subset.trans (WongIntervalCanonicalization.canonicalize_breakpoints H) hbp
  · intro x a s ha hs
    exact (canonicalize_paths H x a s).trans (hss x a s ha hs)
  · intro x m s nonempty hm hs
    exact (canonicalize_paths H x m s).trans (hms x m s nonempty hm hs)

end
end WongSimplificationNormalForm

#print axioms WongSimplificationNormalForm.first_kept_child
#print axioms WongSimplificationNormalForm.siblings_disjoint
#print axioms WongSimplificationNormalForm.retained_nonsample_branches
#print axioms WongSimplificationNormalForm.represented_contraction_normal
#print axioms WongSimplificationNormalForm.finite_local_normal_form
#print axioms WongSimplificationNormalForm.finite_resolved_normal_form

#print axioms WongSimplificationNormalForm.mrca_kept
#print axioms WongSimplificationNormalForm.truncated_mrca_kept

#print axioms WongSimplificationNormalForm.canonicalize_paths
#print axioms WongSimplificationNormalForm.canonical_resolved_normal_form
