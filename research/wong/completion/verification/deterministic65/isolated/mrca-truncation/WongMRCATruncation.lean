import WongSimplification

/-!
# Truncate fully coalesced material above a local genetic MRCA

Wong et al. (2024), Fig. 3 discussion (journal p. 4) and Appendix B (p. 13).
This operation is different from merely retaining ancestry of some sample.
All statements concern genetic ancestry at a fixed genomic coordinate.
-/
namespace WongMRCATruncation
open WongGARG AncestryViews WongIntervalNormalization WongSimplification
universe u v
noncomputable section
local instance (α : Type*) : DecidableEq α := Classical.decEq α
local instance (P : Prop) : Decidable P := Classical.propDecidable P
variable {Node : Type u} {Coord : Type v} [Fintype Node] [LinearOrder Coord]

/-- Reflexive genetic ancestry at one locus, including an ancestral sample itself. -/
def Anc (G : GARG Node Coord) (x : Coord) (a b : Node) : Prop :=
  a = b ∨ Reach (G.AtLocus x) a b

/-- The node carries ancestry of every designated sample at this locus. -/
def Common (G : GARG Node Coord) (x : Coord) (a : Node) : Prop :=
  ∀ s ∈ G.samples, Anc G x a s

/-- A latest common ancestor, with every common ancestor at or above it. -/
def IsMRCA (G : GARG Node Coord) (x : Coord) (m : Node) : Prop :=
  Common G x m ∧ ∀ a, Common G x a → Anc G x a m

/-- Retain supported local edges only until their child has fully coalesced.
The edge INTO the local MRCA is removed, and paths below it remain. -/
def TruncatedAt (G : GARG Node Coord) (x : Coord) (p c : Node) : Prop :=
  G.ExtractedAt x p c ∧ ¬ Common G x c

variable (G : GARG Node Coord) (x : Coord)

theorem anc_trans {a b c : Node} (hab : Anc G x a b) (hbc : Anc G x b c) :
    Anc G x a c := by
  rcases hab with rfl | hab
  · exact hbc
  rcases hbc with rfl | hbc
  · exact Or.inr hab
  · exact Or.inr (AncestralRestriction.reach_trans hab hbc)

theorem anc_antisymm {a b : Node} (hab : Anc G x a b) (hba : Anc G x b a) : a = b := by
  rcases hab with h | h
  · exact h
  rcases hba with hba | hba
  · exact hba.symm
  · exact False.elim (G.locus_acyclic x a (AncestralRestriction.reach_trans h hba))

theorem strict_not_reverse {a b : Node} (hab : Reach (G.AtLocus x) a b)
    (hba : Anc G x b a) : False := by
  rcases hba with hba | hba
  · subst b
    exact G.locus_acyclic x a hab
  · exact G.locus_acyclic x a (AncestralRestriction.reach_trans hab hba)

theorem anc_comparable (unique : G.UniqueParentAt x) {a b s : Node}
    (ha : Anc G x a s) (hb : Anc G x b s) : Anc G x a b ∨ Anc G x b a := by
  rcases ha with rfl | ha
  · exact Or.inr hb
  rcases hb with rfl | hb
  · exact Or.inl (Or.inr ha)
  rcases G.local_ancestors_comparable x unique ha hb with h | h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr h)
  · exact Or.inr (Or.inr h)

theorem common_upwards {a b : Node} (hab : Anc G x a b) (hb : Common G x b) :
    Common G x a := fun s hs => anc_trans G x hab (hb s hs)

theorem mrca_unique {m n : Node} (hm : IsMRCA G x m) (hn : IsMRCA G x n) : m = n :=
  anc_antisymm G x (hn.2 m hm.1) (hm.2 n hn.1)

/-- Finite local single-parent ancestry with a common ancestor has a unique
latest one. It is obtained by maximizing a derived topological code. -/
theorem exists_unique_mrca (samples : G.samples.Nonempty) (unique : G.UniqueParentAt x)
    (common : ∃ a, Common G x a) : ∃! m, IsMRCA G x m := by
  let A := Finset.univ.filter (Common G x)
  have hA : A.Nonempty := by
    obtain ⟨a,ha⟩ := common
    exact ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha⟩⟩
  obtain ⟨m,hm,hmax⟩ := Finset.exists_max_image A G.orderCode hA
  have hmc : Common G x m := (Finset.mem_filter.mp hm).2
  have hmr : IsMRCA G x m := by
    refine ⟨hmc,?_⟩
    intro a ha
    obtain ⟨s,hs⟩ := samples
    rcases anc_comparable G x unique (ha s hs) (hmc s hs) with ham | hma
    · exact ham
    rcases hma with same | path
    · exact Or.inl same.symm
    · have hlt : G.orderCode m < G.orderCode a :=
        reach_time_increases G.orderCode (fun _ _ he => G.orderCode_edge (G.locus_edge_topology he)) path
      have hle := hmax a (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha⟩)
      exact False.elim ((not_lt_of_ge hle) hlt)
  exact ⟨m,hmr,fun n hn => mrca_unique G x hn hmr⟩

theorem common_iff_ancestor_mrca {m : Node} (hm : IsMRCA G x m) (a : Node) :
    Common G x a ↔ Anc G x a m :=
  ⟨fun ha => hm.2 a ha, fun ham => common_upwards G x ham hm.1⟩

/-- Source-equivalent deletion rule: remove the edge into the MRCA and all
supported edges with a child above it. -/
theorem truncation_iff_cut_above {m : Node} (hm : IsMRCA G x m) (p c : Node) :
    TruncatedAt G x p c ↔ G.ExtractedAt x p c ∧ ¬ Anc G x c m := by
  rw [TruncatedAt,common_iff_ancestor_mrca G x hm c]


/-- An edge into fully coalesced material can be sample-supported yet is removed.
This formalizes why truncation is stronger than ordinary support restriction. -/
theorem supported_but_removed (samples : G.samples.Nonempty) {p c : Node}
    (hc : Common G x c) (edge : G.AtLocus x p c) :
    G.ExtractedAt x p c ∧ ¬ TruncatedAt G x p c := by
  obtain ⟨s,hs⟩ := samples
  exact ⟨⟨edge,s,hs,hc s hs⟩,fun h => h.2 hc⟩

/-- In a local single-parent graph, a strict ancestor of a child is its parent
or an ancestor of that parent. -/
theorem ancestor_of_parent (unique : G.UniqueParentAt x) {a p c : Node}
    (path : Reach (G.AtLocus x) a c) (edge : G.AtLocus x p c) : Anc G x a p := by
  cases path with
  | edge e => exact Or.inl (unique c a p e edge)
  | @snoc b _ hp e =>
    have same := unique c b p e edge
    subst b
    exact Or.inr hp

/-- With a latest common ancestor, truncation keeps precisely supported edges
whose parent is at or below that ancestor. -/
theorem truncation_iff_below_mrca (unique : G.UniqueParentAt x)
    {m : Node} (hm : IsMRCA G x m) (p c : Node) :
    TruncatedAt G x p c ↔ G.ExtractedAt x p c ∧ Anc G x m p := by
  constructor
  · rintro ⟨he,hn⟩
    refine ⟨he,?_⟩
    obtain ⟨s,hs,hcs⟩ := he.2
    rcases anc_comparable G x unique (hm.1 s hs) hcs with hmc | hcm
    · rcases hmc with same | path
      · exact False.elim (hn (same ▸ hm.1))
      · exact ancestor_of_parent G x unique path he.1
    · exact False.elim (hn ((common_iff_ancestor_mrca G x hm c).mpr hcm))
  · rintro ⟨he,hmp⟩
    refine ⟨he,?_⟩
    intro hc
    have hmc : Reach (G.AtLocus x) m c := by
      rcases hmp with rfl | hp
      · exact .edge he.1
      · exact .snoc hp he.1
    exact strict_not_reverse G x hmc (hm.2 c hc)

private theorem support_parent {p c : Node} (he : G.AtLocus x p c)
    (hc : G.SampleAncestral x c) : G.SampleAncestral x p := by
  obtain ⟨s,hs,rfl | path⟩ := hc
  · exact ⟨c,hs,Or.inr (.edge he)⟩
  · exact ⟨s,hs,Or.inr (AncestralRestriction.reach_trans (.edge he) path)⟩

/-- Every original path whose strict descendants are not fully coalesced is
retained when it ends in sample-supported material. -/
private theorem path_truncates {a b : Node}
    (path : Reach (G.AtLocus x) a b)
    (below : ∀ c, Reach (G.AtLocus x) a c → ¬ Common G x c)
    (support : G.SampleAncestral x b) : Reach (TruncatedAt G x) a b := by
  revert support
  induction path with
  | edge he =>
    intro support
    exact .edge ⟨⟨he,support⟩,below _ (.edge he)⟩
  | @snoc b c path he ih =>
    intro support
    exact .snoc (ih (support_parent G x he support))
      ⟨⟨he,support⟩,below _ (.snoc path he)⟩

/-- Even when a designated sample is itself ancestral, sample-to-sample
paths survive; the proof does not require local single parenthood. -/
theorem sample_paths_preserved {a s : Node} (ha : a ∈ G.samples) (hs : s ∈ G.samples) :
    Reach (TruncatedAt G x) a s ↔ Reach (G.AtLocus x) a s := by
  constructor
  · exact reach_mono (fun _ _ h => h.1.1)
  · intro path
    apply path_truncates G x path ?_ ⟨s,hs,Or.inl rfl⟩
    intro c hac hc
    exact strict_not_reverse G x hac (hc a ha)

/-- Every strict MRCA-to-sample path survives, including ancestral-sample inputs. -/
theorem mrca_sample_paths_preserved {m s : Node} (hm : IsMRCA G x m)
    (hs : s ∈ G.samples) :
    Reach (TruncatedAt G x) m s ↔ Reach (G.AtLocus x) m s := by
  constructor
  · exact reach_mono (fun _ _ h => h.1.1)
  · intro path
    apply path_truncates G x path ?_ ⟨s,hs,Or.inl rfl⟩
    intro c hmc hc
    exact strict_not_reverse G x hmc (hm.2 c hc)

/-- The reflexive version covers a singleton or a sample that is the MRCA. -/
theorem mrca_reaches_every_sample {m : Node} (hm : IsMRCA G x m)
    {s : Node} (hs : s ∈ G.samples) :
    m = s ∨ Reach (TruncatedAt G x) m s := by
  rcases hm.1 s hs with same | path
  · exact Or.inl same
  · exact Or.inr ((mrca_sample_paths_preserved G x hm hs).mpr path)

theorem no_incoming_mrca {m : Node} (hm : IsMRCA G x m) (p : Node) :
    ¬ TruncatedAt G x p m := fun h => h.2 hm.1

/-- Fully coalesced material is removed, but every remaining edge is supported
by a sample in the resulting truncated graph itself. -/
theorem truncated_support {p c : Node} (h : TruncatedAt G x p c) :
    ∃ s ∈ G.samples, c = s ∨ Reach (TruncatedAt G x) c s := by
  obtain ⟨s,hs,same | path⟩ := h.1.2
  · exact ⟨s,hs,Or.inl same⟩
  · refine ⟨s,hs,Or.inr (path_truncates G x path ?_ ⟨s,hs,Or.inl rfl⟩)⟩
    intro d hcd hd
    exact h.2 (common_upwards G x (Or.inr hcd) hd)

/-- If no local common ancestor exists, no fully coalesced segment is claimed;
the operation agrees exactly with ordinary sample support restriction. -/
theorem no_common_no_extra_truncation (h : ¬ ∃ a, Common G x a) (p c : Node) :
    TruncatedAt G x p c ↔ G.ExtractedAt x p c :=
  ⟨fun he => he.1, fun he => ⟨he,fun hc => h ⟨c,hc⟩⟩⟩

/-- A sampled common ancestor is automatically the latest one. -/
theorem ancestral_sample_is_mrca {s : Node} (hs : s ∈ G.samples) (hc : Common G x s) :
    IsMRCA G x s := ⟨hc,fun _ ha => ha s hs⟩

theorem singleton_sample_is_mrca {s : Node} (samples : G.samples = {s}) :
    IsMRCA G x s := by
  apply ancestral_sample_is_mrca G x (by simp [samples])
  intro t ht
  have hts : t = s := by simpa [samples] using ht
  exact Or.inl hts.symm

/-- With one sample, its locus is already fully coalesced: all edges are removed,
while the finite output construction below retains the sample identifier. -/
theorem singleton_has_no_edges {s : Node} (samples : G.samples = {s}) (p c : Node) :
    ¬ TruncatedAt G x p c := by
  rintro ⟨⟨_,t,ht,hct⟩,hn⟩
  have hts : t = s := by simpa [samples] using ht
  subst t
  apply hn
  intro u hu
  have hus : u = s := by simpa [samples] using hu
  subst u
  exact hct

theorem empty_samples_no_edges (samples : G.samples = ∅) (p c : Node) :
    ¬ TruncatedAt G x p c := by
  rintro ⟨⟨_,s,hs,_⟩,_⟩
  simp [samples] at hs

/-- Two distinct sampled local roots cannot have a common ancestor. This is a
concrete multiple-root case; mere unused isolated catalogue nodes do not count. -/
theorem distinct_sample_roots_no_common {r s : Node} (hr : r ∈ G.samples)
    (hs : s ∈ G.samples) (different : r ≠ s)
    (rootR : ∀ p, ¬ G.AtLocus x p r) (rootS : ∀ p, ¬ G.AtLocus x p s) :
    ¬ ∃ a, Common G x a := by
  rintro ⟨a,ha⟩
  have har : a = r := by
    rcases ha r hr with same | path
    · exact same
    · cases path with
      | edge he => exact False.elim (rootR _ he)
      | snoc _ he => exact False.elim (rootR _ he)
  have has : a = s := by
    rcases ha s hs with same | path
    · exact same
    · cases path with
      | edge he => exact False.elim (rootS _ he)
      | snoc _ he => exact False.elim (rootS _ he)
  exact different (har.symm.trans has)

/-- Full local relation equality transports the common-ancestor predicate. -/
theorem common_congr {y : Coord} (same : ∀ a b, G.AtLocus x a b ↔ G.AtLocus y a b)
    (a : Node) : Common G x a ↔ Common G y a := by
  constructor
  · intro h s hs
    rcases h s hs with eq | path
    · exact Or.inl eq
    · exact Or.inr (reach_mono (fun p c he => (same p c).mp he) path)
  · intro h s hs
    rcases h s hs with eq | path
    · exact Or.inl eq
    · exact Or.inr (reach_mono (fun p c he => (same p c).mpr he) path)

/-- The coalescence test is constant on automatically generated source cells. -/
def truncatedPresentation : CellPresentation (TruncatedAt G) where
  cells := WongBreakpointCells.cells G.breakpoints
  disjoint := WongBreakpointCells.cells_pairwise_disjoint G.breakpoints
  constant := by
    intro I hI y hy p c
    have hE := (extractedPresentation G (automaticPresentation G)).constant I hI y hy p c
    have hC := common_congr G y
      (fun a b => WongBreakpointCells.locus_constant_on_cell G hI hy a b) c
    exact and_congr hE (not_congr hC)
  covered := by
    intro y p c h
    exact WongBreakpointCells.locus_covered G h.1.1

theorem truncated_union_acyclic : UnionAcyclic (TruncatedAt G) := by
  intro a path
  apply G.acyclic a
  apply reach_mono (R := EraseIndex (TruncatedAt G)) ?_ path
  rintro p c ⟨y,h⟩
  exact G.locus_edge_topology h.1.1

/-- Actual finite interval output; unused original catalogue IDs remain isolated. -/
def truncate : GARG Node Coord :=
  (truncatedPresentation G).toGARG G.samples (truncated_union_acyclic G)

theorem truncate_at_iff (p c : Node) :
    (truncate G).AtLocus x p c ↔ TruncatedAt G x p c :=
  (truncatedPresentation G).toGARG_at_iff G.samples (truncated_union_acyclic G) x p c

theorem truncate_unique_parent (unique : G.UniqueParentAt x) :
    (truncate G).UniqueParentAt x := by
  intro c a b ha hb
  exact unique c a b ((truncate_at_iff G x a c).mp ha).1.1
    ((truncate_at_iff G x b c).mp hb).1.1

theorem truncate_sample_supported : (truncate G).SampleSupported := by
  intro y p c h
  obtain ⟨s,hs,same | path⟩ := truncated_support G y ((truncate_at_iff G y p c).mp h)
  · exact ⟨s,hs,Or.inl same⟩
  · exact ⟨s,hs,Or.inr (reach_mono (fun a b he => (truncate_at_iff G y a b).mpr he) path)⟩

theorem truncate_breakpoints : (truncate G).breakpoints ⊆ G.breakpoints := by
  apply reencoding_breakpoints_subset (truncatedPresentation G) G.samples
    (truncated_union_acyclic G) G.breakpoints
  intro I hI
  have bounds := (WongBreakpointCells.mem_cells_iff G.breakpoints I).mp hI
  exact ⟨bounds.1,bounds.2.1⟩

theorem truncate_sample_paths {a s : Node} (ha : a ∈ G.samples) (hs : s ∈ G.samples) :
    Reach ((truncate G).AtLocus x) a s ↔ Reach (G.AtLocus x) a s := by
  have eq : Reach ((truncate G).AtLocus x) a s ↔ Reach (TruncatedAt G x) a s :=
    ⟨reach_mono (fun p c he => (truncate_at_iff G x p c).mp he),
     reach_mono (fun p c he => (truncate_at_iff G x p c).mpr he)⟩
  exact eq.trans (sample_paths_preserved G x ha hs)

theorem truncate_mrca_paths {m s : Node} (hm : IsMRCA G x m) (hs : s ∈ G.samples) :
    Reach ((truncate G).AtLocus x) m s ↔ Reach (G.AtLocus x) m s := by
  have eq : Reach ((truncate G).AtLocus x) m s ↔ Reach (TruncatedAt G x) m s :=
    ⟨reach_mono (fun p c he => (truncate_at_iff G x p c).mp he),
     reach_mono (fun p c he => (truncate_at_iff G x p c).mpr he)⟩
  exact eq.trans (mrca_sample_paths_preserved G x hm hs)

/-- Finite canonical output, exact stopping semantics, sample paths and support,
local single parenthood and unchanged endpoint supply, all in one statement. -/
theorem finite_mrca_truncation :
    ∃ H : GARG Node Coord,
      H.samples = G.samples ∧ H.NonemptyAnnotations ∧ H.CanonicalRecords ∧
      (∀ y p c, H.AtLocus y p c ↔ TruncatedAt G y p c) ∧
      H.SampleSupported ∧
      (∀ y, G.UniqueParentAt y → H.UniqueParentAt y) ∧
      H.breakpoints ⊆ G.breakpoints ∧
      (∀ y a s, a ∈ G.samples → s ∈ G.samples →
        (Reach (H.AtLocus y) a s ↔ Reach (G.AtLocus y) a s)) ∧
      (∀ y m s, IsMRCA G y m → s ∈ G.samples →
        (Reach (H.AtLocus y) m s ↔ Reach (G.AtLocus y) m s)) :=
  ⟨truncate G,rfl,
    (truncatedPresentation G).toGARG_nonempty G.samples (truncated_union_acyclic G),
    (truncatedPresentation G).toGARG_canonical G.samples (truncated_union_acyclic G),
    truncate_at_iff G,truncate_sample_supported G,truncate_unique_parent G,
    truncate_breakpoints G,
    fun y _ _ ha hs => truncate_sample_paths G y ha hs,
    fun y _ _ hm hs => truncate_mrca_paths G y hm hs⟩

end
end WongMRCATruncation

#print axioms WongMRCATruncation.exists_unique_mrca
#print axioms WongMRCATruncation.mrca_unique
#print axioms WongMRCATruncation.common_iff_ancestor_mrca
#print axioms WongMRCATruncation.truncation_iff_cut_above
#print axioms WongMRCATruncation.truncation_iff_below_mrca
#print axioms WongMRCATruncation.sample_paths_preserved
#print axioms WongMRCATruncation.mrca_sample_paths_preserved
#print axioms WongMRCATruncation.mrca_reaches_every_sample
#print axioms WongMRCATruncation.no_incoming_mrca
#print axioms WongMRCATruncation.truncated_support
#print axioms WongMRCATruncation.no_common_no_extra_truncation
#print axioms WongMRCATruncation.ancestral_sample_is_mrca
#print axioms WongMRCATruncation.singleton_sample_is_mrca
#print axioms WongMRCATruncation.singleton_has_no_edges
#print axioms WongMRCATruncation.empty_samples_no_edges
#print axioms WongMRCATruncation.distinct_sample_roots_no_common
#print axioms WongMRCATruncation.truncate_at_iff
#print axioms WongMRCATruncation.truncate_unique_parent
#print axioms WongMRCATruncation.truncate_sample_supported
#print axioms WongMRCATruncation.truncate_breakpoints
#print axioms WongMRCATruncation.truncate_sample_paths
#print axioms WongMRCATruncation.truncate_mrca_paths
#print axioms WongMRCATruncation.finite_mrca_truncation

#print axioms WongMRCATruncation.supported_but_removed
