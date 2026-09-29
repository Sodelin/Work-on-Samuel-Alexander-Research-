import WongGARG
import RealBridges
import SamuelAlexanderResearch.AncestralRestriction
import SamuelAlexanderResearch.AncestryContraction
import SamuelAlexanderResearch.FiniteHistoryCompletion

/-!
# Actual finite gARGs, sample restriction, and opposite infinite completions

This composes the finite interval gARG model with the generic ancestral-material
restriction and the Alexander species definitions. The completion witnesses
are abstract graph extensions of a finite DAG. They do not infer genome owners,
a reproductive pedigree, future genomic intervals, or biological species.
-/

namespace WongAlexander

open AncestryViews SpeciesBridge SpeciesGlobalIAP FiniteHistoryCompletion

universe u v

noncomputable section

variable {Node : Type u} {Coord : Type v} [Fintype Node] [LinearOrder Coord]
variable (G : WongGARG.GARG Node Coord)

/-- The gARG's source-oriented ancestry predicate is exactly the generic one. -/
theorem sample_ancestral_iff (x : Coord) (a : Node) :
    G.SampleAncestral x a ↔
      AncestralRestriction.Ancestral (G.AtLocus x) (fun s => s ∈ G.samples) a := by
  constructor
  · rintro ⟨s, hs, same | path⟩
    · subst a
      exact Or.inl hs
    · exact Or.inr ⟨s, hs, path⟩
  · intro ha
    rcases ha with sample | ⟨s, hs, path⟩
    · exact ⟨a, sample, Or.inl rfl⟩
    · exact ⟨s, hs, Or.inr path⟩

/-- Actual interval-edge extraction instantiates the generic restriction. -/
theorem extracted_edge_iff_restrict (x : Coord) (a b : Node) :
    G.ExtractedAt x a b ↔
      AncestralRestriction.Restrict (G.AtLocus x) (fun s => s ∈ G.samples) a b := by
  constructor
  · intro he
    exact ⟨he.1, (sample_ancestral_iff G x b).mp he.2⟩
  · intro he
    exact ⟨he.1, (sample_ancestral_iff G x b).mpr he.2⟩

/-- For the actual finite interval gARG, extraction preserves exactly all
original fixed-location paths ending at a designated sample. -/
theorem extracted_sample_path_iff (x : Coord) {a s : Node} (hs : s ∈ G.samples) :
    Reach (G.ExtractedAt x) a s ↔ Reach (G.AtLocus x) a s := by
  constructor
  · intro path
    exact AncestralRestriction.restricted_path_original
      (reach_mono (fun p c he => (extracted_edge_iff_restrict G x p c).mp he) path)
  · intro path
    have retained :=
      (AncestralRestriction.sample_path_iff (R := G.AtLocus x) hs).mpr path
    exact reach_mono (fun p c he => (extracted_edge_iff_restrict G x p c).mpr he) retained

/-- Actual interval gARG sample resolution followed by retained-node
elimination preserves exactly fixed-location ancestry into a retained sample.
No unary-node criterion or tskit algorithm is assumed. -/
theorem extracted_contracted_sample_path_iff (x : Coord) (K : Node → Prop)
    {a s : Node} (ha : K a) (hs : K s) (sample : s ∈ G.samples) :
    Reach (AncestryContraction.Contract (G.ExtractedAt x) K) a s ↔
      Reach (G.AtLocus x) a s :=
  (AncestryContraction.retained_path_iff ha hs).trans
    (extracted_sample_path_iff G x sample)
/-- An actual finite node catalog cannot itself satisfy the infinite-population
vertex axiom. No assumption about the biological owners of nodes is involved. -/
theorem finite_catalog_not_infinite : ¬ BirthOrder.InfiniteVertices Node := by
  classical
  intro hinf
  apply (BirthOrder.infiniteVertices_iff_not_finiteCover Node).mp hinf
  refine ⟨Finset.univ.toList, ?_⟩
  intro a _
  simp

/-- Literal real birthdates, finite real date sublevels, finitely many children,
and an infinite natural-number population. -/
def RealDatedBiosphere (E : Graph) : Prop :=
  ∃ birth : Nat → ℝ,
    (∀ a b, E a b → birth a < birth b) ∧
    (∀ r : ℝ, BirthOrder.FiniteCover (fun a => birth a ≤ r)) ∧
    (∀ a, FiniteSupport (E a)) ∧ InfiniteSupport Whole

theorem natural_biosphere_has_real_dates {E : Graph} (h : NaturalDateBiosphere E) :
    RealDatedBiosphere E := by
  refine ⟨fun a => (a : ℝ), ?_, ?_, h.2.2.1, h.2.2.2⟩
  · intro a b he
    change (a : ℝ) < (b : ℝ)
    exact_mod_cast h.1 a b he
  · intro r
    obtain ⟨n, hn⟩ := exists_nat_gt r
    refine ⟨List.range n, ?_⟩
    intro a ha
    apply List.mem_range.mpr
    have hlt : (a : ℝ) < n := lt_of_le_of_lt ha hn
    exact_mod_cast hlt

theorem nat_topology_at_codes_iff (a b : Node) :
    G.natTopology (G.orderCode a) (G.orderCode b) ↔ G.Topology a b := by
  constructor
  · rintro ⟨c, d, hc, hd, edge⟩
    have ca : c = a := G.orderCode_injective hc
    have db : d = b := G.orderCode_injective hd
    simpa only [ca, db] using edge
  · intro edge
    exact ⟨a, b, rfl, rfl, edge⟩

/-- All encoded original edges already lie inside the finite code bound. -/
theorem old_nat_topology_eq :
    Old G.natTopology (Fintype.card Node * Fintype.card Node) = G.natTopology := by
  funext i j
  apply propext
  constructor
  · exact fun he => he.2.2
  · intro he
    have bounds := G.natTopology_edge_bounds he
    exact ⟨bounds.1, bounds.2, he⟩

theorem old_encoded_path_iff (a b : Node) :
    Descendant (Old G.natTopology (Fintype.card Node * Fintype.card Node))
      (G.orderCode a) (G.orderCode b) ↔ Reach G.Topology a b := by
  rw [old_nat_topology_eq G]
  exact reach_iff_species_descendant.symm.trans (G.natTopology_path_iff a b)

/-- Acyclicity of the actual gARG supplies the completion hypothesis; its node
identifiers do not need to have a pre-existing birth order. -/
theorem ordered_encoded_prefix :
    OrderedPrefix G.natTopology (Fintype.card Node * Fintype.card Node) :=
  fun _ _ _ _ edge => G.natTopology_edge_order edge

/-- Every actual finite interval gARG has an injective copy, preserving exactly
its raw edges and ancestry paths, inside two connected infinite populations.
Both have real birthdates, finite date sublevels, finite child sets and finite
root sets. One whole population is an inspecies and maximal specieslike; the
other whole population fails IAP.

This proves ambiguity of abstract infinite graph completion. It does not
interpret the genome-node embedding as an organism-owner map. -/
theorem actual_garg_opposite_infinite_completions :
    ∃ (code : Node → Nat) (A B : Graph),
      Function.Injective code ∧
      RealDatedBiosphere A ∧ RealDatedBiosphere B ∧
      NaturalDateBiosphere A ∧ NaturalDateBiosphere B ∧
      FiniteSupport (Root A) ∧ FiniteSupport (Root B) ∧
      WeaklyConnected A Whole ∧ WeaklyConnected B Whole ∧
      (∀ a b, (A (code a) (code b) ↔ G.Topology a b) ∧
        (B (code a) (code b) ↔ G.Topology a b)) ∧
      (∀ a b, (Descendant A (code a) (code b) ↔ Reach G.Topology a b) ∧
        (Descendant B (code a) (code b) ↔ Reach G.Topology a b)) ∧
      Inspecies A Whole ∧ MaximalSpecieslike A Whole ∧ ¬ IAP B Whole := by
  obtain ⟨A, B, hA, hB, rootsA, rootsB, connectedA, connectedB,
    edges, paths, speciesA, maximalA, notIAPB⟩ :=
    finite_history_does_not_determine_species G.natTopology
      (Fintype.card Node * Fintype.card Node) (ordered_encoded_prefix G)
  refine ⟨G.orderCode, A, B, G.orderCode_injective,
    natural_biosphere_has_real_dates hA, natural_biosphere_has_real_dates hB,
    hA, hB, rootsA, rootsB, connectedA, connectedB, ?_, ?_,
    speciesA, maximalA, notIAPB⟩
  · intro a b
    have he := edges (G.orderCode a) (G.orderCode b)
      (G.orderCode_lt_bound a) (G.orderCode_lt_bound b)
    exact ⟨he.1.trans (nat_topology_at_codes_iff G a b),
      he.2.trans (nat_topology_at_codes_iff G a b)⟩
  · intro a b
    have hp := paths (G.orderCode a) (G.orderCode b) (G.orderCode_lt_bound b)
    exact ⟨hp.1.trans (old_encoded_path_iff G a b),
      hp.2.trans (old_encoded_path_iff G a b)⟩

end
end WongAlexander

#print axioms WongAlexander.sample_ancestral_iff
#print axioms WongAlexander.extracted_sample_path_iff
#print axioms WongAlexander.finite_catalog_not_infinite
#print axioms WongAlexander.natural_biosphere_has_real_dates
#print axioms WongAlexander.ordered_encoded_prefix
#print axioms WongAlexander.old_encoded_path_iff
#print axioms WongAlexander.actual_garg_opposite_infinite_completions
#print axioms WongAlexander.extracted_contracted_sample_path_iff
