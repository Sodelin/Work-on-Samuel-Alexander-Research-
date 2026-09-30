import GraphCuts

namespace Nanuq.Source.RootedBinary

variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X)

/-- Taxa in the actual component of `a` after deleting one edge ID. -/
noncomputable def sideTaxa (e : E) (a : V) : Finset X := by
  classical
  exact Finset.univ.filter (fun x => N.graph.ReachWithout e a (N.leaf x))

@[simp] theorem mem_sideTaxa (e : E) (a : V) (x : X) :
    x ∈ N.sideTaxa e a ↔ N.graph.ReachWithout e a (N.leaf x) := by
  classical
  simp [sideTaxa]

theorem source_side_mass_positive (e : E) :
    0 < (N.sideTaxa e (N.graph.source e)).card := by
  obtain ⟨x, hx⟩ := N.bridge_source_side_contains_taxon e
  exact Finset.card_pos.mpr ⟨x, (N.mem_sideTaxa e _ x).mpr hx⟩

theorem target_side_mass_positive {e : E} (he : N.graph.IsBridge e) :
    0 < (N.sideTaxa e (N.graph.target e)).card := by
  obtain ⟨x, hx⟩ := N.bridge_target_side_contains_taxon he
  exact Finset.card_pos.mpr ⟨x, (N.mem_sideTaxa e _ x).mpr hx⟩

theorem bridge_taxa_disjoint {e : E} (he : N.graph.IsBridge e) :
    Disjoint (N.sideTaxa e (N.graph.source e))
      (N.sideTaxa e (N.graph.target e)) := by
  classical
  apply Finset.disjoint_left.mpr
  intro x hs ht
  exact N.graph.bridge_sides_disjoint he
    ((N.mem_sideTaxa e _ x).mp hs) ((N.mem_sideTaxa e _ x).mp ht)

theorem edge_taxa_cover [DecidableEq X] (e : E) :
    N.sideTaxa e (N.graph.source e) ∪ N.sideTaxa e (N.graph.target e) = Finset.univ := by
  classical
  apply Finset.ext
  intro x
  simp only [Finset.mem_union, mem_sideTaxa, Finset.mem_univ, iff_true]
  exact N.graph.edge_side_cover e (N.underlying_connected _ _)

theorem bridge_mass_sum {e : E} (he : N.graph.IsBridge e) :
    (N.sideTaxa e (N.graph.source e)).card +
      (N.sideTaxa e (N.graph.target e)).card = Fintype.card X := by
  classical
  rw [← Finset.card_union_of_disjoint (N.bridge_taxa_disjoint he), N.edge_taxa_cover]
  exact Finset.card_univ

/-- The two sides give an actual nonempty bipartition of the labeled taxa. -/
theorem bridge_port_masses {e : E} (he : N.graph.IsBridge e) :
    0 < (N.sideTaxa e (N.graph.source e)).card ∧
    0 < (N.sideTaxa e (N.graph.target e)).card ∧
    (N.sideTaxa e (N.graph.source e)).card +
      (N.sideTaxa e (N.graph.target e)).card = Fintype.card X :=
  ⟨N.source_side_mass_positive e, N.target_side_mass_positive he, N.bridge_mass_sum he⟩

end Nanuq.Source.RootedBinary

#print axioms Nanuq.Source.RootedBinary.bridge_port_masses
#print axioms Nanuq.Source.RootedBinary.bridge_taxa_disjoint
