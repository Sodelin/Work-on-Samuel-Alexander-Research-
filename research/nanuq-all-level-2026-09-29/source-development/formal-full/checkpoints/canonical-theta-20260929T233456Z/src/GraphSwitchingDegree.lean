import GraphSwitching

namespace Nanuq.Source.RootedBinary

variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X)

theorem outDegree_le_two (a : V) : N.graph.outDegree a ≤ 2 := by
  classical
  by_cases hr : a = N.root
  · rw [hr, N.root_degrees.2]
  · by_cases hl : ∃ x, N.leaf x = a
    · obtain ⟨x, rfl⟩ := hl
      rw [(N.leaf_degrees x).2]
      exact Nat.zero_le 2
    · have hnotleaf : ∀ x, N.leaf x ≠ a := by
        intro x hx
        exact hl ⟨x, hx⟩
      rcases N.internal_degrees a hr hnotleaf with ht | hh
      · rw [ht.2]
      · rw [hh.2]
        exact Nat.le_succ 1

namespace Switching
variable {N} (S : N.Switching)

theorem selected_indegree_le_one (a : V) : S.graph.inDegree a ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro e he f hf
  exact S.selected_uniqueIncoming e f
    ((Finset.mem_filter.mp he).2.trans (Finset.mem_filter.mp hf).2.symm)

theorem selected_outdegree_le (a : V) : S.graph.outDegree a ≤ N.graph.outDegree a := by
  classical
  let emb : S.Edge ↪ E := ⟨Subtype.val, Subtype.val_injective⟩
  have hsub :
      (Finset.univ.filter (fun e : S.Edge => S.graph.source e = a)).map emb ⊆
        Finset.univ.filter (fun e : E => N.graph.source e = a) := by
    intro e he
    obtain ⟨f, hf, hfe⟩ := Finset.mem_map.mp he
    rw [← hfe]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hf).2⟩
  have hc := Finset.card_le_card hsub
  simpa only [EdgeGraph.outDegree, Finset.card_map] using hc

/-- Undirected incidence degree is at most three before suppressing degree-two
vertices, including the retained root. Edges are counted with multiplicity. -/
theorem selected_total_degree_le_three (a : V) :
    S.graph.inDegree a + S.graph.outDegree a ≤ 3 :=
  Nat.add_le_add (S.selected_indegree_le_one a)
    ((S.selected_outdegree_le a).trans (N.outDegree_le_two a))

theorem selected_leaf_degrees (x : X) :
    S.graph.inDegree (N.leaf x) = 1 ∧ S.graph.outDegree (N.leaf x) = 0 := by
  constructor
  · apply Nat.le_antisymm (S.selected_indegree_le_one _)
    apply Nat.succ_le_of_lt
    apply Finset.card_pos.mpr
    obtain ⟨e, he⟩ := S.selected_parent (N.leaf_ne_root x)
    exact ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩⟩
  · apply Nat.eq_zero_of_le_zero
    have h := S.selected_outdegree_le (N.leaf x)
    rw [(N.leaf_degrees x).2] at h
    exact h

/-- The switching is a tree of maximum degree three and retains every original
taxon as a degree-one vertex. -/
theorem selected_subcubic_tree :
    S.graph.IsTree ∧
    (∀ a, S.graph.inDegree a + S.graph.outDegree a ≤ 3) ∧
    (∀ x, S.graph.inDegree (N.leaf x) = 1 ∧ S.graph.outDegree (N.leaf x) = 0) :=
  ⟨S.selected_is_tree, S.selected_total_degree_le_three, S.selected_leaf_degrees⟩

end Switching
end Nanuq.Source.RootedBinary

#print axioms Nanuq.Source.RootedBinary.Switching.selected_subcubic_tree
