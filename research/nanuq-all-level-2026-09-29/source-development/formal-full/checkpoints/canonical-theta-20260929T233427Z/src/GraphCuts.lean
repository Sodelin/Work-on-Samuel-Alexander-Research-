import GraphLeaves

namespace Nanuq.Source
namespace EdgeGraph

variable {V E : Type*} (G : EdgeGraph V E)

/-- Deleting one edge leaves at most two relevant sides of a connected graph. -/
theorem edge_side_cover (e : E) {a : V}
    (h : G.UReach (fun _ => True) (G.source e) a) :
    G.ReachWithout e (G.source e) a ∨ G.ReachWithout e (G.target e) a := by
  induction h with
  | refl => exact Or.inl (.refl)
  | @tail b c _ hstep ih =>
      obtain ⟨f, _, hinc⟩ := hstep
      by_cases hfe : f = e
      · subst f
        rcases hinc with ⟨hs, ht⟩ | ⟨hs, ht⟩
        · apply Or.inr
          rw [← ht]
          exact .refl
        · apply Or.inl
          rw [← hs]
          exact .refl
      · rcases ih with hb | hb
        · exact Or.inl (hb.tail ⟨f, hfe, hinc⟩)
        · exact Or.inr (hb.tail ⟨f, hfe, hinc⟩)

theorem bridge_sides_disjoint {e : E} (he : G.IsBridge e) {a : V}
    (hs : G.ReachWithout e (G.source e) a)
    (ht : G.ReachWithout e (G.target e) a) : False :=
  he (hs.trans (G.ureach_symm ht))

/-- The target side of a directed bridge is closed under directed edges. -/
theorem bridge_target_forward_closed {e : E} (he : G.IsBridge e)
    {a b : V} (hab : G.DStep a b)
    (ha : G.ReachWithout e (G.target e) a) :
    G.ReachWithout e (G.target e) b := by
  obtain ⟨f, hs, ht⟩ := hab
  have hfe : f ≠ e := by
    intro hfe
    subst f
    apply he
    rw [← hs] at ha
    exact G.ureach_symm ha
  exact ha.tail ⟨f, hfe, Or.inl ⟨hs, ht⟩⟩

/-- A directed path whose endpoint is not below an edge cannot use that edge. -/
theorem dreach_without_of_no_return (e : E) {a b : V} (hab : G.DReach a b) :
    (¬ G.DReach (G.target e) b) → G.ReachWithout e a b := by
  induction hab with
  | refl => intro _; exact .refl
  | @tail b c _ hstep ih =>
      intro hno
      have hp := ih (fun h => hno (h.tail hstep))
      obtain ⟨f, hs, ht⟩ := hstep
      have hfe : f ≠ e := by
        intro hfe
        subst f
        apply hno
        rw [← ht]
        exact .refl
      exact hp.tail ⟨f, hfe, Or.inl ⟨hs, ht⟩⟩

theorem avoid_target_reach_without (e : E) {a b : V}
    (h : G.AvoidReach (G.target e) a b) : G.ReachWithout e a b := by
  rcases h with ⟨ha, hb, hw⟩
  clear ha hb
  induction hw with
  | refl => exact .refl
  | tail _ hstep ih =>
      obtain ⟨f, hs, ht⟩ := hstep.1
      have hfe : f ≠ e := by
        intro hfe
        subst f
        exact hstep.2.2 ht.symm
      exact ih.tail ⟨f, hfe, Or.inl ⟨hs, ht⟩⟩

end EdgeGraph

namespace RootedBinary
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X)

theorem edge_target_ne_root (e : E) : N.graph.target e ≠ N.root := by
  intro ht
  apply N.acyclic N.root
  exact Relation.TransGen.tail' (N.rooted (N.graph.source e)) ⟨e, rfl, ht⟩

theorem root_on_source_side (e : E) :
    N.graph.ReachWithout e (N.graph.source e) N.root := by
  apply N.graph.ureach_symm
  apply N.graph.dreach_without_of_no_return e (N.rooted (N.graph.source e))
  intro hreturn
  exact N.acyclic (N.graph.source e)
    (Relation.TransGen.head' ⟨e, rfl, rfl⟩ hreturn)

theorem bridge_target_side_contains_taxon {e : E} (he : N.graph.IsBridge e) :
    ∃ x, N.graph.ReachWithout e (N.graph.target e) (N.leaf x) := by
  apply N.forward_closed_contains_leaf
    (P := fun a => N.graph.ReachWithout e (N.graph.target e) a)
  · intro a b hab ha
    exact N.graph.bridge_target_forward_closed he hab ha
  · exact Relation.ReflTransGen.refl (a := N.graph.target e)

/-- LSA excludes an empty rootward side of every bridge. -/
theorem bridge_source_side_contains_taxon (e : E) :
    ∃ x, N.graph.ReachWithout e (N.graph.source e) (N.leaf x) := by
  obtain ⟨x, hx⟩ := N.exists_leaf_avoiding_of_ne_root (N.edge_target_ne_root e)
  exact ⟨x, (N.root_on_source_side e).trans (N.graph.avoid_target_reach_without e hx)⟩

/-- Both sides of each actual cut edge contain labeled taxa. -/
theorem bridge_both_sides_contain_taxa {e : E} (he : N.graph.IsBridge e) :
    (∃ x, N.graph.ReachWithout e (N.graph.source e) (N.leaf x)) ∧
    (∃ x, N.graph.ReachWithout e (N.graph.target e) (N.leaf x)) :=
  ⟨N.bridge_source_side_contains_taxon e, N.bridge_target_side_contains_taxon he⟩

end RootedBinary
end Nanuq.Source

#print axioms Nanuq.Source.EdgeGraph.edge_side_cover
#print axioms Nanuq.Source.EdgeGraph.bridge_sides_disjoint
#print axioms Nanuq.Source.RootedBinary.bridge_both_sides_contain_taxa
