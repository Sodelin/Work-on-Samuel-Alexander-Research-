import GraphSwitchingDegree
import GraphGalls

namespace Nanuq.Source.RootedBinary.Switching

variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable {N : RootedBinary V E X} (S : N.Switching)

theorem reach_without_original (e : S.Edge) {a b : V}
    (h : S.graph.ReachWithout e a b) : N.graph.ReachWithout e.val a b := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih =>
      obtain ⟨f, hfe, hinc⟩ := hstep
      have hv : f.val ≠ e.val := fun heq => hfe (Subtype.ext heq)
      exact ih.tail ⟨f.val, hv, hinc⟩

/-- A retained original bridge has exactly its original source component. -/
theorem selected_source_side_iff (e : S.Edge) (he : N.graph.IsBridge e.val) (a : V) :
    S.graph.ReachWithout e (S.graph.source e) a ↔
      N.graph.ReachWithout e.val (N.graph.source e.val) a := by
  constructor
  · exact S.reach_without_original e
  · intro ha
    rcases S.graph.edge_side_cover e (S.selected_connected (S.graph.source e) a) with hs | ht
    · exact hs
    · exact False.elim (N.graph.bridge_sides_disjoint he ha (S.reach_without_original e ht))

/-- A retained original bridge has exactly its original target component. -/
theorem selected_target_side_iff (e : S.Edge) (he : N.graph.IsBridge e.val) (a : V) :
    S.graph.ReachWithout e (S.graph.target e) a ↔
      N.graph.ReachWithout e.val (N.graph.target e.val) a := by
  constructor
  · exact S.reach_without_original e
  · intro ha
    rcases S.graph.edge_side_cover e (S.selected_connected (S.graph.source e) a) with hs | ht
    · exact False.elim (N.graph.bridge_sides_disjoint he (S.reach_without_original e hs) ha)
    · exact ht

theorem galled_bridge_retained (hg : N.graph.GalledDetour) {e : E}
    (he : N.graph.IsBridge e) : S.keep e :=
  S.ordinary e (N.graph.galled_bridge_not_hybrid_target hg he)

/-- Every raw bridge split, hence every separation of taxa made by that bridge,
is unchanged in every actual switching. -/
theorem preserves_bridge_sides (hg : N.graph.GalledDetour) (e : E)
    (he : N.graph.IsBridge e) :
    ∃ f : S.Edge, f.val = e ∧ ∀ a,
      (S.graph.ReachWithout f (S.graph.source f) a ↔
        N.graph.ReachWithout e (N.graph.source e) a) ∧
      (S.graph.ReachWithout f (S.graph.target f) a ↔
        N.graph.ReachWithout e (N.graph.target e) a) := by
  let f : S.Edge := ⟨e, S.galled_bridge_retained hg he⟩
  refine ⟨f, rfl, ?_⟩
  intro a
  exact ⟨S.selected_source_side_iff f he a, S.selected_target_side_iff f he a⟩

end Nanuq.Source.RootedBinary.Switching

#print axioms Nanuq.Source.RootedBinary.Switching.preserves_bridge_sides
