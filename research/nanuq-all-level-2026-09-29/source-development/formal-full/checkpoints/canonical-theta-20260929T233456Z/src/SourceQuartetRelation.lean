import GraphBridgeSplits
import QuartetSemantics

namespace Nanuq.Source.EdgeGraph

open Nanuq.Quartet

variable {V E : Type*} (G : EdgeGraph V E)

/-- An oriented actual edge-deletion split on four vertices. -/
def OrientedQuartet (e : E) (a b c d : V) : Prop :=
  G.ReachWithout e (G.source e) a ∧ G.ReachWithout e (G.source e) b ∧
  G.ReachWithout e (G.target e) c ∧ G.ReachWithout e (G.target e) d

/-- The edge-cut quartet relation, independent of the arbitrary edge orientation. -/
def HasQuartet (a b c d : V) : Prop :=
  ∃ e, G.IsBridge e ∧ (G.OrientedQuartet e a b c d ∨ G.OrientedQuartet e c d a b)

theorem hasQuartet_swap_right {a b c d : V} (h : G.HasQuartet a b c d) :
    G.HasQuartet a b d c := by
  obtain ⟨e, he, h | h⟩ := h
  · exact ⟨e, he, Or.inl ⟨h.1, h.2.1, h.2.2.2, h.2.2.1⟩⟩
  · exact ⟨e, he, Or.inr ⟨h.2.1, h.1, h.2.2.1, h.2.2.2⟩⟩

theorem hasQuartet_incompatible {a b c d : V}
    (h : G.HasQuartet a b c d) (k : G.HasQuartet a c b d) : False := by
  obtain ⟨e, he, h⟩ := h
  obtain ⟨f, hf, k⟩ := k
  rcases h with h | h <;> rcases k with k | k
  · exact G.bridge_splits_compatible he hf
      h.1 h.2.1 h.2.2.1 h.2.2.2 k.1 k.2.1 k.2.2.1 k.2.2.2
  · exact G.bridge_splits_compatible he hf
      h.2.1 h.1 h.2.2.2 h.2.2.1 k.1 k.2.1 k.2.2.1 k.2.2.2
  · exact G.bridge_splits_compatible he hf
      h.1 h.2.1 h.2.2.1 h.2.2.2 k.2.1 k.1 k.2.2.2 k.2.2.1
  · exact G.bridge_splits_compatible he hf
      h.2.1 h.1 h.2.2.2 h.2.2.1 k.2.1 k.1 k.2.2.2 k.2.2.1

/-- A concrete edge-cut meaning for the three quartet resolution constructors. -/
def Resolves (v : Fin 4 → V) : Resolution → Prop
  | .xy_zw => G.HasQuartet (v 0) (v 1) (v 2) (v 3)
  | .xz_yw => G.HasQuartet (v 0) (v 2) (v 1) (v 3)
  | .xw_yz => G.HasQuartet (v 0) (v 3) (v 1) (v 2)

theorem resolution_unique {v : Fin 4 → V} {q r : Resolution}
    (hq : G.Resolves v q) (hr : G.Resolves v r) : q = r := by
  cases q <;> cases r
  · rfl
  · exact False.elim (G.hasQuartet_incompatible hq hr)
  · exact False.elim (G.hasQuartet_incompatible (G.hasQuartet_swap_right hq) hr)
  · exact False.elim (G.hasQuartet_incompatible hr hq)
  · rfl
  · exact False.elim (G.hasQuartet_incompatible
      (G.hasQuartet_swap_right hq) (G.hasQuartet_swap_right hr))
  · exact False.elim (G.hasQuartet_incompatible (G.hasQuartet_swap_right hr) hq)
  · exact False.elim (G.hasQuartet_incompatible
      (G.hasQuartet_swap_right hr) (G.hasQuartet_swap_right hq))
  · rfl

end Nanuq.Source.EdgeGraph

#print axioms Nanuq.Source.EdgeGraph.resolution_unique
