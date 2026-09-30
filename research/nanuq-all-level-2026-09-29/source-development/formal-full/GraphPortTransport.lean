import GraphTreePorts
import GraphBridgeSplits

namespace Nanuq.Source.EdgeGraph

variable {V E : Type*} [Fintype E] [DecidableEq V] (G : EdgeGraph V E)

theorem crossing_bridge_endpoints_inc {e : E} (he : G.IsBridge e) {s t a b : V}
    (hi : G.Inc e s t) {keep : E → Prop} (hwalk : G.UReach keep a b)
    (ha : G.ReachWithout e s a) (hb : G.ReachWithout e t b) :
    G.UReach keep a s ∧ G.UReach keep a t := by
  rcases hi with ⟨hs, ht⟩ | ⟨hs, ht⟩
  · have h := G.crossing_bridge_endpoints he hwalk
      (by rw [hs]; exact ha) (by rw [ht]; exact hb)
    simpa only [hs, ht] using h
  · have h := G.crossing_bridge_endpoints he (G.ureach_symm hwalk)
      (by rw [hs]; exact hb) (by rw [ht]; exact ha)
    constructor
    · exact hwalk.trans (by simpa only [UReach, ht] using h.2)
    · exact hwalk.trans (by simpa only [UReach, hs] using h.1)

/-- From one side of a bridge, the direction toward any vertex on the opposite
side also points toward that bridge's opposite endpoint. -/
theorem port_across_bridge {e g : E} (he : G.IsBridge e) {s t v a : V}
    (hi : G.Inc e s t) (hv : G.ReachWithout e s v) (ha : G.ReachWithout e t a)
    (hp : G.IsPortTo v a g) : G.IsPortTo v t g := by
  classical
  by_cases hge : g = e
  · subst g
    rcases hi with ⟨hes, het⟩ | ⟨hes, het⟩ <;>
      rcases hp with ⟨hgs, _⟩ | ⟨hgt, _⟩
    · exact Or.inl ⟨hgs, by rw [het]; exact .refl⟩
    · apply False.elim
      apply he
      rw [hes, hgt]
      exact hv
    · apply False.elim
      apply he
      apply G.ureach_symm
      rw [het, hgs]
      exact hv
    · exact Or.inr ⟨hgt, by rw [hes]; exact .refl⟩
  · rcases hp with ⟨hgs, hp⟩ | ⟨hgt, hp⟩
    · have hs : G.ReachWithout e s (G.target g) :=
        hv.tail ⟨g, hge, Or.inl ⟨hgs, rfl⟩⟩
      have hc := G.crossing_bridge_endpoints_inc he hi hp hs ha
      exact Or.inl ⟨hgs, hc.2⟩
    · have hs : G.ReachWithout e s (G.source g) :=
        hv.tail ⟨g, hge, Or.inr ⟨rfl, hgt⟩⟩
      have hc := G.crossing_bridge_endpoints_inc he hi hp hs ha
      exact Or.inr ⟨hgt, hc.2⟩

/-- Two destinations beyond the same separating bridge have the same port
direction at a vertex on the other side. -/
theorem ports_equal_across_bridge (hu : G.UniqueIncoming) (hac : G.Acyclic)
    {e g h : E} (he : G.IsBridge e) {s t v a b : V} (hi : G.Inc e s t)
    (hv : G.ReachWithout e s v) (ha : G.ReachWithout e t a)
    (hb : G.ReachWithout e t b) (hga : G.IsPortTo v a g) (hhb : G.IsPortTo v b h) :
    g = h :=
  G.port_unique hu hac (G.port_across_bridge he hi hv ha hga)
    (G.port_across_bridge he hi hv hb hhb)

end Nanuq.Source.EdgeGraph

#print axioms Nanuq.Source.EdgeGraph.ports_equal_across_bridge
