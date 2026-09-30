import GraphTreePorts

namespace Nanuq.Source.EdgeGraph

variable {V E : Type*} [Fintype E] [DecidableEq V] (G : EdgeGraph V E)

theorem port_outgoing_desc (hu : G.UniqueIncoming) (ha : G.Acyclic)
    {v a : V} {e : E} (hs : G.source e = v) (h : G.IsPortTo v a e) :
    G.DReach (G.target e) a := by
  rcases h with ⟨_, h⟩ | ⟨ht, _⟩
  · exact (G.target_side_iff_descendant hu ha e a).mp h
  · exact False.elim (G.acyclic_no_loop ha e (hs.trans ht.symm))

theorem port_incoming_not_desc (hu : G.UniqueIncoming) (ha : G.Acyclic)
    {v a : V} {e : E} (ht : G.target e = v) (h : G.IsPortTo v a e) :
    ¬ G.DReach v a := by
  rcases h with ⟨hs, _⟩ | ⟨_, h⟩
  · exact False.elim (G.acyclic_no_loop ha e (hs.trans ht.symm))
  · intro hd
    have hother := (G.target_side_iff_descendant hu ha e a).mpr (by rw [ht]; exact hd)
    exact G.bridge_sides_disjoint (G.uniqueIncoming_all_bridges hu ha e) h hother

end Nanuq.Source.EdgeGraph
