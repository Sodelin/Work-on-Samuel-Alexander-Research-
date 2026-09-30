import SourceNetwork

namespace Nanuq.Source
namespace EdgeGraph

variable {V E : Type*} [Fintype E] [DecidableEq V] (G : EdgeGraph V E)

/-- The ordinary-edge detour between the two parents of each hybrid.
Together with the two incoming edges, a simple detour is the source gall.
Equivalence of this reachability formulation to a simple-cycle formulation
is an explicit walk-simplification obligation, not a canonical-shape premise.
-/
def GalledDetour : Prop :=
  ∀ h, G.IsHybrid h → ∀ e f,
    e ≠ f → G.target e = h → G.target f = h →
    G.UReach (fun d => ¬ G.IsHybrid (G.target d) ∧ G.source d ≠ h ∧ G.target d ≠ h)
      (G.source e) (G.source f)

theorem hybrid_has_partner {h : V} (hh : G.IsHybrid h) (e : E) :
    ∃ f, G.target f = h ∧ f ≠ e := by
  classical
  have hc : 1 < (Finset.univ.filter (fun d => G.target d = h)).card := by
    change 1 < G.inDegree h
    rw [hh.1]
    exact Nat.lt_succ_self 1
  obtain ⟨f, hf, hne⟩ := Finset.exists_mem_ne hc e
  exact ⟨f, (Finset.mem_filter.mp hf).2, hne⟩

theorem galled_hybrid_edge_not_bridge (hg : G.GalledDetour) {e : E}
    (hh : G.IsHybrid (G.target e)) : ¬ G.IsBridge e := by
  obtain ⟨f, hft, hne⟩ := G.hybrid_has_partner hh e
  have hd := hg (G.target e) hh e f hne.symm rfl hft
  apply G.not_bridge_of_detour
  have hp : G.ReachWithout e (G.source e) (G.source f) := by
    apply G.ureach_mono _ hd
    intro d hd hde
    subst d
    exact hd.1 hh
  exact hp.trans (G.ureach_single ⟨f, hne, Or.inl ⟨rfl, hft⟩⟩)

theorem galled_bridge_not_hybrid_target (hg : G.GalledDetour) {e : E}
    (he : G.IsBridge e) : ¬ G.IsHybrid (G.target e) := by
  intro hh
  exact G.galled_hybrid_edge_not_bridge hg hh he

theorem galled_hybrid_parent_sameBlob (hg : G.GalledDetour) {e : E}
    (hh : G.IsHybrid (G.target e)) :
    G.SameBlob (G.source e) (G.target e) :=
  G.nonbridge_sameBlob (G.galled_hybrid_edge_not_bridge hg hh)

variable [Fintype V]

noncomputable def hybridsInBlob (a : V) : Finset V := by
  classical
  exact Finset.univ.filter (fun h => G.IsHybrid h ∧ G.SameBlob h a)

/-- Level is measured in actual bridge-deletion components of the raw graph. -/
def LevelAtMost (k : Nat) : Prop := ∀ a, (G.hybridsInBlob a).card ≤ k

end EdgeGraph
end Nanuq.Source

#print axioms Nanuq.Source.EdgeGraph.hybrid_has_partner
#print axioms Nanuq.Source.EdgeGraph.galled_hybrid_edge_not_bridge
#print axioms Nanuq.Source.EdgeGraph.galled_bridge_not_hybrid_target
