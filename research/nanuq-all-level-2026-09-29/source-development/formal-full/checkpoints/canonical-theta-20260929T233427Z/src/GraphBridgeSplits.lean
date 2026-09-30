import GraphCuts

namespace Nanuq.Source.EdgeGraph

variable {V E : Type*} (G : EdgeGraph V E)

/-- A walk either avoids an edge or reaches both endpoints of an occurrence
of that edge using only edges allowed in the original walk. -/
theorem ureach_avoids_or_hits (f : E) {keep : E → Prop} {a b : V}
    (h : G.UReach keep a b) :
    G.ReachWithout f a b ∨
      (G.UReach keep a (G.source f) ∧ G.UReach keep a (G.target f)) := by
  classical
  induction h with
  | refl => exact Or.inl (.refl)
  | @tail b c hp hstep ih =>
      obtain ⟨g, hg, hinc⟩ := hstep
      by_cases hgf : g = f
      · subst g
        have hc := hp.tail ⟨f, hg, hinc⟩
        rcases hinc with ⟨hs, ht⟩ | ⟨hs, ht⟩
        · rw [← hs] at hp
          rw [← ht] at hc
          exact Or.inr ⟨hp, hc⟩
        · rw [← hs] at hc
          rw [← ht] at hp
          exact Or.inr ⟨hc, hp⟩
      · rcases ih with hav | hhit
        · exact Or.inl (hav.tail ⟨g, hgf, hinc⟩)
        · exact Or.inr hhit

/-- A walk connecting opposite sides of a bridge reaches its two endpoints. -/
theorem crossing_bridge_endpoints {f : E} (hf : G.IsBridge f)
    {keep : E → Prop} {a b : V} (h : G.UReach keep a b)
    (ha : G.ReachWithout f (G.source f) a)
    (hb : G.ReachWithout f (G.target f) b) :
    G.UReach keep a (G.source f) ∧ G.UReach keep a (G.target f) := by
  rcases G.ureach_avoids_or_hits f h with hav | hhit
  · exact False.elim (hf (ha.trans (hav.trans (G.ureach_symm hb))))
  · exact hhit

/-- Two actual bridge splits cannot cross as `ab|cd` and `ac|bd`.
The result holds for arbitrary edge-indexed graphs; no tree is assumed. -/
theorem bridge_splits_compatible {e f : E} (he : G.IsBridge e) (hf : G.IsBridge f)
    {a b c d : V}
    (hea : G.ReachWithout e (G.source e) a)
    (heb : G.ReachWithout e (G.source e) b)
    (hec : G.ReachWithout e (G.target e) c)
    (hed : G.ReachWithout e (G.target e) d)
    (hfa : G.ReachWithout f (G.source f) a)
    (hfc : G.ReachWithout f (G.source f) c)
    (hfb : G.ReachWithout f (G.target f) b)
    (hfd : G.ReachWithout f (G.target f) d) : False := by
  have hab := (G.ureach_symm hea).trans heb
  have hcd := (G.ureach_symm hec).trans hed
  have hleft := (G.crossing_bridge_endpoints hf hab hfa hfb).1
  have hright := (G.crossing_bridge_endpoints hf hcd hfc hfd).1
  exact G.bridge_sides_disjoint he (hea.trans hleft) (hec.trans hright)

end Nanuq.Source.EdgeGraph

#print axioms Nanuq.Source.EdgeGraph.bridge_splits_compatible
