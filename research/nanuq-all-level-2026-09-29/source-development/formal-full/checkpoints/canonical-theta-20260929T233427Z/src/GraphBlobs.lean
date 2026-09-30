import GraphCuts

namespace Nanuq.Source
namespace EdgeGraph

variable {V E : Type*} (G : EdgeGraph V E)

/-- Actual bridge edges, with their original edge identities. -/
def BridgeEdge := {e : E // G.IsBridge e}

/-- Contract the actual components after all bridges have been deleted. -/
def bridgeQuotient : EdgeGraph G.Blob G.BridgeEdge where
  source e := G.blobOf (G.source e.val)
  target e := G.blobOf (G.target e.val)

theorem sameBlob_avoids_bridge {e : E} (he : G.IsBridge e) {a b : V}
    (h : G.SameBlob a b) : G.ReachWithout e a b := by
  apply G.ureach_mono (keep := fun f => ¬ G.IsBridge f) _ h
  intro f hf hfe
  subst f
  exact hf he

/-- Lift a quotient walk avoiding one retained bridge to the original graph.
At each quotient vertex the connecting detour uses only nonbridge edges. -/
theorem quotient_reach_lifts_without (e : G.BridgeEdge) {q r : G.Blob}
    (h : G.bridgeQuotient.ReachWithout e q r) :
    ∀ {a b : V}, G.blobOf a = q → G.blobOf b = r → G.ReachWithout e.val a b := by
  induction h with
  | refl =>
      intro a b ha hb
      exact G.sameBlob_avoids_bridge e.property (Quotient.exact (ha.trans hb.symm))
  | @tail r s _ hstep ih =>
      intro a b ha hb
      obtain ⟨f, hfe, hinc⟩ := hstep
      have hfval : f.val ≠ e.val := fun hval => hfe (Subtype.ext hval)
      rcases hinc with ⟨hs, ht⟩ | ⟨hs, ht⟩
      · have hprev := ih ha hs
        have hnext : G.ReachWithout e.val (G.target f.val) b :=
          G.sameBlob_avoids_bridge e.property (Quotient.exact (ht.trans hb.symm))
        exact hprev.trans ((G.ureach_single
          ⟨f.val, hfval, G.inc_source_target f.val⟩).trans hnext)
      · have hprev := ih ha ht
        have hnext : G.ReachWithout e.val (G.source f.val) b :=
          G.sameBlob_avoids_bridge e.property (Quotient.exact (hs.trans hb.symm))
        exact hprev.trans ((G.ureach_single
          ⟨f.val, hfval, G.inc_symm (G.inc_source_target f.val)⟩).trans hnext)

/-- No bridge becomes part of a cycle after the actual blobs are contracted. -/
theorem quotient_edge_is_bridge (e : G.BridgeEdge) : G.bridgeQuotient.IsBridge e := by
  intro h
  exact e.property (G.quotient_reach_lifts_without e h rfl rfl)

theorem reach_projects_to_blobs {a b : V}
    (h : G.UReach (fun _ => True) a b) :
    G.bridgeQuotient.UReach (fun _ => True) (G.blobOf a) (G.blobOf b) := by
  classical
  induction h with
  | refl => exact .refl
  | @tail b c _ hstep ih =>
      obtain ⟨e, _, hinc⟩ := hstep
      by_cases he : G.IsBridge e
      · apply ih.tail
        refine ⟨⟨e, he⟩, trivial, ?_⟩
        rcases hinc with ⟨hs, ht⟩ | ⟨hs, ht⟩
        · exact Or.inl ⟨congrArg G.blobOf hs, congrArg G.blobOf ht⟩
        · exact Or.inr ⟨congrArg G.blobOf hs, congrArg G.blobOf ht⟩
      · have hbc : G.blobOf b = G.blobOf c := by
          apply Quotient.sound
          exact G.ureach_single ⟨e, he, hinc⟩
        rw [← hbc]
        exact ih

/-- The bridge characterization of a nonempty edge-indexed tree: it is connected
and every individual edge disconnects its endpoints on deletion. -/
def IsTree : Prop :=
  Nonempty V ∧ (∀ a b, G.UReach (fun _ => True) a b) ∧ ∀ e, G.IsBridge e

theorem quotient_isTree (hne : Nonempty V)
    (hconn : ∀ a b, G.UReach (fun _ => True) a b) : G.bridgeQuotient.IsTree := by
  obtain ⟨v⟩ := hne
  refine ⟨⟨G.blobOf v⟩, ?_, G.quotient_edge_is_bridge⟩
  intro q r
  refine Quotient.inductionOn₂ q r ?_
  intro a b
  exact G.reach_projects_to_blobs (hconn a b)

end EdgeGraph

namespace RootedBinary
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X)

theorem blob_quotient_is_tree : N.graph.bridgeQuotient.IsTree :=
  N.graph.quotient_isTree ⟨N.root⟩ N.underlying_connected

end RootedBinary
end Nanuq.Source

#print axioms Nanuq.Source.EdgeGraph.quotient_reach_lifts_without
#print axioms Nanuq.Source.EdgeGraph.quotient_edge_is_bridge
#print axioms Nanuq.Source.RootedBinary.blob_quotient_is_tree
