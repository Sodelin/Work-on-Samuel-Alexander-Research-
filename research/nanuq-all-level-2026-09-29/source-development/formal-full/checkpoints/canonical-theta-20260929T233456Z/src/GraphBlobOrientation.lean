import GraphBlobs
import GraphBridgeSplits
import GraphSwitching

namespace Nanuq.Source
namespace EdgeGraph

variable {V E : Type*} (G : EdgeGraph V E)

noncomputable instance blobDecidableEq : DecidableEq G.Blob := Classical.decEq _

noncomputable instance blobFintype [Fintype V] : Fintype G.Blob := by
  classical
  apply Fintype.ofSurjective G.blobOf
  intro q
  exact Quotient.inductionOn q (fun a => ⟨a, rfl⟩)

noncomputable instance bridgeEdgeFintype [Fintype E] : Fintype G.BridgeEdge := by
  classical
  unfold BridgeEdge
  infer_instance

theorem all_bridges_acyclic (hb : ∀ e, G.IsBridge e) : G.Acyclic := by
  intro a hcycle
  obtain ⟨b, ⟨e, hs, ht⟩, hreturn⟩ := Relation.TransGen.head'_iff.mp hcycle
  have hret : G.DReach (G.target e) (G.source e) := by
    rw [hs, ht]
    exact hreturn
  have hside : G.ReachWithout e (G.target e) (G.source e) :=
    G.dreach_preserves
      (P := fun v => G.ReachWithout e (G.target e) v)
      (fun _ _ huv hv => G.bridge_target_forward_closed (hb e) huv hv) hret (.refl)
  exact hb e (G.ureach_symm hside)

/-- If every edge is a bridge and the root lies on every source side, there
cannot be two different incoming edges at one vertex. -/
theorem root_source_sides_uniqueIncoming (hb : ∀ e, G.IsBridge e) (root : V)
    (hr : ∀ e, G.ReachWithout e (G.source e) root) : G.UniqueIncoming := by
  classical
  intro e f htarget
  by_contra hne
  have heother : G.ReachWithout e (G.target e) (G.source f) :=
    G.ureach_single ⟨f, Ne.symm hne, Or.inr ⟨rfl, htarget.symm⟩⟩
  have hc := G.crossing_bridge_endpoints (hb e) (G.ureach_symm (hr f)) (hr e) heother
  have hlast := hc.2
  rw [htarget] at hlast
  exact hb f ((hr f).trans hlast)

/-- Edge-avoiding paths project through actual blob contraction. -/
theorem reach_projects_without (e : G.BridgeEdge) {a b : V}
    (h : G.ReachWithout e.val a b) :
    G.bridgeQuotient.ReachWithout e (G.blobOf a) (G.blobOf b) := by
  classical
  induction h with
  | refl => exact .refl
  | @tail b c _ hstep ih =>
      obtain ⟨f, hfe, hinc⟩ := hstep
      by_cases hf : G.IsBridge f
      · apply ih.tail
        refine ⟨⟨f, hf⟩, ?_, ?_⟩
        · intro heq
          exact hfe (congrArg Subtype.val heq)
        · rcases hinc with ⟨hs, ht⟩ | ⟨hs, ht⟩
          · exact Or.inl ⟨congrArg G.blobOf hs, congrArg G.blobOf ht⟩
          · exact Or.inr ⟨congrArg G.blobOf hs, congrArg G.blobOf ht⟩
      · have hbc : G.blobOf b = G.blobOf c := by
          apply Quotient.sound
          exact G.ureach_single ⟨f, hf, hinc⟩
        rw [← hbc]
        exact ih

theorem dreach_projects_to_blobs {a b : V} (h : G.DReach a b) :
    G.bridgeQuotient.DReach (G.blobOf a) (G.blobOf b) := by
  classical
  induction h with
  | refl => exact .refl
  | @tail b c _ hstep ih =>
      obtain ⟨e, hs, ht⟩ := hstep
      by_cases he : G.IsBridge e
      · exact ih.tail ⟨⟨e, he⟩, congrArg G.blobOf hs, congrArg G.blobOf ht⟩
      · have hbc : G.blobOf b = G.blobOf c := by
          rw [← hs, ← ht]
          exact Quotient.sound (G.nonbridge_sameBlob he)
        rw [← hbc]
        exact ih

end EdgeGraph

namespace RootedBinary
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X)

theorem blob_quotient_rooted (b : N.graph.Blob) :
    N.graph.bridgeQuotient.DReach (N.graph.blobOf N.root) b := by
  refine Quotient.inductionOn b ?_
  intro a
  exact N.graph.dreach_projects_to_blobs (N.rooted a)

theorem blob_root_on_source_side (e : N.graph.BridgeEdge) :
    N.graph.bridgeQuotient.ReachWithout e (N.graph.bridgeQuotient.source e)
      (N.graph.blobOf N.root) :=
  N.graph.reach_projects_without e (N.root_on_source_side e.val)

theorem blob_quotient_uniqueIncoming : N.graph.bridgeQuotient.UniqueIncoming :=
  N.graph.bridgeQuotient.root_source_sides_uniqueIncoming N.graph.quotient_edge_is_bridge
    (N.graph.blobOf N.root) N.blob_root_on_source_side

theorem blob_quotient_acyclic : N.graph.bridgeQuotient.Acyclic :=
  N.graph.bridgeQuotient.all_bridges_acyclic N.graph.quotient_edge_is_bridge

/-- The actual finite quotient is oriented away from the root blob, with a
unique incoming edge at each nonroot blob. The properties are derived. -/
theorem blob_arborescence :
    N.graph.bridgeQuotient.IsTree ∧ N.graph.bridgeQuotient.Acyclic ∧
    N.graph.bridgeQuotient.UniqueIncoming ∧
    ∀ b, N.graph.bridgeQuotient.DReach (N.graph.blobOf N.root) b :=
  ⟨N.blob_quotient_is_tree, N.blob_quotient_acyclic,
    N.blob_quotient_uniqueIncoming, N.blob_quotient_rooted⟩

end RootedBinary
end Nanuq.Source

#print axioms Nanuq.Source.RootedBinary.blob_arborescence
