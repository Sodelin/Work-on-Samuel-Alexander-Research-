import GraphBlobOrientation

namespace Nanuq.Source
namespace EdgeGraph

variable {V E : Type*} (G : EdgeGraph V E)

theorem ureach_eq_of_no_step {keep : E → Prop} {a b : V}
    (hno : ∀ c, ¬ G.UStep keep a c) (h : G.UReach keep a b) : a = b := by
  induction h with
  | refl => rfl
  | @tail b c _ hstep ih =>
      rw [← ih] at hstep
      exact False.elim (hno c hstep)

end EdgeGraph

namespace RootedBinary
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X)

theorem no_edge_source_leaf (x : X) (e : E) : N.graph.source e ≠ N.leaf x := by
  intro hs
  have hc : 0 < N.graph.outDegree (N.leaf x) :=
    Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩⟩
  rw [(N.leaf_degrees x).2] at hc
  exact Nat.not_lt_zero _ hc

theorem leaf_incident_edge (x : X) :
    ∃ e, N.graph.target e = N.leaf x ∧
      ∀ f b, N.graph.Inc f (N.leaf x) b → f = e := by
  obtain ⟨e, he, hu⟩ := N.incoming_unique_of_indegree_one (N.leaf_degrees x).1
  refine ⟨e, he, ?_⟩
  intro f b hf
  rcases hf with ⟨hs, _⟩ | ⟨_, ht⟩
  · exact False.elim (N.no_edge_source_leaf x f hs)
  · exact hu f ht

theorem leaf_incoming_bridge (x : X) {e : E} (he : N.graph.target e = N.leaf x) :
    N.graph.IsBridge e := by
  obtain ⟨f, _, hf⟩ := N.leaf_incident_edge x
  have hef : e = f := hf e (N.graph.source e) (Or.inr ⟨rfl, he⟩)
  have hno : ∀ b, ¬ N.graph.UStep (fun g => g ≠ e) (N.leaf x) b := by
    intro b h
    obtain ⟨g, hge, hg⟩ := h
    exact hge ((hf g b hg).trans hef.symm)
  intro hdetour
  rw [he] at hdetour
  have hEq := N.graph.ureach_eq_of_no_step hno (N.graph.ureach_symm hdetour)
  exact N.no_edge_source_leaf x e hEq.symm

theorem leaf_sameBlob_iff (x : X) (a : V) :
    N.graph.SameBlob (N.leaf x) a ↔ a = N.leaf x := by
  constructor
  · intro h
    obtain ⟨e, he, hu⟩ := N.leaf_incident_edge x
    have hno : ∀ b, ¬ N.graph.UStep (fun f => ¬ N.graph.IsBridge f) (N.leaf x) b := by
      intro b hs
      obtain ⟨f, hf, hinc⟩ := hs
      have hfe := hu f b hinc
      subst f
      exact hf (N.leaf_incoming_bridge x he)
    exact (N.graph.ureach_eq_of_no_step hno h).symm
  · rintro rfl
    exact .refl

theorem blobOf_leaf_eq_iff (x : X) (a : V) :
    N.graph.blobOf a = N.graph.blobOf (N.leaf x) ↔ a = N.leaf x := by
  constructor
  · intro h
    exact (N.leaf_sameBlob_iff x a).mp (N.graph.sameBlob_symm (Quotient.exact h))
  · rintro rfl
    rfl

def blobLeaf : X ↪ N.graph.Blob where
  toFun x := N.graph.blobOf (N.leaf x)
  inj' := by
    intro x y h
    exact N.leaf.injective ((N.blobOf_leaf_eq_iff y (N.leaf x)).mp h)

theorem blob_leaf_ne_root (x : X) : N.blobLeaf x ≠ N.graph.blobOf N.root := by
  intro h
  have hr := (N.blobOf_leaf_eq_iff x N.root).mp h.symm
  exact N.leaf_ne_root x hr.symm

theorem blob_leaf_no_outgoing (x : X) (e : N.graph.BridgeEdge) :
    N.graph.bridgeQuotient.source e ≠ N.blobLeaf x := by
  intro h
  exact N.no_edge_source_leaf x e.val
    ((N.blobOf_leaf_eq_iff x (N.graph.source e.val)).mp h)

theorem blob_leaf_incoming_unique (x : X) :
    ∃ e : N.graph.BridgeEdge, N.graph.bridgeQuotient.target e = N.blobLeaf x ∧
      ∀ f : N.graph.BridgeEdge, N.graph.bridgeQuotient.target f = N.blobLeaf x → f = e := by
  obtain ⟨e, he, hu⟩ := N.incoming_unique_of_indegree_one (N.leaf_degrees x).1
  let f : N.graph.BridgeEdge := ⟨e, N.leaf_incoming_bridge x he⟩
  refine ⟨f, congrArg N.graph.blobOf he, ?_⟩
  intro g hg
  apply Subtype.ext
  exact hu g.val ((N.blobOf_leaf_eq_iff x (N.graph.target g.val)).mp hg)

/-- Original taxa give distinct degree-one leaves of the actual blob quotient. -/
theorem blob_leaf_degrees (x : X) :
    N.graph.bridgeQuotient.inDegree (N.blobLeaf x) = 1 ∧
    N.graph.bridgeQuotient.outDegree (N.blobLeaf x) = 0 := by
  classical
  constructor
  · apply Finset.card_eq_one_iff_existsUnique.mpr
    obtain ⟨e, he, hu⟩ := N.blob_leaf_incoming_unique x
    refine ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩, ?_⟩
    intro f hf
    exact hu f (Finset.mem_filter.mp hf).2
  · apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    exact N.blob_leaf_no_outgoing x e (Finset.mem_filter.mp he).2

end RootedBinary
end Nanuq.Source

#print axioms Nanuq.Source.RootedBinary.blobLeaf
#print axioms Nanuq.Source.RootedBinary.blob_leaf_degrees
