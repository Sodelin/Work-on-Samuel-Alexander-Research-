import GraphBlobPorts
import GraphPortTransport

namespace Nanuq.Source.RootedBinary

variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X)

theorem blobProjection_eq_iff_port (b : N.graph.Blob) (hb : N.NonleafBlob b)
    (x : X) (p : N.BlobPort b) :
    N.blobProjection b hb x = p ↔
      N.graph.bridgeQuotient.IsPortTo b (N.blobLeaf x) p.val := by
  constructor
  · intro h
    simpa only [h] using N.blobProjection_spec b hb x
  · intro h
    apply Subtype.ext
    exact N.graph.bridgeQuotient.port_unique N.blob_quotient_uniqueIncoming
      N.blob_quotient_acyclic (N.blobProjection_spec b hb x) h

/-- An outgoing port fiber is exactly the taxon component beyond its original
bridge, not a supplied abstract partition. -/
theorem blobProjection_eq_iff_target_side (b : N.graph.Blob)
    (hb : N.NonleafBlob b) (x : X) (p : N.BlobPort b)
    (hs : N.graph.bridgeQuotient.source p.val = b) :
    N.blobProjection b hb x = p ↔
      N.graph.ReachWithout p.val.val (N.graph.target p.val.val) (N.leaf x) := by
  rw [N.blobProjection_eq_iff_port]
  constructor
  · intro h
    rcases h with ⟨_, ht⟩ | ⟨ht, _⟩
    · exact N.graph.quotient_reach_lifts_without p.val ht rfl rfl
    · exact False.elim ((N.graph.bridgeQuotient.bridge_endpoints_ne
        (N.graph.quotient_edge_is_bridge p.val)) (hs.trans ht.symm))
  · intro h
    exact Or.inl ⟨hs, N.graph.reach_projects_without p.val h⟩

/-- The incoming-port version of the exact fiber/component correspondence. -/
theorem blobProjection_eq_iff_source_side (b : N.graph.Blob)
    (hb : N.NonleafBlob b) (x : X) (p : N.BlobPort b)
    (ht : N.graph.bridgeQuotient.target p.val = b) :
    N.blobProjection b hb x = p ↔
      N.graph.ReachWithout p.val.val (N.graph.source p.val.val) (N.leaf x) := by
  rw [N.blobProjection_eq_iff_port]
  constructor
  · intro h
    rcases h with ⟨hs, _⟩ | ⟨_, hs⟩
    · exact False.elim ((N.graph.bridgeQuotient.bridge_endpoints_ne
        (N.graph.quotient_edge_is_bridge p.val)) (hs.trans ht.symm))
    · exact N.graph.quotient_reach_lifts_without p.val hs rfl rfl
  · intro h
    exact Or.inr ⟨ht, N.graph.reach_projects_without p.val h⟩

/-- At two distinct blobs, all taxa outside the port pointing from the first
blob toward the second lie in a single port of the second blob. -/
theorem port_transport_between_blobs (b c : N.graph.Blob)
    (hb : N.NonleafBlob b) (hc : N.NonleafBlob c) (hbc : b ≠ c) :
    ∃ p : N.BlobPort b,
      N.graph.bridgeQuotient.IsPortTo b c p.val ∧
      ∀ x y, N.blobProjection b hb x ≠ p → N.blobProjection b hb y ≠ p →
        N.blobProjection c hc x = N.blobProjection c hc y := by
  classical
  obtain ⟨e, he⟩ := N.graph.bridgeQuotient.port_exists N.blob_quotient_uniqueIncoming
    N.blob_quotient_acyclic (N.graph.blobOf N.root) N.blob_quotient_rooted b c
    (Ne.symm hbc)
  let p : N.BlobPort b := ⟨e, he.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)⟩
  refine ⟨p, he, ?_⟩
  intro x y hx hy
  have hne (z : X) (hz : N.blobProjection b hb z ≠ p) :
      (N.blobProjection b hb z).val ≠ e := fun h => hz (Subtype.ext h)
  have hebridge := N.graph.quotient_edge_is_bridge e
  apply Subtype.ext
  rcases he with ⟨hes, hec⟩ | ⟨het, hec⟩
  · have hside (z : X) (hz : N.blobProjection b hb z ≠ p) :
        N.graph.bridgeQuotient.ReachWithout e (N.graph.bridgeQuotient.source e)
          (N.blobLeaf z) := by
      rcases N.graph.bridgeQuotient.edge_side_cover e
        ((N.blob_quotient_is_tree).2.1 _ _) with hs | ht
      · exact hs
      · exact False.elim (hne z hz (N.graph.bridgeQuotient.port_unique
          N.blob_quotient_uniqueIncoming N.blob_quotient_acyclic
          (N.blobProjection_spec b hb z) (Or.inl ⟨hes, ht⟩)))
    exact N.graph.bridgeQuotient.ports_equal_across_bridge
      N.blob_quotient_uniqueIncoming N.blob_quotient_acyclic hebridge
      (N.graph.bridgeQuotient.inc_symm (N.graph.bridgeQuotient.inc_source_target e))
      hec (hside x hx) (hside y hy)
      (N.blobProjection_spec c hc x) (N.blobProjection_spec c hc y)
  · have hside (z : X) (hz : N.blobProjection b hb z ≠ p) :
        N.graph.bridgeQuotient.ReachWithout e (N.graph.bridgeQuotient.target e)
          (N.blobLeaf z) := by
      rcases N.graph.bridgeQuotient.edge_side_cover e
        ((N.blob_quotient_is_tree).2.1 _ _) with hs | ht
      · exact False.elim (hne z hz (N.graph.bridgeQuotient.port_unique
          N.blob_quotient_uniqueIncoming N.blob_quotient_acyclic
          (N.blobProjection_spec b hb z) (Or.inr ⟨het, hs⟩)))
      · exact ht
    exact N.graph.bridgeQuotient.ports_equal_across_bridge
      N.blob_quotient_uniqueIncoming N.blob_quotient_acyclic hebridge
      (N.graph.bridgeQuotient.inc_source_target e)
      hec (hside x hx) (hside y hy)
      (N.blobProjection_spec c hc x) (N.blobProjection_spec c hc y)

end Nanuq.Source.RootedBinary

#print axioms Nanuq.Source.RootedBinary.blobProjection_eq_iff_target_side
#print axioms Nanuq.Source.RootedBinary.blobProjection_eq_iff_source_side
#print axioms Nanuq.Source.RootedBinary.port_transport_between_blobs
