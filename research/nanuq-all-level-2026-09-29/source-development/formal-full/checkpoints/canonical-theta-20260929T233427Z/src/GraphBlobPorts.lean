import GraphBlobLeaves
import GraphTreePorts
import GraphPorts

namespace Nanuq.Source.RootedBinary

variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X)

/-- Nonleaf blobs are precisely those distinct from every labeled leaf blob. -/
def NonleafBlob (b : N.graph.Blob) : Prop := ∀ x, N.blobLeaf x ≠ b

def BlobPort (b : N.graph.Blob) :=
  {e : N.graph.BridgeEdge //
    N.graph.bridgeQuotient.source e = b ∨ N.graph.bridgeQuotient.target e = b}

noncomputable instance blobPortFintype (b : N.graph.Blob) : Fintype (N.BlobPort b) := by
  classical
  unfold BlobPort
  infer_instance

/-- Actual taxon-to-port projection, constructed by unique graph direction. -/
noncomputable def blobProjection (b : N.graph.Blob) (hb : N.NonleafBlob b) (x : X) :
    N.BlobPort b := by
  let e := N.graph.bridgeQuotient.portTo N.blob_quotient_uniqueIncoming
    N.blob_quotient_acyclic (N.graph.blobOf N.root) N.blob_quotient_rooted
    b (N.blobLeaf x) (hb x)
  have he := N.graph.bridgeQuotient.portTo_spec N.blob_quotient_uniqueIncoming
    N.blob_quotient_acyclic (N.graph.blobOf N.root) N.blob_quotient_rooted
    b (N.blobLeaf x) (hb x)
  exact ⟨e, he.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)⟩

theorem blobProjection_spec (b : N.graph.Blob) (hb : N.NonleafBlob b) (x : X) :
    N.graph.bridgeQuotient.IsPortTo b (N.blobLeaf x) (N.blobProjection b hb x).val :=
  N.graph.bridgeQuotient.portTo_spec N.blob_quotient_uniqueIncoming
    N.blob_quotient_acyclic (N.graph.blobOf N.root) N.blob_quotient_rooted
    b (N.blobLeaf x) (hb x)

/-- Every actual port has at least one actual taxon on its external side. -/
theorem blobProjection_surjective (b : N.graph.Blob) (hb : N.NonleafBlob b) :
    Function.Surjective (N.blobProjection b hb) := by
  intro p
  rcases p.property with hs | ht
  · obtain ⟨x, hx⟩ := N.bridge_target_side_contains_taxon p.val.property
    refine ⟨x, ?_⟩
    apply Subtype.ext
    exact N.graph.bridgeQuotient.port_unique N.blob_quotient_uniqueIncoming
      N.blob_quotient_acyclic (N.blobProjection_spec b hb x)
      (Or.inl ⟨hs, N.graph.reach_projects_without p.val hx⟩)
  · obtain ⟨x, hx⟩ := N.bridge_source_side_contains_taxon p.val.val
    refine ⟨x, ?_⟩
    apply Subtype.ext
    exact N.graph.bridgeQuotient.port_unique N.blob_quotient_uniqueIncoming
      N.blob_quotient_acyclic (N.blobProjection_spec b hb x)
      (Or.inr ⟨ht, N.graph.reach_projects_without p.val hx⟩)

noncomputable def portTaxa (b : N.graph.Blob) (hb : N.NonleafBlob b) (p : N.BlobPort b) :
    Finset X := by
  classical
  exact Finset.univ.filter (fun x => N.blobProjection b hb x = p)

/-- The masses used by the local weighted metric are actual positive fiber
cardinalities of the proved port projection. -/
theorem actual_port_mass_positive (b : N.graph.Blob) (hb : N.NonleafBlob b)
    (p : N.BlobPort b) : 0 < (N.portTaxa b hb p).card := by
  classical
  obtain ⟨x, hx⟩ := N.blobProjection_surjective b hb p
  apply Finset.card_pos.mpr
  exact ⟨x, by simp [portTaxa, hx]⟩

end Nanuq.Source.RootedBinary

#print axioms Nanuq.Source.RootedBinary.blobProjection_surjective
#print axioms Nanuq.Source.RootedBinary.actual_port_mass_positive
