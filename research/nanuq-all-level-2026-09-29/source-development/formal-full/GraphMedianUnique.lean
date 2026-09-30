import GraphBlobMedian
import GraphPortTransport

namespace Nanuq.Source.RootedBinary

private theorem two_of_three_avoid {A : Type*} (f : Fin 3 → A)
    (hf : Function.Injective f) (a : A) :
    ∃ i j, i ≠ j ∧ f i ≠ a ∧ f j ≠ a := by
  classical
  by_cases h0 : f 0 = a
  · refine ⟨1, 2, by decide, ?_, ?_⟩
    · intro h1
      exact (by decide : (1 : Fin 3) ≠ 0) (hf (h1.trans h0.symm))
    · intro h2
      exact (by decide : (2 : Fin 3) ≠ 0) (hf (h2.trans h0.symm))
  · by_cases h1 : f 1 = a
    · refine ⟨0, 2, by decide, h0, ?_⟩
      intro h2
      exact (by decide : (2 : Fin 3) ≠ 1) (hf (h2.trans h1.symm))
    · exact ⟨0, 1, by decide, h0, h1⟩

variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X)

/-- Two distinct blobs cannot each put the same three taxa in three distinct
ports: the bridge direction between them puts two taxa in one port at the other. -/
theorem three_port_blob_unique (q : Fin 3 ↪ X) (b c : N.graph.Blob)
    (hb : N.NonleafBlob b) (hc : N.NonleafBlob c)
    (hbi : Function.Injective (fun i => N.blobProjection b hb (q i)))
    (hci : Function.Injective (fun i => N.blobProjection c hc (q i))) : b = c := by
  classical
  by_contra hbc
  obtain ⟨e, he⟩ := N.graph.bridgeQuotient.port_exists N.blob_quotient_uniqueIncoming
    N.blob_quotient_acyclic (N.graph.blobOf N.root) N.blob_quotient_rooted b c (Ne.symm hbc)
  let f : Fin 3 → N.graph.BridgeEdge := fun i => (N.blobProjection b hb (q i)).val
  have hfi : Function.Injective f := by
    intro i j hij
    exact hbi (Subtype.ext hij)
  obtain ⟨i, j, hij, hi, hj⟩ := two_of_three_avoid f hfi e
  have hebridge := N.graph.quotient_edge_is_bridge e
  rcases he with ⟨hes, hec⟩ | ⟨het, hec⟩
  · have hside (k : Fin 3) (hk : f k ≠ e) :
        N.graph.bridgeQuotient.ReachWithout e (N.graph.bridgeQuotient.source e)
          (N.blobLeaf (q k)) := by
      rcases N.graph.bridgeQuotient.edge_side_cover e
        ((N.blob_quotient_is_tree).2.1 _ _) with hs | ht
      · exact hs
      · exact False.elim (hk (N.graph.bridgeQuotient.port_unique
          N.blob_quotient_uniqueIncoming N.blob_quotient_acyclic
          (N.blobProjection_spec b hb (q k)) (Or.inl ⟨hes, ht⟩)))
    have hp := N.graph.bridgeQuotient.ports_equal_across_bridge
      N.blob_quotient_uniqueIncoming N.blob_quotient_acyclic hebridge
      (N.graph.bridgeQuotient.inc_symm (N.graph.bridgeQuotient.inc_source_target e))
      hec (hside i hi) (hside j hj)
      (N.blobProjection_spec c hc (q i)) (N.blobProjection_spec c hc (q j))
    exact hij (hci (Subtype.ext hp))
  · have hside (k : Fin 3) (hk : f k ≠ e) :
        N.graph.bridgeQuotient.ReachWithout e (N.graph.bridgeQuotient.target e)
          (N.blobLeaf (q k)) := by
      rcases N.graph.bridgeQuotient.edge_side_cover e
        ((N.blob_quotient_is_tree).2.1 _ _) with hs | ht
      · exact False.elim (hk (N.graph.bridgeQuotient.port_unique
          N.blob_quotient_uniqueIncoming N.blob_quotient_acyclic
          (N.blobProjection_spec b hb (q k)) (Or.inr ⟨het, hs⟩)))
      · exact ht
    have hp := N.graph.bridgeQuotient.ports_equal_across_bridge
      N.blob_quotient_uniqueIncoming N.blob_quotient_acyclic hebridge
      (N.graph.bridgeQuotient.inc_source_target e)
      hec (hside i hi) (hside j hj)
      (N.blobProjection_spec c hc (q i)) (N.blobProjection_spec c hc (q j))
    exact hij (hci (Subtype.ext hp))

def ThreeWayBlob (q : Fin 3 ↪ X) (b : N.graph.Blob) : Prop :=
  ∃ hb : N.NonleafBlob b, Function.Injective (fun i => N.blobProjection b hb (q i))

theorem existsUnique_three_way_blob (q : Fin 3 ↪ X) : ∃! b, N.ThreeWayBlob q b := by
  obtain ⟨b, hb, hbi⟩ := N.exists_three_port_blob q
  refine ⟨b, ⟨hb, hbi⟩, ?_⟩
  intro c hc
  obtain ⟨hc, hci⟩ := hc
  exact N.three_port_blob_unique q c b hc hb hci hbi

noncomputable def tripleMedian (q : Fin 3 ↪ X) : N.graph.Blob :=
  Classical.choose (N.existsUnique_three_way_blob q)

theorem tripleMedian_spec (q : Fin 3 ↪ X) : N.ThreeWayBlob q (N.tripleMedian q) :=
  (Classical.choose_spec (N.existsUnique_three_way_blob q)).1

end Nanuq.Source.RootedBinary

#print axioms Nanuq.Source.RootedBinary.existsUnique_three_way_blob
