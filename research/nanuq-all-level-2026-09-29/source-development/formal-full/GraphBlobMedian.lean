import GraphBlobPorts
import GraphPortConsequences

namespace Nanuq.Source.RootedBinary

variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X)

noncomputable def blobDescTaxa {n : Nat} (q : Fin n ↪ X) (b : N.graph.Blob) :
    Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i =>
    N.graph.bridgeQuotient.DReach b (N.blobLeaf (q i)))

@[simp] theorem mem_blobDescTaxa {n : Nat} (q : Fin n ↪ X) (b : N.graph.Blob)
    (i : Fin n) : i ∈ N.blobDescTaxa q b ↔
      N.graph.bridgeQuotient.DReach b (N.blobLeaf (q i)) := by
  classical
  simp [blobDescTaxa]

theorem blobDescTaxa_root_card {n : Nat} (q : Fin n ↪ X) :
    (N.blobDescTaxa q (N.graph.blobOf N.root)).card = n := by
  classical
  simp [blobDescTaxa, N.blob_quotient_rooted]

theorem blobDescTaxa_leaf_card_le_one {n : Nat} (q : Fin n ↪ X) (x : X) :
    (N.blobDescTaxa q (N.blobLeaf x)).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro i hi j hj
  have hei := N.graph.bridgeQuotient.dreach_eq_of_outdegree_zero (N.blob_leaf_degrees x).2
    ((N.mem_blobDescTaxa q _ i).mp hi)
  have hej := N.graph.bridgeQuotient.dreach_eq_of_outdegree_zero (N.blob_leaf_degrees x).2
    ((N.mem_blobDescTaxa q _ j).mp hj)
  exact q.injective (N.blobLeaf.injective (hei.symm.trans hej))

theorem nonleafBlob_of_two_descendants {n : Nat} (q : Fin n ↪ X) (b : N.graph.Blob)
    (hc : 2 ≤ (N.blobDescTaxa q b).card) : N.NonleafBlob b := by
  intro x hx
  have hxcard := N.blobDescTaxa_leaf_card_le_one q x
  rw [hx] at hxcard
  exact Nat.not_succ_le_self 1 (hc.trans hxcard)

/-- Descend through any child carrying at least two selected taxa. No upper
bound on a blob's number of ports is assumed. -/
theorem exists_lowest_blob_fork {n : Nat} (q : Fin n ↪ X) (a : N.graph.Blob)
    (hc : 2 ≤ (N.blobDescTaxa q a).card) :
    ∃ b, 2 ≤ (N.blobDescTaxa q b).card ∧
      ∀ e : N.graph.BridgeEdge, N.graph.bridgeQuotient.source e = b →
        (N.blobDescTaxa q (N.graph.bridgeQuotient.target e)).card ≤ 1 := by
  classical
  let r : N.graph.Blob → N.graph.Blob → Prop :=
    fun b a => Relation.TransGen N.graph.bridgeQuotient.DStep a b
  haveI : IsTrans N.graph.Blob r := ⟨fun _ _ _ hab hbc => hbc.trans hab⟩
  haveI : Std.Irrefl r := ⟨fun a => N.blob_quotient_acyclic a⟩
  have hw : WellFounded r := Finite.wellFounded_of_trans_of_irrefl r
  refine hw.induction (C := fun a => 2 ≤ (N.blobDescTaxa q a).card →
    ∃ b, 2 ≤ (N.blobDescTaxa q b).card ∧ ∀ e : N.graph.BridgeEdge,
      N.graph.bridgeQuotient.source e = b →
        (N.blobDescTaxa q (N.graph.bridgeQuotient.target e)).card ≤ 1) a ?_ hc
  intro b ih hb
  by_cases hchild : ∃ e : N.graph.BridgeEdge, N.graph.bridgeQuotient.source e = b ∧
      2 ≤ (N.blobDescTaxa q (N.graph.bridgeQuotient.target e)).card
  · obtain ⟨e, hs, ht⟩ := hchild
    exact ih (N.graph.bridgeQuotient.target e)
      (Relation.TransGen.single ⟨e, hs, rfl⟩) ht
  · refine ⟨b, hb, ?_⟩
    intro e he
    have hn : ¬ 2 ≤ (N.blobDescTaxa q (N.graph.bridgeQuotient.target e)).card :=
      fun h => hchild ⟨e, he, h⟩
    exact Nat.le_of_lt_succ (Nat.lt_of_not_ge hn)

/-- Every triple of distinct taxa has an actual nonleaf blob at which its
three port images are distinct. This is the existence part of the median. -/
theorem exists_three_port_blob (q : Fin 3 ↪ X) :
    ∃ (b : N.graph.Blob) (hb : N.NonleafBlob b),
      Function.Injective (fun i => N.blobProjection b hb (q i)) := by
  classical
  have hroot : 2 ≤ (N.blobDescTaxa q (N.graph.blobOf N.root)).card := by
    rw [N.blobDescTaxa_root_card q]
    exact Nat.le_succ 2
  obtain ⟨b, hbcount, hsmall⟩ :=
    N.exists_lowest_blob_fork q (N.graph.blobOf N.root) hroot
  have hb := N.nonleafBlob_of_two_descendants q b hbcount
  have houtside : (Finset.univ \ N.blobDescTaxa q b).card ≤ 1 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
    exact Nat.sub_le_sub_left hbcount 3
  refine ⟨b, hb, ?_⟩
  intro i j hij
  change N.blobProjection b hb (q i) = N.blobProjection b hb (q j) at hij
  let p := N.blobProjection b hb (q i)
  have hi := N.blobProjection_spec b hb (q i)
  have hj := N.blobProjection_spec b hb (q j)
  rw [← hij] at hj
  change N.graph.bridgeQuotient.IsPortTo b (N.blobLeaf (q i)) p.val at hi
  change N.graph.bridgeQuotient.IsPortTo b (N.blobLeaf (q j)) p.val at hj
  rcases p.property with hs | ht
  · have hid := N.graph.bridgeQuotient.port_outgoing_desc
      N.blob_quotient_uniqueIncoming N.blob_quotient_acyclic hs hi
    have hjd := N.graph.bridgeQuotient.port_outgoing_desc
      N.blob_quotient_uniqueIncoming N.blob_quotient_acyclic hs hj
    exact Finset.card_le_one.mp (hsmall p.val hs) i
      ((N.mem_blobDescTaxa q _ i).mpr hid) j ((N.mem_blobDescTaxa q _ j).mpr hjd)
  · have hid := N.graph.bridgeQuotient.port_incoming_not_desc
      N.blob_quotient_uniqueIncoming N.blob_quotient_acyclic ht hi
    have hjd := N.graph.bridgeQuotient.port_incoming_not_desc
      N.blob_quotient_uniqueIncoming N.blob_quotient_acyclic ht hj
    have himem : i ∈ Finset.univ \ N.blobDescTaxa q b :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,
        fun h => hid ((N.mem_blobDescTaxa q b i).mp h)⟩
    have hjmem : j ∈ Finset.univ \ N.blobDescTaxa q b :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,
        fun h => hjd ((N.mem_blobDescTaxa q b j).mp h)⟩
    exact Finset.card_le_one.mp houtside i himem j hjmem

end Nanuq.Source.RootedBinary

#print axioms Nanuq.Source.RootedBinary.exists_three_port_blob
