import GraphPortFibers
import AnchorPortFibers
import SourceResolve

namespace Nanuq.Source.RootedBinary

open Nanuq.PortPatterns Nanuq.Quartet
open scoped Classical

variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X)

noncomputable def rawQuartetSide (q : Fin 4 ↪ X) (e : E) (a : V) :
    Finset (Fin 4) := by
  classical
  exact Finset.univ.filter (fun i => N.graph.ReachWithout e a (N.leaf (q i)))

@[simp] theorem mem_rawQuartetSide (q : Fin 4 ↪ X) (e : E) (a : V) (i : Fin 4) :
    i ∈ N.rawQuartetSide q e a ↔ N.graph.ReachWithout e a (N.leaf (q i)) := by
  classical
  simp [rawQuartetSide]

theorem rawQuartetSide_card_sum (q : Fin 4 ↪ X) {e : E} (he : N.graph.IsBridge e) :
    (N.rawQuartetSide q e (N.graph.source e)).card +
      (N.rawQuartetSide q e (N.graph.target e)).card = 4 := by
  classical
  have hdisj : Disjoint (N.rawQuartetSide q e (N.graph.source e))
      (N.rawQuartetSide q e (N.graph.target e)) := by
    apply Finset.disjoint_left.mpr
    intro i hs ht
    exact N.graph.bridge_sides_disjoint he
      ((N.mem_rawQuartetSide q e _ i).mp hs) ((N.mem_rawQuartetSide q e _ i).mp ht)
  have hcover : N.rawQuartetSide q e (N.graph.source e) ∪
      N.rawQuartetSide q e (N.graph.target e) = Finset.univ := by
    ext i
    simp only [Finset.mem_union, mem_rawQuartetSide, Finset.mem_univ, iff_true]
    exact N.graph.edge_side_cover e (N.underlying_connected _ _)
  rw [← Finset.card_union_of_disjoint hdisj, hcover]
  exact Fintype.card_fin 4

/-- Two distinct quartet-branching blobs give an actual port fiber of size two. -/
theorem two_branching_blobs_port (q : Fin 4 ↪ X) (b c : N.graph.Blob)
    (hb : N.NonleafBlob b) (hc : N.NonleafBlob c) (hbc : b ≠ c)
    (hf : 3 ≤ portCount (fun i => N.blobProjection b hb (q i)))
    (hg : 3 ≤ portCount (fun i => N.blobProjection c hc (q i))) :
    ∃ p : N.BlobPort b,
      N.graph.bridgeQuotient.IsPortTo b c p.val ∧
      (Finset.univ.filter (fun i => N.blobProjection b hb (q i) = p)).card = 2 := by
  classical
  obtain ⟨p, hp, htransport⟩ := N.port_transport_between_blobs b c hb hc hbc
  have hex : ∃ i : Fin 4, N.blobProjection b hb (q i) ≠ p := by
    by_contra h
    have hall : ∀ i : Fin 4, N.blobProjection b hb (q i) = p := by
      intro i
      by_contra hi
      exact h ⟨i, hi⟩
    have hh := portCount_le_card_add_one (fun i => N.blobProjection b hb (q i))
      ∅ p (fun i _ => hall i)
    simp only [Finset.card_empty, zero_add] at hh
    omega
  obtain ⟨i, hi⟩ := hex
  exact ⟨p, hp, bridge_fiber_card_two _ _ p (N.blobProjection c hc (q i))
    (fun j hj => htransport (q j) (q i) hj hi) hf hg⟩

/-- The separating 2+2 edge is an original bridge, derived from actual port
directions rather than supplied by a blob-tree quartet certificate. -/
theorem two_branching_blobs_bridge (q : Fin 4 ↪ X) (b c : N.graph.Blob)
    (hb : N.NonleafBlob b) (hc : N.NonleafBlob c) (hbc : b ≠ c)
    (hf : 3 ≤ portCount (fun i => N.blobProjection b hb (q i)))
    (hg : 3 ≤ portCount (fun i => N.blobProjection c hc (q i))) :
    ∃ e : E, N.graph.IsBridge e ∧
      (N.rawQuartetSide q e (N.graph.source e)).card = 2 ∧
      (N.rawQuartetSide q e (N.graph.target e)).card = 2 := by
  classical
  obtain ⟨p, _, hp⟩ := N.two_branching_blobs_port q b c hb hc hbc hf hg
  let e := p.val.val
  have he : N.graph.IsBridge e := p.val.property
  have hsum := N.rawQuartetSide_card_sum q he
  refine ⟨e, he, ?_⟩
  rcases p.property with hs | ht
  · have hset : N.rawQuartetSide q e (N.graph.target e) =
        Finset.univ.filter (fun i => N.blobProjection b hb (q i) = p) := by
      ext i
      simp only [mem_rawQuartetSide, Finset.mem_filter, Finset.mem_univ, true_and]
      exact (N.blobProjection_eq_iff_target_side b hb (q i) p hs).symm
    have htwo : (N.rawQuartetSide q e (N.graph.target e)).card = 2 := by
      rw [hset, hp]
    rw [htwo] at hsum
    exact ⟨Nat.add_right_cancel hsum, htwo⟩
  · have hset : N.rawQuartetSide q e (N.graph.source e) =
        Finset.univ.filter (fun i => N.blobProjection b hb (q i) = p) := by
      ext i
      simp only [mem_rawQuartetSide, Finset.mem_filter, Finset.mem_univ, true_and]
      exact (N.blobProjection_eq_iff_source_side b hb (q i) p ht).symm
    have htwo : (N.rawQuartetSide q e (N.graph.source e)).card = 2 := by
      rw [hset, hp]
    rw [htwo] at hsum
    exact ⟨htwo, Nat.add_left_cancel hsum⟩

private theorem classify_two_of_four : ∀ s : Finset (Fin 4), s.card = 2 →
    (0 ∈ s ∧ 1 ∈ s ∧ 2 ∉ s ∧ 3 ∉ s) ∨
    (2 ∈ s ∧ 3 ∈ s ∧ 0 ∉ s ∧ 1 ∉ s) ∨
    (0 ∈ s ∧ 2 ∈ s ∧ 1 ∉ s ∧ 3 ∉ s) ∨
    (1 ∈ s ∧ 3 ∈ s ∧ 0 ∉ s ∧ 2 ∉ s) ∨
    (0 ∈ s ∧ 3 ∈ s ∧ 1 ∉ s ∧ 2 ∉ s) ∨
    (1 ∈ s ∧ 2 ∈ s ∧ 0 ∉ s ∧ 3 ∉ s) := by
  decide +kernel

theorem original_bridge_resolution (q : Fin 4 ↪ X) {e : E}
    (he : N.graph.IsBridge e)
    (ht : (N.rawQuartetSide q e (N.graph.target e)).card = 2) :
    ∃ r, N.graph.Resolves (fun i => N.leaf (q i)) r := by
  let s := N.rawQuartetSide q e (N.graph.target e)
  have hT (i : Fin 4) (hi : i ∈ s) :
      N.graph.ReachWithout e (N.graph.target e) (N.leaf (q i)) :=
    (N.mem_rawQuartetSide q e _ i).mp hi
  have hS (i : Fin 4) (hi : i ∉ s) :
      N.graph.ReachWithout e (N.graph.source e) (N.leaf (q i)) := by
    rcases N.graph.edge_side_cover e (N.underlying_connected _ _) with h | h
    · exact h
    · exact False.elim (hi ((N.mem_rawQuartetSide q e _ i).mpr h))
  rcases classify_two_of_four s ht with h | h | h | h | h | h
  · exact ⟨.xy_zw, e, he, Or.inr ⟨hS 2 h.2.2.1, hS 3 h.2.2.2,
      hT 0 h.1, hT 1 h.2.1⟩⟩
  · exact ⟨.xy_zw, e, he, Or.inl ⟨hS 0 h.2.2.1, hS 1 h.2.2.2,
      hT 2 h.1, hT 3 h.2.1⟩⟩
  · exact ⟨.xz_yw, e, he, Or.inr ⟨hS 1 h.2.2.1, hS 3 h.2.2.2,
      hT 0 h.1, hT 2 h.2.1⟩⟩
  · exact ⟨.xz_yw, e, he, Or.inl ⟨hS 0 h.2.2.1, hS 2 h.2.2.2,
      hT 1 h.1, hT 3 h.2.1⟩⟩
  · exact ⟨.xw_yz, e, he, Or.inr ⟨hS 1 h.2.2.1, hS 2 h.2.2.2,
      hT 0 h.1, hT 3 h.2.1⟩⟩
  · exact ⟨.xw_yz, e, he, Or.inl ⟨hS 0 h.2.2.1, hS 3 h.2.2.2,
      hT 1 h.1, hT 2 h.2.1⟩⟩

/-- Every actual switching has the same quartet whenever two distinct blobs
each occupy three or more of its ports. -/
theorem two_branching_blobs_force_resolution (hgall : N.graph.GalledDetour)
    (q : Fin 4 ↪ X) (b c : N.graph.Blob)
    (hb : N.NonleafBlob b) (hc : N.NonleafBlob c) (hbc : b ≠ c)
    (hf : 3 ≤ portCount (fun i => N.blobProjection b hb (q i)))
    (hg : 3 ≤ portCount (fun i => N.blobProjection c hc (q i))) :
    ∃ r, N.graph.Resolves (fun i => N.leaf (q i)) r ∧
      (∀ S : N.Switching, S.resolve q = r) ∧
      N.rawQuartetMean q = separatesFirstPair r := by
  obtain ⟨e, he, _, ht⟩ := N.two_branching_blobs_bridge q b c hb hc hbc hf hg
  obtain ⟨r, hr⟩ := N.original_bridge_resolution q he ht
  exact ⟨r, hr, fun S => S.resolve_of_original_bridge hgall q r hr,
    N.rawQuartetMean_of_bridge hgall q r hr⟩

end Nanuq.Source.RootedBinary

#print axioms Nanuq.Source.RootedBinary.two_branching_blobs_bridge
#print axioms Nanuq.Source.RootedBinary.two_branching_blobs_force_resolution
