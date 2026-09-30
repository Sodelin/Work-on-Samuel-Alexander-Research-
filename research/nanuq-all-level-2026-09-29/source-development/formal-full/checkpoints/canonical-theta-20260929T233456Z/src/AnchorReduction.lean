import AnchorIndexTransport
import ZeroTheta

/-!
Six-witness reduction from a proved leaf-level compression invariance theorem
to the kernel-checked finite certificate. No bound on original arm lengths is
assumed. The sole remaining hypothesis here is stated leaf-level invariance.
-/
namespace Nanuq.Theta

theorem alpha_nonnegative_of_anchor_compression (t : Counts)
    (hpreserve : ∀ (W : Finset Leaf), (∀ l ∈ W, l ∈ circular t) →
      Leaf.c1 ∈ W → Leaf.c2 ∈ W →
      ∀ a ∈ W, ∀ b ∈ W, a ≠ b → ∀ x ∈ W, ∀ y ∈ W,
        anchor t a b x y =
          anchor (compressedCounts W) (compressLeaf W a) (compressLeaf W b)
            (compressLeaf W x) (compressLeaf W y))
    (p q i j : Fin (circular t).length) (hpq : p < q) (hij : i < j) :
    0 ≤ alpha t p.val q.val i.val j.val := by
  let W := retainedWitnesses t p q i j
  have hvalid : ∀ l ∈ W, l ∈ circular t :=
    fun _ hl => retainedWitnesses_subset_circular t p q i j hl
  have hc1 : Leaf.c1 ∈ W := by simp [W, retainedWitnesses]
  have hc2 : Leaf.c2 ∈ W := by simp [W, retainedWitnesses]
  have hp : leafIndex t p ∈ W := by simp [W, retainedWitnesses, sixWitnesses]
  have hq : leafIndex t q ∈ W := by simp [W, retainedWitnesses, sixWitnesses]
  have hi : leafIndex t i ∈ W := by simp [W, retainedWitnesses, sixWitnesses]
  have hj : leafIndex t j ∈ W := by simp [W, retainedWitnesses, sixWitnesses]
  have hin : leafIndex t (Nanuq.Weighted.cyclicNext i) ∈ W := by
    simp [W, retainedWitnesses, sixWitnesses]
  have hjn : leafIndex t (Nanuq.Weighted.cyclicNext j) ∈ W := by
    simp [W, retainedWitnesses, sixWitnesses]
  have hpqLeaf : leafIndex t p ≠ leafIndex t q := by
    intro heq
    exact (ne_of_lt hpq) (leafIndex_injective t heq)
  have heq := alpha_preserved_under_compression t W hvalid hc1 hc2 p q i j
    hp hq hi hj hin hjn (fun a ha b hb =>
      hpreserve W hvalid hc1 hc2 _ hp _ hq hpqLeaf a ha b hb)
  rw [heq]
  exact anchor_nonnegative_upto_six (compressedCounts W)
    (compressed_retained_total_le t p q i j)
    (compressedIndex_strictMono t W hvalid hc1 hc2 p q hp hq hpq)
    (compressedIndex t W hvalid hc1 hc2 q hq).isLt
    (compressedIndex_strictMono t W hvalid hc1 hc2 i j hi hj hij)
    (compressedIndex t W hvalid hc1 hc2 j hj).isLt

theorem weighted_anchor_nonnegative_of_compression (t : Counts)
    (hpreserve : ∀ (W : Finset Leaf), (∀ l ∈ W, l ∈ circular t) →
      Leaf.c1 ∈ W → Leaf.c2 ∈ W →
      ∀ a ∈ W, ∀ b ∈ W, a ≠ b → ∀ x ∈ W, ∀ y ∈ W,
        anchor t a b x y =
          anchor (compressedCounts W) (compressLeaf W a) (compressLeaf W b)
            (compressLeaf W x) (compressLeaf W y))
    (p q i j : Fin (circular t).length) (hpq : p < q) (hij : i < j) :
    0 ≤ Nanuq.Weighted.circularAlpha
      (Nanuq.Weighted.anchorMatrix (rhoFin t) p q) i j := by
  rw [weighted_alpha_eq_alpha]
  exact alpha_nonnegative_of_anchor_compression t hpreserve p q i j hpq hij

#print axioms alpha_nonnegative_of_anchor_compression
#print axioms weighted_anchor_nonnegative_of_compression

end Nanuq.Theta


