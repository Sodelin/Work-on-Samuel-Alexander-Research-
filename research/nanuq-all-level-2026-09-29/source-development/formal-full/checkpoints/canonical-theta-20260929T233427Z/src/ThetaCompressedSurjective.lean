import AnchorIndexTransport
import AnchorLeafPosition

/-! Every compressed canonical index comes from one retained original taxon. -/
namespace Nanuq.Theta

theorem compressedIndex_surjective (t : Counts) (W : Finset Leaf)
    (hvalid : ∀ l ∈ W, l ∈ circular t) (hc1 : Leaf.c1 ∈ W) (hc2 : Leaf.c2 ∈ W)
    (q : Fin (circular (compressedCounts W)).length) :
    ∃ p : Fin (circular t).length, ∃ hp : leafIndex t p ∈ W,
      compressedIndex t W hvalid hc1 hc2 p hp = q := by
  have hmem := leafIndex_mem_circular (compressedCounts W) q
  rw [← compressed_circular_eq t W hvalid hc1 hc2] at hmem
  obtain ⟨l,hl,himage⟩ := List.mem_map.mp hmem
  have horiginal : l ∈ circular t := (List.mem_filter.mp hl).1
  have hkeep : l ∈ W := of_decide_eq_true (List.mem_filter.mp hl).2
  let p : Fin (circular t).length := ⟨leafPosition t l,leafPosition_lt t horiginal⟩
  have hleaf : leafIndex t p = l := leafAt_leafPosition t horiginal
  have hp : leafIndex t p ∈ W := by rw [hleaf]; exact hkeep
  refine ⟨p,hp,?_⟩
  apply leafIndex_injective (compressedCounts W)
  rw [leafIndex_compressedIndex t W hvalid hc1 hc2 p hp,hleaf]
  exact himage

theorem compressedIndex_lt_iff (t : Counts) (W : Finset Leaf)
    (hvalid : ∀ l ∈ W, l ∈ circular t) (hc1 : Leaf.c1 ∈ W) (hc2 : Leaf.c2 ∈ W)
    (p q : Fin (circular t).length) (hp : leafIndex t p ∈ W) (hq : leafIndex t q ∈ W) :
    compressedIndex t W hvalid hc1 hc2 p hp < compressedIndex t W hvalid hc1 hc2 q hq ↔ p < q := by
  constructor
  · intro hlt
    by_contra hnot
    rcases lt_or_eq_of_le (le_of_not_gt hnot) with hqp | heq
    · have hreverse := compressedIndex_strictMono t W hvalid hc1 hc2 q p hq hp hqp
      exact (not_lt_of_gt hreverse) hlt
    · subst q
      exact (lt_irrefl _) hlt
  · exact compressedIndex_strictMono t W hvalid hc1 hc2 p q hp hq

#print axioms compressedIndex_surjective
#print axioms compressedIndex_lt_iff
end Nanuq.Theta