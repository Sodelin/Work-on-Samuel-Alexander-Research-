import CircularThetaSupport
import AnchorNondegenerate
import ThetaCompression

/-! Retaining both boundaries of a circular split preserves its actual
edge-display predicate under arm compression. -/
namespace Nanuq.Theta
open Nanuq.Weighted Nanuq.Reconstruction

theorem compressed_successor_eq_iff (t : Counts) (W : Finset Leaf)
    (hvalid : ∀ l ∈ W, l ∈ circular t) (hc1 : Leaf.c1 ∈ W) (hc2 : Leaf.c2 ∈ W)
    (i j : Fin (circular t).length) (hi : leafIndex t i ∈ W) (hj : leafIndex t j ∈ W)
    (hin : leafIndex t (cyclicNext i) ∈ W) :
    cyclicNext (compressedIndex t W hvalid hc1 hc2 i hi) =
        compressedIndex t W hvalid hc1 hc2 j hj ↔ cyclicNext i = j := by
  rw [← compressedIndex_cyclicNext t W hvalid hc1 hc2 i hi hin]
  constructor
  · exact compressedIndex_injective t W hvalid hc1 hc2 _ _ hin hj
  · intro he
    subst j
    rfl

theorem displayedSplit_compression (t : Counts) (W : Finset Leaf)
    (hvalid : ∀ l ∈ W, l ∈ circular t) (hc1 : Leaf.c1 ∈ W) (hc2 : Leaf.c2 ∈ W)
    (i j : Fin (circular t).length) (hi : leafIndex t i ∈ W) (hj : leafIndex t j ∈ W)
    (hin : leafIndex t (cyclicNext i) ∈ W) (hjn : leafIndex t (cyclicNext j) ∈ W)
    (hij : i < j) :
    displayedSplit t i.val j.val = true ↔
      displayedSplit (compressedCounts W)
        (compressedIndex t W hvalid hc1 hc2 i hi).val
        (compressedIndex t W hvalid hc1 hc2 j hj).val = true := by
  let u := compressedCounts W
  let ci := compressedIndex t W hvalid hc1 hc2 i hi
  let cj := compressedIndex t W hvalid hc1 hc2 j hj
  have hcij : ci < cj := compressedIndex_strictMono t W hvalid hc1 hc2 i j hi hj hij
  have hs1 : cyclicNext ci = cj ↔ cyclicNext i = j :=
    compressed_successor_eq_iff t W hvalid hc1 hc2 i j hi hj hin
  have hs2 : cyclicNext cj = ci ↔ cyclicNext j = i :=
    compressed_successor_eq_iff t W hvalid hc1 hc2 j i hj hi hjn
  change displayedSplit t i.val j.val = true ↔ displayedSplit u ci.val cj.val = true
  by_cases hni : cyclicNext i = j
  · exact iff_of_true (displayedSplit_of_successor t i j hij (Or.inl hni))
      (displayedSplit_of_successor u ci cj hcij (Or.inl (hs1.mpr hni)))
  by_cases hnj : cyclicNext j = i
  · exact iff_of_true (displayedSplit_of_successor t i j hij (Or.inr hnj))
      (displayedSplit_of_successor u ci cj hcij (Or.inr (hs2.mpr hnj)))
  have hnci : cyclicNext ci ≠ cj := fun h => hni (hs1.mp h)
  have hncj : cyclicNext cj ≠ ci := fun h => hnj (hs2.mp h)
  rw [displayedSplit_iff_boundary_quartet t i j hij hni hnj,
    displayedSplit_iff_boundary_quartet u ci cj hcij hnci hncj]
  have hn : 2 ≤ (circular t).length := by rw [circular_length]; omega
  have hab : leafIndex t i ≠ leafIndex t (cyclicNext j) :=
    fun h => hnj ((leafIndex_injective t h).symm)
  have hac : leafIndex t i ≠ leafIndex t (cyclicNext i) :=
    fun h => cyclicNext_ne_self_of_two_le hn i ((leafIndex_injective t h).symm)
  have had : leafIndex t i ≠ leafIndex t j :=
    fun h => (ne_of_lt hij) (leafIndex_injective t h)
  have hbc : leafIndex t (cyclicNext j) ≠ leafIndex t (cyclicNext i) :=
    fun h => (ne_of_gt hij) (cyclicNext_injective (leafIndex_injective t h))
  have hbd : leafIndex t (cyclicNext j) ≠ leafIndex t j :=
    fun h => cyclicNext_ne_self_of_two_le hn j (leafIndex_injective t h)
  have hcd : leafIndex t (cyclicNext i) ≠ leafIndex t j :=
    fun h => hni (leafIndex_injective t h)
  have hci : leafIndex u ci = compressLeaf W (leafIndex t i) :=
    leafIndex_compressedIndex t W hvalid hc1 hc2 i hi
  have hcj : leafIndex u cj = compressLeaf W (leafIndex t j) :=
    leafIndex_compressedIndex t W hvalid hc1 hc2 j hj
  have hcin : leafIndex u (cyclicNext ci) = compressLeaf W (leafIndex t (cyclicNext i)) := by
    rw [← compressedIndex_cyclicNext t W hvalid hc1 hc2 i hi hin]
    exact leafIndex_compressedIndex t W hvalid hc1 hc2 _ hin
  have hcjn : leafIndex u (cyclicNext cj) = compressLeaf W (leafIndex t (cyclicNext j)) := by
    rw [← compressedIndex_cyclicNext t W hvalid hc1 hc2 j hj hjn]
    exact leafIndex_compressedIndex t W hvalid hc1 hc2 _ hjn
  simp only [hci,hcj,hcin,hcjn]
  apply exists_congr
  intro s
  rw [quartet_compression t W hvalid s _ _ _ _ hi hjn hin hj hab hac had hbc hbd hcd]

#print axioms displayedSplit_compression
end Nanuq.Theta
