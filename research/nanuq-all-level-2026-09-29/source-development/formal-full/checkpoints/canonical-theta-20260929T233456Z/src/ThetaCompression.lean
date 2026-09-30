import ThetaQuartetOrder
import AnchorMetricOrder

/-! Exact source-quartet and anchor preservation under arbitrary arm compression. -/
namespace Nanuq.Theta

/-- Deleting unselected ordinary arm leaves and replacing their positions by
ranks preserves each of the four actual switched-tree quartet resolutions. -/
theorem quartet_compression (t : Counts) (W : Finset Leaf)
    (hvalid : ∀ l ∈ W, l ∈ circular t) (s : Switching) (a b c d : Leaf)
    (ha : a ∈ W) (hb : b ∈ W) (hc : c ∈ W) (hd : d ∈ W)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    quartet t s a b c d =
      quartet (compressedCounts W) s (compressLeaf W a) (compressLeaf W b)
        (compressLeaf W c) (compressLeaf W d) := by
  have hne {x y : Leaf} (hx : x ∈ W) (hy : y ∈ W) (hne : x ≠ y) :
      compressLeaf W x ≠ compressLeaf W y :=
    fun h => hne (compressLeaf_injective_on W hx hy h)
  rw [quartet_eq_orderQuartet t s a b c d
    (hvalid a ha) (hvalid b hb) (hvalid c hc) (hvalid d hd) hab hac had hbc hbd hcd,
    quartet_eq_orderQuartet (compressedCounts W) s
      (compressLeaf W a) (compressLeaf W b) (compressLeaf W c) (compressLeaf W d)
      (compressLeaf_mem_circular W ha) (compressLeaf_mem_circular W hb)
      (compressLeaf_mem_circular W hc) (compressLeaf_mem_circular W hd)
      (hne ha hb hab) (hne ha hc hac) (hne ha hd had)
      (hne hb hc hbc) (hne hb hd hbd) (hne hc hd hcd)]
  let X := {l : Leaf // l ∈ W}
  have he := orderQuartet_invariant
    (fun x : X => switchedArm s x.val)
    (fun x : X => metricPosition t s x.val)
    (fun x : X => metricPosition (compressedCounts W) s (compressLeaf W x.val))
    (fun x y hsame => metricPosition_lt_iff_compressed t W hvalid s
      x.val y.val x.property y.property hsame)
    (⟨a, ha⟩ : X) (⟨b, hb⟩ : X) (⟨c, hc⟩ : X) (⟨d, hd⟩ : X)
  simpa only [orderQuartet, switchedArm_compressLeaf] using he

/-- The equality preserves the source's distinct quartet set, including
multiplicities being discarded before taking the mean. -/
theorem rho2_compression (t : Counts) (W : Finset Leaf)
    (hvalid : ∀ l ∈ W, l ∈ circular t) (a b c d : Leaf)
    (ha : a ∈ W) (hb : b ∈ W) (hc : c ∈ W) (hd : d ∈ W)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    rho2 t a b c d =
      rho2 (compressedCounts W) (compressLeaf W a) (compressLeaf W b)
        (compressLeaf W c) (compressLeaf W d) := by
  have he : (fun s => quartet t s a b c d) =
      (fun s => quartet (compressedCounts W) s (compressLeaf W a)
        (compressLeaf W b) (compressLeaf W c) (compressLeaf W d)) := by
    funext s
    exact quartet_compression t W hvalid s a b c d ha hb hc hd hab hac had hbc hbd hcd
  simp only [rho2, distinctQuartets, he]

/-- Every retained entry of an anchor matrix is unchanged by compression.
Only the two anchors must be distinct; the matrix endpoints may coincide. -/
theorem anchor_compression (t : Counts) (W : Finset Leaf)
    (hvalid : ∀ l ∈ W, l ∈ circular t) (p q x y : Leaf)
    (hp : p ∈ W) (hq : q ∈ W) (hx : x ∈ W) (hy : y ∈ W) (hpq : p ≠ q) :
    anchor t p q x y =
      anchor (compressedCounts W) (compressLeaf W p) (compressLeaf W q)
        (compressLeaf W x) (compressLeaf W y) := by
  have heq (a b : Leaf) (ha : a ∈ W) (hb : b ∈ W) :
      compressLeaf W a = compressLeaf W b ↔ a = b :=
    ⟨compressLeaf_injective_on W ha hb, fun h => congrArg (compressLeaf W) h⟩
  simp only [anchor, heq x y hx hy, heq x p hx hp, heq x q hx hq,
    heq y p hy hp, heq y q hy hq]
  by_cases hxy : x = y
  · simp only [hxy, if_true]
  · simp only [hxy, if_false]
    by_cases hpair : (x = p ∧ y = q) ∨ (x = q ∧ y = p)
    · simp only [hpair, if_true]
    · simp only [hpair, if_false]
      by_cases hout : x = p ∨ x = q ∨ y = p ∨ y = q
      · simp only [hout, if_true]
      · simp only [hout, if_false]
        simp only [not_or] at hout
        exact rho2_compression t W hvalid x y p q hx hy hp hq
          hxy hout.1 hout.2.1 hout.2.2.1 hout.2.2.2 hpq

#print axioms quartet_compression
#print axioms rho2_compression
#print axioms anchor_compression
end Nanuq.Theta