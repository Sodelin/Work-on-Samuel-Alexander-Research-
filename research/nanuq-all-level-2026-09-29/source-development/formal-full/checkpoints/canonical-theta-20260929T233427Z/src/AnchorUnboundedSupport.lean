import AnchorUnboundedTheorem
import CircularSupportCompression
import ThetaCompressedSurjective

/-! Exact displayed-edge support for arbitrary canonical theta arm lengths.
The finite support witnesses are transported through proved order, quartet,
anchor, and actual-edge support compression, in both directions. -/
namespace Nanuq.Theta
open Nanuq.Weighted Nanuq.Reconstruction

theorem alpha_compression_indexed (t : Counts) (W : Finset Leaf)
    (hvalid : ∀ l ∈ W, l ∈ circular t) (hc1 : Leaf.c1 ∈ W) (hc2 : Leaf.c2 ∈ W)
    (p q i j : Fin (circular t).length)
    (hp : leafIndex t p ∈ W) (hq : leafIndex t q ∈ W)
    (hi : leafIndex t i ∈ W) (hj : leafIndex t j ∈ W)
    (hin : leafIndex t (cyclicNext i) ∈ W) (hjn : leafIndex t (cyclicNext j) ∈ W)
    (hpq : p < q) :
    alpha t p.val q.val i.val j.val =
      alpha (compressedCounts W)
        (compressedIndex t W hvalid hc1 hc2 p hp).val
        (compressedIndex t W hvalid hc1 hc2 q hq).val
        (compressedIndex t W hvalid hc1 hc2 i hi).val
        (compressedIndex t W hvalid hc1 hc2 j hj).val := by
  have hpqLeaf : leafIndex t p ≠ leafIndex t q :=
    fun h => (ne_of_lt hpq) (leafIndex_injective t h)
  exact alpha_preserved_under_compression t W hvalid hc1 hc2 p q i j hp hq hi hj hin hjn
    (fun a ha b hb => anchor_compression t W hvalid _ _ a b hp hq ha hb hpqLeaf)

/-- A circular split of an arbitrary theta is displayed precisely when some
actual anchor coefficient is positive. The two-leaf degenerate theta is
explicitly excluded by `hlo`, as its source matrix is zero. -/
theorem unbounded_support_exact (t : Counts) (hlo : 1 ≤ t.total)
    (i j : Fin (circular t).length) (hij : i < j) :
    displayedSplit t i.val j.val = true ↔
      ∃ p q : Fin (circular t).length, p < q ∧ 0 < alpha t p.val q.val i.val j.val := by
  have hlen : 3 ≤ (circular t).length := by rw [circular_length]; omega
  constructor
  · intro hsplit
    let W := retainedWitnesses t i j i j
    have hvalid : ∀ l ∈ W, l ∈ circular t :=
      fun _ hl => retainedWitnesses_subset_circular t i j i j hl
    have hc1 : Leaf.c1 ∈ W := by simp [W,retainedWitnesses]
    have hc2 : Leaf.c2 ∈ W := by simp [W,retainedWitnesses]
    have hi : leafIndex t i ∈ W := by simp [W,retainedWitnesses,sixWitnesses]
    have hj : leafIndex t j ∈ W := by simp [W,retainedWitnesses,sixWitnesses]
    have hin : leafIndex t (cyclicNext i) ∈ W := by simp [W,retainedWitnesses,sixWitnesses]
    have hjn : leafIndex t (cyclicNext j) ∈ W := by simp [W,retainedWitnesses,sixWitnesses]
    let ci := compressedIndex t W hvalid hc1 hc2 i hi
    let cj := compressedIndex t W hvalid hc1 hc2 j hj
    have hcij : ci < cj := compressedIndex_strictMono t W hvalid hc1 hc2 i j hi hj hij
    have huLo : 1 ≤ (compressedCounts W).total := compressed_retained_total_pos t hlen i j i j hij
    have huHi : (compressedCounts W).total ≤ 6 := compressed_retained_total_le t i j i j
    have hcompressed := (displayedSplit_compression t W hvalid hc1 hc2 i j hi hj hin hjn hij).mp hsplit
    obtain ⟨p',q',hpq',hq',hpos'⟩ :=
      (bounded_support_exact (compressedCounts W) huLo huHi hcij cj.isLt).mp hcompressed
    let fp : Fin (circular (compressedCounts W)).length := ⟨p',lt_trans hpq' hq'⟩
    let fq : Fin (circular (compressedCounts W)).length := ⟨q',hq'⟩
    obtain ⟨p,hp,hpe⟩ := compressedIndex_surjective t W hvalid hc1 hc2 fp
    obtain ⟨q,hq,hqe⟩ := compressedIndex_surjective t W hvalid hc1 hc2 fq
    have hpq : p < q := (compressedIndex_lt_iff t W hvalid hc1 hc2 p q hp hq).mp
      (by rw [hpe,hqe]; exact hpq')
    refine ⟨p,q,hpq,?_⟩
    rw [alpha_compression_indexed t W hvalid hc1 hc2 p q i j hp hq hi hj hin hjn hpq,
      hpe,hqe]
    exact hpos'
  · rintro ⟨p,q,hpq,hpos⟩
    let W := retainedWitnesses t p q i j
    have hvalid : ∀ l ∈ W, l ∈ circular t :=
      fun _ hl => retainedWitnesses_subset_circular t p q i j hl
    have hc1 : Leaf.c1 ∈ W := by simp [W,retainedWitnesses]
    have hc2 : Leaf.c2 ∈ W := by simp [W,retainedWitnesses]
    have hp : leafIndex t p ∈ W := by simp [W,retainedWitnesses,sixWitnesses]
    have hq : leafIndex t q ∈ W := by simp [W,retainedWitnesses,sixWitnesses]
    have hi : leafIndex t i ∈ W := by simp [W,retainedWitnesses,sixWitnesses]
    have hj : leafIndex t j ∈ W := by simp [W,retainedWitnesses,sixWitnesses]
    have hin : leafIndex t (cyclicNext i) ∈ W := by simp [W,retainedWitnesses,sixWitnesses]
    have hjn : leafIndex t (cyclicNext j) ∈ W := by simp [W,retainedWitnesses,sixWitnesses]
    let cp := compressedIndex t W hvalid hc1 hc2 p hp
    let cq := compressedIndex t W hvalid hc1 hc2 q hq
    let ci := compressedIndex t W hvalid hc1 hc2 i hi
    let cj := compressedIndex t W hvalid hc1 hc2 j hj
    have hcpq : cp < cq := compressedIndex_strictMono t W hvalid hc1 hc2 p q hp hq hpq
    have hcij : ci < cj := compressedIndex_strictMono t W hvalid hc1 hc2 i j hi hj hij
    have huLo : 1 ≤ (compressedCounts W).total := compressed_retained_total_pos t hlen p q i j hij
    have huHi : (compressedCounts W).total ≤ 6 := compressed_retained_total_le t p q i j
    apply (displayedSplit_compression t W hvalid hc1 hc2 i j hi hj hin hjn hij).mpr
    apply (bounded_support_exact (compressedCounts W) huLo huHi hcij cj.isLt).mpr
    refine ⟨cp.val,cq.val,hcpq,cq.isLt,?_⟩
    rw [← alpha_compression_indexed t W hvalid hc1 hc2 p q i j hp hq hi hj hin hjn hpq]
    exact hpos

theorem unbounded_weighted_exact_support (t : Counts) (hlo : 1 ≤ t.total)
    (m : Fin (circular t).length → ℚ) (hm : ∀ x, 0 < m x)
    (i j : Fin (circular t).length) (hij : i < j) :
    0 < circularAlpha (weightedNanuq (rhoFin t) m) i j ↔
      displayedSplit t i.val j.val = true := by
  rw [circularAlpha_weightedNanuq_pos_iff (rhoFin t) m hm i j
    (fun p q hpq => unbounded_metric_anchor_nonnegative t p q i j hpq hij),
    unbounded_support_exact t hlo i j hij]
  simp only [weighted_alpha_eq_alpha]

theorem unbounded_source_exact_support (t : Counts) (hlo : 1 ≤ t.total)
    (i j : Fin (circular t).length) (hij : i < j) :
    0 < circularAlpha (sourceNanuq (rhoFin t)) i j ↔
      displayedSplit t i.val j.val = true := by
  rw [← weightedNanuq_unit_eq_source]
  exact unbounded_weighted_exact_support t hlo (fun _ => 1) (fun _ => by decide) i j hij

/-- Full local canonical-theta theorem, with arbitrary arm lengths and exact
support from actual switching edges, in the source's uniform-distinct metric. -/
theorem unbounded_source_full_theorem (t : Counts) (hlo : 1 ≤ t.total) :
    CircularDecomposable (sourceNanuq (rhoFin t)) ∧
    PseudometricLaws (sourceNanuq (rhoFin t)) ∧
    (∀ x y, x ≠ y → 0 < sourceNanuq (rhoFin t) x y) ∧
    (∀ i j, i < j → (0 < circularAlpha (sourceNanuq (rhoFin t)) i j ↔
      displayedSplit t i.val j.val = true)) := by
  refine ⟨unbounded_source_circular t, ?_, bounded_source_positive t hlo,
    unbounded_source_exact_support t hlo⟩
  exact circular_decomposable_pseudometric _ (unbounded_source_circular t)

#print axioms unbounded_support_exact
#print axioms unbounded_weighted_exact_support
#print axioms unbounded_source_full_theorem
end Nanuq.Theta
