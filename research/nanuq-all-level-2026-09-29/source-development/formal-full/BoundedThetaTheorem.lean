import ThetaCertificate
import ThetaSupportCertificate
import ThetaQuartetSymmetry
import ThetaSourceExact
import AnchorThetaBridge
import CircularDecomposition
import WeightedProperties
import Mathlib.Tactic.Positivity

/-!
A complete formal theorem for the canonical theta evaluator with 1..6 ordinary
arm leaves (the 209 templates in the finite reduction). This file actually
assembles the independent finite certificate, source-average semantics, weighted
formula, circular reconstruction, metric laws, and exact displayed-split support.

This is not yet the arbitrary-arm or arbitrary-multi-blob source-network theorem:
the corresponding compression, classification, and graph-composition bridges
are additional named obligations in OBLIGATIONS.md.
-/

namespace Nanuq.Theta

open Nanuq.Weighted Nanuq.Reconstruction

theorem rhoFin_nonneg (t : Counts) (a b c d : Fin (circular t).length) :
    0 ≤ rhoFin t a b c d := by
  unfold rhoFin rho2
  dsimp
  positivity

theorem bounded_metric_anchor_nonnegative (t : Counts)
    (hlo : 1 ≤ t.total) (hhi : t.total ≤ 6)
    (p q i j : Fin (circular t).length) (hpq : p < q) (hij : i < j) :
    0 ≤ circularAlpha (anchorMatrix (rhoFin t) p q) i j := by
  rw [weighted_alpha_eq_alpha]
  exact bounded_anchor_nonnegative t hlo hhi hpq q.isLt hij j.isLt

theorem bounded_weighted_circular (t : Counts)
    (hlo : 1 ≤ t.total) (hhi : t.total ≤ 6)
    (m : Fin (circular t).length → ℚ) (hm : ∀ x, 0 ≤ m x) :
    CircularDecomposable (weightedNanuq (rhoFin t) m) := by
  apply circular_decomposable_of_coefficients
  · exact weightedNanuq_symmetric _ _ (rhoFin_endpoint_symmetric t)
  · exact weightedNanuq_diag _ _
  · intro i j hij
    exact circularAlpha_weightedNanuq_nonneg _ _ hm i j
      (fun p q hpq => bounded_metric_anchor_nonnegative t hlo hhi p q i j hpq hij)

theorem bounded_weighted_pseudometric (t : Counts)
    (hlo : 1 ≤ t.total) (hhi : t.total ≤ 6)
    (m : Fin (circular t).length → ℚ) (hm : ∀ x, 0 ≤ m x) :
    PseudometricLaws (weightedNanuq (rhoFin t) m) :=
  circular_decomposable_pseudometric _ (bounded_weighted_circular t hlo hhi m hm)

/-- Exact support uses the edges of the four executable switching trees.
The published unit-mass support theorem is not a premise. -/
theorem bounded_weighted_exact_support (t : Counts)
    (hlo : 1 ≤ t.total) (hhi : t.total ≤ 6)
    (m : Fin (circular t).length → ℚ) (hm : ∀ x, 0 < m x)
    (i j : Fin (circular t).length) (hij : i < j) :
    0 < circularAlpha (weightedNanuq (rhoFin t) m) i j ↔
      displayedSplit t i.val j.val = true := by
  have hanchor := circularAlpha_weightedNanuq_pos_iff (rhoFin t) m hm i j
    (fun p q hpq => bounded_metric_anchor_nonnegative t hlo hhi p q i j hpq hij)
  have hsupport := bounded_support_exact t hlo hhi (i := i.val) (j := j.val) hij j.isLt
  rw [hanchor]
  constructor
  · rintro ⟨p, q, hpq, hpos⟩
    apply hsupport.mpr
    refine ⟨p.val, q.val, hpq, q.isLt, ?_⟩
    rw [← weighted_alpha_eq_alpha t p q i j]
    exact hpos
  · intro hsplit
    obtain ⟨p, q, hpq, hq, hpos⟩ := hsupport.mp hsplit
    let fp : Fin (circular t).length := ⟨p, lt_trans hpq hq⟩
    let fq : Fin (circular t).length := ⟨q, hq⟩
    refine ⟨fp, fq, hpq, ?_⟩
    rw [weighted_alpha_eq_alpha]
    exact hpos

theorem bounded_source_circular (t : Counts)
    (hlo : 1 ≤ t.total) (hhi : t.total ≤ 6) :
    CircularDecomposable (sourceNanuq (rhoFin t)) := by
  rw [← weightedNanuq_unit_eq_source]
  exact bounded_weighted_circular t hlo hhi (fun _ => 1) (fun _ => by decide)

theorem bounded_source_positive (t : Counts)
    (hlo : 1 ≤ t.total) (x y : Fin (circular t).length) (hxy : x ≠ y) :
    0 < sourceNanuq (rhoFin t) x y := by
  have hn : 3 ≤ (circular t).length := by
    rw [circular_length]
    omega
  exact sourceNanuq_pos_of_three_le (rhoFin t) hn x y hxy
    (fun p q _ _ _ => rhoFin_nonneg t x y p q)

theorem bounded_source_exact_support (t : Counts)
    (hlo : 1 ≤ t.total) (hhi : t.total ≤ 6)
    (i j : Fin (circular t).length) (hij : i < j) :
    0 < circularAlpha (sourceNanuq (rhoFin t)) i j ↔
      displayedSplit t i.val j.val = true := by
  rw [← weightedNanuq_unit_eq_source]
  exact bounded_weighted_exact_support t hlo hhi (fun _ => 1) (fun _ => by decide) i j hij

/-- All conclusions for every bounded canonical template, not just an abstract
conditional positivity transfer. The final graph-class theorem remains separate. -/
theorem bounded_source_theorem (t : Counts)
    (hlo : 1 ≤ t.total) (hhi : t.total ≤ 6) :
    CircularDecomposable (sourceNanuq (rhoFin t)) ∧
    PseudometricLaws (sourceNanuq (rhoFin t)) ∧
    (∀ x y, x ≠ y → 0 < sourceNanuq (rhoFin t) x y) ∧
    (∀ i j, i < j → (0 < circularAlpha (sourceNanuq (rhoFin t)) i j ↔
      displayedSplit t i.val j.val = true)) := by
  refine ⟨bounded_source_circular t hlo hhi, ?_, bounded_source_positive t hlo, ?_⟩
  · exact circular_decomposable_pseudometric _ (bounded_source_circular t hlo hhi)
  · exact bounded_source_exact_support t hlo hhi

/-- The quartet tensor in that source formula is literally the uniform mean
over distinct quartet resolutions of the four switchings, for any label order. -/
theorem bounded_source_tensor (t : Counts)
    (hlo : 1 ≤ t.total) (hhi : t.total ≤ 6)
    (a b c d : Fin (circular t).length)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    rhoFin t a b c d = Nanuq.Quartet.sourceMean
      (sourceResolution t (leafIndex t a) (leafIndex t b) (leafIndex t c) (leafIndex t d)) :=
  rhoFin_source_of_checked (bounded_quartets_checked t hlo hhi) a b c d hab hac had hbc hbd hcd

#print axioms bounded_weighted_circular
#print axioms bounded_weighted_exact_support
#print axioms bounded_source_theorem
#print axioms bounded_source_tensor

end Nanuq.Theta
