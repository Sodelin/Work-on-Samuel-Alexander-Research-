import ThetaCompression
import AnchorReduction
import BoundedThetaTheorem

/-!
Unconditional arbitrary-arm anchor nonnegativity and circular decomposability
for the concrete canonical theta evaluator. Compression preservation, index
transport, and the complete finite certificate are all proved dependencies.
This theorem does not assert the remaining general network-class graph bridge.
-/
namespace Nanuq.Theta

open Nanuq.Weighted Nanuq.Reconstruction

theorem unbounded_anchor_nonnegative (t : Counts)
    (p q i j : Fin (circular t).length) (hpq : p < q) (hij : i < j) :
    0 ≤ alpha t p.val q.val i.val j.val := by
  apply alpha_nonnegative_of_anchor_compression t
  · intro W hvalid _ _ a ha b hb hab x hx y hy
    exact anchor_compression t W hvalid a b x y ha hb hx hy hab
  · exact hpq
  · exact hij

theorem unbounded_metric_anchor_nonnegative (t : Counts)
    (p q i j : Fin (circular t).length) (hpq : p < q) (hij : i < j) :
    0 ≤ circularAlpha (anchorMatrix (rhoFin t) p q) i j := by
  rw [weighted_alpha_eq_alpha]
  exact unbounded_anchor_nonnegative t p q i j hpq hij

theorem unbounded_weighted_circular (t : Counts)
    (m : Fin (circular t).length → ℚ) (hm : ∀ x, 0 ≤ m x) :
    CircularDecomposable (weightedNanuq (rhoFin t) m) := by
  apply circular_decomposable_of_coefficients
  · exact weightedNanuq_symmetric _ _ (rhoFin_endpoint_symmetric t)
  · exact weightedNanuq_diag _ _
  · intro i j hij
    exact circularAlpha_weightedNanuq_nonneg _ _ hm i j
      (fun p q hpq => unbounded_metric_anchor_nonnegative t p q i j hpq hij)

theorem unbounded_weighted_pseudometric (t : Counts)
    (m : Fin (circular t).length → ℚ) (hm : ∀ x, 0 ≤ m x) :
    PseudometricLaws (weightedNanuq (rhoFin t) m) :=
  circular_decomposable_pseudometric _ (unbounded_weighted_circular t m hm)

theorem unbounded_source_circular (t : Counts) :
    CircularDecomposable (sourceNanuq (rhoFin t)) := by
  rw [← weightedNanuq_unit_eq_source]
  exact unbounded_weighted_circular t (fun _ => 1) (fun _ => by decide)

theorem unbounded_weighted_support_matches_source (t : Counts)
    (m : Fin (circular t).length → ℚ) (hm : ∀ x, 0 < m x)
    (i j : Fin (circular t).length) (hij : i < j) :
    0 < circularAlpha (weightedNanuq (rhoFin t) m) i j ↔
      0 < circularAlpha (sourceNanuq (rhoFin t)) i j := by
  exact positive_masses_source_support (rhoFin t) m hm i j
    (fun p q hpq => unbounded_metric_anchor_nonnegative t p q i j hpq hij)

theorem unbounded_source_theorem (t : Counts) (hlo : 1 ≤ t.total) :
    CircularDecomposable (sourceNanuq (rhoFin t)) ∧
    PseudometricLaws (sourceNanuq (rhoFin t)) ∧
    (∀ x y, x ≠ y → 0 < sourceNanuq (rhoFin t) x y) := by
  exact ⟨unbounded_source_circular t,
    circular_decomposable_pseudometric _ (unbounded_source_circular t),
    bounded_source_positive t hlo⟩

#print axioms unbounded_anchor_nonnegative
#print axioms unbounded_weighted_circular
#print axioms unbounded_source_theorem
#print axioms unbounded_weighted_support_matches_source

end Nanuq.Theta

