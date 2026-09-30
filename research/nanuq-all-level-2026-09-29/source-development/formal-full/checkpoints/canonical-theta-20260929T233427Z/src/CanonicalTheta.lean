import AnchorUnboundedSupport
import ThetaSourceUnbounded
import ThetaTaxonRestriction

/-!
Public entry point for the completed LOCAL canonical theta theorem.

All four arm lengths are arbitrary natural numbers. The tensor is the exact
uniform average over distinct displayed quartet resolutions. Its displayed
split support is computed from actual edges of the four switching trees.

This file does not assert that every raw level-two blob has this canonical
form, or that the global source metric composes over actual blob projections.
Those are separate remaining graph obligations in OBLIGATIONS.md.
-/
namespace Nanuq.Canonical

open Nanuq.Theta Nanuq.Weighted Nanuq.Reconstruction

theorem theta_source (t : Counts) (hsize : 1 ≤ t.total) :
    CircularDecomposable (sourceNanuq (rhoFin t)) ∧
    PseudometricLaws (sourceNanuq (rhoFin t)) ∧
    (∀ x y, x ≠ y → 0 < sourceNanuq (rhoFin t) x y) ∧
    (∀ i j, i < j → (0 < circularAlpha (sourceNanuq (rhoFin t)) i j ↔
      displayedSplit t i.val j.val = true)) :=
  unbounded_source_full_theorem t hsize

theorem theta_weighted (t : Counts) (hsize : 1 ≤ t.total)
    (mass : Fin (circular t).length → ℚ) (hm : ∀ x, 0 < mass x) :
    CircularDecomposable (weightedNanuq (rhoFin t) mass) ∧
    PseudometricLaws (weightedNanuq (rhoFin t) mass) ∧
    (∀ i j, i < j → (0 < circularAlpha (weightedNanuq (rhoFin t) mass) i j ↔
      displayedSplit t i.val j.val = true)) :=
  ⟨unbounded_weighted_circular t mass (fun x => le_of_lt (hm x)),
   unbounded_weighted_pseudometric t mass (fun x => le_of_lt (hm x)),
   unbounded_weighted_exact_support t hsize mass hm⟩

theorem theta_exact_quartet_mean (t : Counts)
    (a b c d : Fin (circular t).length)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    rhoFin t a b c d = Nanuq.Quartet.sourceMean
      (sourceResolution t (leafIndex t a) (leafIndex t b) (leafIndex t c) (leafIndex t d)) :=
  rhoFin_source t a b c d hab hac had hbc hbd hcd

#print axioms theta_source
#print axioms theta_weighted
#print axioms theta_exact_quartet_mean

end Nanuq.Canonical
