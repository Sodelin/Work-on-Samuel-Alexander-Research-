import AnchorUnboundedTheorem
import ThetaSourceUnbounded
import ThetaWitnessSymmetry
import WeightedRestriction

/-! Exact weighted circularity for every ordered subset of canonical theta taxa.
Deleted taxa receive zero mass before restriction; retaining the unit masses
of deleted taxa would give a different NANUQ formula. -/
namespace Nanuq.Theta

open Nanuq.Weighted Nanuq.Composition Nanuq.Reconstruction
variable {n : Nat}

theorem restricted_theta_weighted_circular (t : Counts)
    (f : Fin n → Fin (circular t).length) (hf : StrictMono f)
    (mass : Fin n → ℚ) (hm : ∀ x, 0 ≤ mass x) :
    CircularDecomposable (weightedNanuq (pullbackRho f (rhoFin t)) mass) := by
  apply weighted_circular_restriction f hf (rhoFin t) (rhoFin_witness_symmetric t) mass
  exact unbounded_weighted_circular t _ (weightedPortMass_nonneg f mass hm)

theorem restricted_theta_source_circular (t : Counts)
    (f : Fin n → Fin (circular t).length) (hf : StrictMono f) :
    CircularDecomposable (sourceNanuq (pullbackRho f (rhoFin t))) := by
  rw [← weightedNanuq_unit_eq_source]
  exact restricted_theta_weighted_circular t f hf (fun _ => 1) (fun _ => by decide)

#print axioms restricted_theta_weighted_circular
#print axioms restricted_theta_source_circular

end Nanuq.Theta
