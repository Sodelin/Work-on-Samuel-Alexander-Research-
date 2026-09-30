import AnchorComposition
import CircularRestriction

/-! Exact weighted taxon restriction by zero extension of the masses. -/
namespace Nanuq.Composition

open Nanuq.Weighted Nanuq.Reconstruction
variable {n m : Nat}

def pullbackRho (f : Fin n → Fin m) (rho : QuartetData m) : QuartetData n :=
  fun x y p q => rho (f x) (f y) (f p) (f q)

theorem pullbackRho_symmetric (f : Fin n → Fin m) (hf : Function.Injective f)
    (rho : QuartetData m) (hsym : WitnessSymmetric rho) :
    WitnessSymmetric (pullbackRho f rho) := by
  intro x y p q hxy hpq hp hq
  exact hsym _ _ _ _ (fun h => hxy (hf h)) (fun h => hpq (hf h))
    ⟨fun h => hp.1 (hf h), fun h => hp.2 (hf h)⟩
    ⟨fun h => hq.1 (hf h), fun h => hq.2 (hf h)⟩

theorem orderedAnchor_pullback (f : Fin n → Fin m) (hf : Function.Injective f)
    (rho : QuartetData m) (p q x y : Fin n) :
    orderedAnchor (pullbackRho f rho) p q x y =
      orderedAnchor rho (f p) (f q) (f x) (f y) := by
  have he (a b : Fin n) : f a = f b ↔ a = b := ⟨fun h => hf h, congrArg f⟩
  simp only [orderedAnchor, anchorMatrix, pullbackRho, he]

theorem weightedPortMass_nonneg {X P : Type*} [Fintype X] [DecidableEq X]
    [Fintype P] [DecidableEq P] (f : X → P) (mass : X → ℚ)
    (hm : ∀ x, 0 ≤ mass x) (p : P) : 0 ≤ weightedPortMass f mass p :=
  Finset.sum_nonneg (fun x _ => hm x)

theorem weightedNanuq_restriction (f : Fin n → Fin m) (hf : Function.Injective f)
    (rho : QuartetData m) (hsym : WitnessSymmetric rho)
    (mass : Fin n → ℚ) (x y : Fin n) :
    weightedNanuq (pullbackRho f rho) mass x y =
      weightedNanuq rho (weightedPortMass f mass) (f x) (f y) := by
  rw [weightedNanuq_eq_ordered_anchor _ (pullbackRho_symmetric f hf rho hsym),
    weightedNanuq_eq_ordered_anchor _ hsym]
  simp_rw [orderedAnchor_pullback f hf rho]
  rw [sum_weighted_pairs_by_ports f mass (fun p q => orderedAnchor rho p q (f x) (f y))]

theorem weighted_circular_restriction (f : Fin n → Fin m) (hf : StrictMono f)
    (rho : QuartetData m) (hsym : WitnessSymmetric rho)
    (mass : Fin n → ℚ)
    (hcircular : CircularDecomposable (weightedNanuq rho (weightedPortMass f mass))) :
    CircularDecomposable (weightedNanuq (pullbackRho f rho) mass) := by
  have heq : weightedNanuq (pullbackRho f rho) mass =
      fun x y => weightedNanuq rho (weightedPortMass f mass) (f x) (f y) := by
    funext x y
    exact weightedNanuq_restriction f hf.injective rho hsym mass x y
  rw [heq]
  exact circular_decomposable_restriction _ hcircular f hf

#print axioms weightedNanuq_restriction
#print axioms weighted_circular_restriction

end Nanuq.Composition
