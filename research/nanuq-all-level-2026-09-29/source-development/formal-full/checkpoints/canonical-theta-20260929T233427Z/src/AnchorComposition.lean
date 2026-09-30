import SourceCompositionBridge

/-!
Direct composition through anchor matrices. The graph-level anchor identity is
an explicit remaining premise. This file proves the full mass-counting step,
including arbitrary initial taxon weights and different port counts per blob.
-/
namespace Nanuq.Composition

open scoped BigOperators
open Nanuq.Weighted

variable {n : Nat}

/-- Repeated anchors contribute zero to an ordered anchor sum. -/
def orderedAnchor (rho : QuartetData n) (p q x y : Fin n) : ℚ :=
  if p = q then 0 else anchorMatrix rho p q x y

@[simp] theorem orderedAnchor_repeated (rho : QuartetData n) (p x y : Fin n) :
    orderedAnchor rho p p x y = 0 := by simp [orderedAnchor]

theorem orderedAnchor_symmetric (rho : QuartetData n) (hsym : WitnessSymmetric rho)
    (p q x y : Fin n) : orderedAnchor rho p q x y = orderedAnchor rho q p x y := by
  by_cases hpq : p = q
  · subst q; rfl
  by_cases hxy : x = y
  · subst y; simp [orderedAnchor]
  by_cases hxp : x = p <;> by_cases hxq : x = q <;>
    by_cases hyp : y = p <;> by_cases hyq : y = q <;>
    simp_all [orderedAnchor, anchorMatrix, Ne.symm hpq]
  rw [hsym x y p q hxy hpq ⟨Ne.symm hxp, Ne.symm hyp⟩
    ⟨Ne.symm hxq, Ne.symm hyq⟩]

theorem weightedNanuq_eq_ordered_anchor (rho : QuartetData n)
    (hsym : WitnessSymmetric rho) (m : Fin n → ℚ) (x y : Fin n) :
    weightedNanuq rho m x y =
      (∑ p, ∑ q, m p * m q * orderedAnchor rho p q x y) / 2 := by
  rw [ordered_pair_sum_eq_twice_upperSum _
    (fun p q => by rw [orderedAnchor_symmetric rho hsym, mul_comm (m p) (m q)])
    (fun p => by simp)]
  have hupper : upperSum (fun p q => m p * m q * orderedAnchor rho p q x y) =
      upperSum (fun p q => m p * m q * anchorMatrix rho p q x y) := by
    unfold upperSum
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    by_cases hpq : p < q
    · simp [hpq, orderedAnchor, ne_of_lt hpq]
    · simp [hpq]
  rw [hupper, ← weightedNanuq_eq_anchor_sum]
  ring

variable {X P : Type*} [Fintype X] [DecidableEq X] [Fintype P] [DecidableEq P]

def weightedPortMass (project : X → P) (m : X → ℚ) (p : P) : ℚ :=
  ∑ x ∈ Finset.univ.filter (fun x => project x = p), m x

theorem weightedPortMass_unit (project : X → P) :
    weightedPortMass project (fun _ => 1) = portMass project := by
  funext p
  simp [weightedPortMass, portMass]

theorem sum_weighted_by_ports (project : X → P) (m : X → ℚ) (f : P → ℚ) :
    (∑ x, m x * f (project x)) = ∑ p, weightedPortMass project m p * f p := by
  simp only [weightedPortMass, Finset.sum_mul, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp

theorem sum_weighted_pairs_by_ports (project : X → P) (m : X → ℚ)
    (f : P → P → ℚ) :
    (∑ x, ∑ y, m x * m y * f (project x) (project y)) =
      ∑ p, ∑ q, weightedPortMass project m p * weightedPortMass project m q * f p q := by
  simp_rw [mul_assoc, ← Finset.mul_sum]
  rw [sum_weighted_by_ports project m (fun p => ∑ y, m y * f p (project y))]
  simp_rw [sum_weighted_by_ports project m]

variable {B : Type*} [Fintype B]

/-- The single remaining hypothesis here is a concrete graph identity for each
anchor entry. No switching-average or separate discrepancy identity is needed. -/
theorem weighted_composition_of_anchor_identity
    (k : B → Nat) (rho : QuartetData n) (localRho : ∀ b, QuartetData (k b))
    (hsym : WitnessSymmetric rho) (hlocalSym : ∀ b, WitnessSymmetric (localRho b))
    (project : ∀ b, Fin n → Fin (k b))
    (hanchor : ∀ p q x y, orderedAnchor rho p q x y =
      ∑ b, orderedAnchor (localRho b) (project b p) (project b q) (project b x) (project b y))
    (m : Fin n → ℚ) (x y : Fin n) :
    weightedNanuq rho m x y =
      ∑ b, weightedNanuq (localRho b) (weightedPortMass (project b) m)
        (project b x) (project b y) := by
  rw [weightedNanuq_eq_ordered_anchor rho hsym]
  simp_rw [hanchor, Finset.mul_sum]
  rw [Finset.sum_comm_cycle]
  rw [div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b _
  rw [sum_weighted_pairs_by_ports (project b) m
    (fun p q => orderedAnchor (localRho b) p q (project b x) (project b y))]
  simpa only [div_eq_mul_inv] using
    (weightedNanuq_eq_ordered_anchor (localRho b) (hlocalSym b) _ _ _).symm

theorem source_composition_of_anchor_identity
    (k : B → Nat) (rho : QuartetData n) (localRho : ∀ b, QuartetData (k b))
    (hsym : WitnessSymmetric rho) (hlocalSym : ∀ b, WitnessSymmetric (localRho b))
    (project : ∀ b, Fin n → Fin (k b))
    (hanchor : ∀ p q x y, orderedAnchor rho p q x y =
      ∑ b, orderedAnchor (localRho b) (project b p) (project b q) (project b x) (project b y))
    (x y : Fin n) :
    sourceNanuq rho x y =
      ∑ b, weightedNanuq (localRho b) (portMass (project b)) (project b x) (project b y) := by
  rw [← weightedNanuq_unit_eq_source]
  rw [weighted_composition_of_anchor_identity k rho localRho hsym hlocalSym project hanchor]
  simp_rw [weightedPortMass_unit]

#print axioms weightedNanuq_eq_ordered_anchor
#print axioms sum_weighted_pairs_by_ports
#print axioms weighted_composition_of_anchor_identity
#print axioms source_composition_of_anchor_identity

end Nanuq.Composition
