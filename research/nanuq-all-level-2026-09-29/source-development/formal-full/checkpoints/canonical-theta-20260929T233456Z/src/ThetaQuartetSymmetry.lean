import ThetaSourceExact
import WeightedProperties
import Mathlib.Data.Fintype.Option

namespace Nanuq.Theta

def Pairing.swapCross : Pairing → Pairing
  | .ab_cd => .ab_cd
  | .ac_bd => .ad_bc
  | .ad_bc => .ac_bd

instance : Fintype Pairing := ⟨{.ab_cd,.ac_bd,.ad_bc}, by intro p; cases p <;> simp⟩

def optionRho2 (rs : List (Option Pairing)) : ℚ := distinctRho2 (rs.filterMap id)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
/-- Swapping the cross resolutions is a bijection preserving the separation
indicator, including deduplication. All four abstract option values are checked. -/
theorem optionRho2_swapCross (r00 r01 r10 r11 : Option Pairing) :
    optionRho2 ([r00,r01,r10,r11].map fun r => r.map Pairing.swapCross) =
      optionRho2 [r00,r01,r10,r11] := by
  revert r00 r01 r10 r11
  decide +kernel

theorem quartet_swap_first (t : Counts) (s : Switching) (a b c d : Leaf) :
    quartet t s b a c d = (quartet t s a b c d).map Pairing.swapCross := by
  dsimp only [quartet]
  rw [treeDistance_comm t s b a]
  split_ifs <;> simp_all [Pairing.swapCross] <;> omega

theorem rho2_option_eq (t : Counts) (a b c d : Leaf) :
    rho2 t a b c d = optionRho2
      [quartet t (false,false) a b c d, quartet t (false,true) a b c d,
       quartet t (true,false) a b c d, quartet t (true,true) a b c d] := rfl

theorem rho2_swap_first (t : Counts) (a b c d : Leaf) :
    rho2 t b a c d = rho2 t a b c d := by
  rw [rho2_option_eq, rho2_option_eq,
    quartet_swap_first t (false,false) a b c d,
    quartet_swap_first t (false,true) a b c d,
    quartet_swap_first t (true,false) a b c d,
    quartet_swap_first t (true,true) a b c d]
  exact optionRho2_swapCross _ _ _ _

theorem rhoFin_swap_first (t : Counts) (a b c d : Fin (circular t).length) :
    rhoFin t b a c d = rhoFin t a b c d := by
  exact congrArg (fun z : ℚ => z / 2) (rho2_swap_first t _ _ _ _)

theorem rhoFin_endpoint_symmetric (t : Counts) :
    Nanuq.Weighted.QuartetEndpointSymmetric (rhoFin t) := by
  intro x y p q _ _ _ _
  exact (rhoFin_swap_first t x y p q).symm

#print axioms optionRho2_swapCross
#print axioms quartet_swap_first
#print axioms rhoFin_endpoint_symmetric
end Nanuq.Theta
