import ThetaQuartetSymmetry
import AnchorComposition

namespace Nanuq.Theta

theorem quartet_swap_last (t : Counts) (s : Switching) (a b c d : Leaf) :
    quartet t s a b d c = (quartet t s a b c d).map Pairing.swapCross := by
  dsimp only [quartet]
  rw [treeDistance_comm t s d c]
  split_ifs <;> simp_all [Pairing.swapCross] <;> omega

theorem rho2_swap_last (t : Counts) (a b c d : Leaf) :
    rho2 t a b d c = rho2 t a b c d := by
  rw [rho2_option_eq, rho2_option_eq,
    quartet_swap_last t (false,false) a b c d,
    quartet_swap_last t (false,true) a b c d,
    quartet_swap_last t (true,false) a b c d,
    quartet_swap_last t (true,true) a b c d]
  exact optionRho2_swapCross _ _ _ _

theorem rhoFin_witness_symmetric (t : Counts) :
    Nanuq.Composition.WitnessSymmetric (rhoFin t) := by
  intro x y p q _ _ _ _
  exact congrArg (fun z : ℚ => z / 2) (rho2_swap_last t _ _ _ _).symm

#print axioms rhoFin_witness_symmetric

end Nanuq.Theta
