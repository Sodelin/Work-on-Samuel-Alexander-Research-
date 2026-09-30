import WeightedCoefficients
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Two- and three-port cases, below the four-taxon scope of the source theorem. -/
namespace Nanuq.Weighted

theorem weightedNanuq_two_zero (rho : QuartetData 2) (m : Fin 2 → ℚ) :
    weightedNanuq rho m = fun _ _ => 0 := by
  funext x y
  fin_cases x <;> fin_cases y <;>
    norm_num [weightedNanuq, outside, Fin.sum_univ_succ]

/-- Length of the pendant edge at i in the three-port star. -/
def threePortLength (m : Fin 3 → ℚ) (i : Fin 3) : ℚ :=
  m (cyclicNext i) * m (cyclicNext (cyclicNext i))

/-- Every three-port weighted matrix is an explicit star metric, independently
of quartet input because no four distinct taxa exist. -/
theorem weightedNanuq_three_star (rho : QuartetData 3) (m : Fin 3 → ℚ) :
    weightedNanuq rho m =
      fun x y => if x = y then 0 else threePortLength m x + threePortLength m y := by
  funext x y
  fin_cases x <;> fin_cases y <;>
    simp +decide [weightedNanuq, outside, Fin.sum_univ_succ, threePortLength, cyclicNext] <;>
    ring

theorem threePortLength_pos (m : Fin 3 → ℚ) (hm : ∀ i, 0 < m i) (i : Fin 3) :
    0 < threePortLength m i := by
  exact mul_pos (hm _) (hm _)

#print axioms weightedNanuq_two_zero
#print axioms weightedNanuq_three_star
#print axioms threePortLength_pos

end Nanuq.Weighted




