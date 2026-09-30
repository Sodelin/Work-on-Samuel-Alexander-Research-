import AnchorPortPatterns

namespace Nanuq.PortPatterns
open Nanuq.Weighted Nanuq.Composition

/-- An anchor entry is completely determined by the collision pattern unless
all four projected taxa remain distinct; that case keeps the local quartet. -/
theorem orderedAnchor_by_ports {n : Nat} (rho : QuartetData n) (f : Fin 4 → Fin n) :
    orderedAnchor rho (f 0) (f 1) (f 2) (f 3) =
      if portCount f = 4 then 2 * rho (f 2) (f 3) (f 0) (f 1)
      else if tripleCount f = 2 ∧ f 0 ≠ f 1 ∧ f 2 ≠ f 3 then 1 else 0 := by
  rw [tripleCount_explicit,portCount_explicit]
  unfold orderedAnchor anchorMatrix
  by_cases h01 : f 0 = f 1 <;> by_cases h02 : f 0 = f 2 <;>
    by_cases h03 : f 0 = f 3 <;> by_cases h12 : f 1 = f 2 <;>
    by_cases h13 : f 1 = f 3 <;> by_cases h23 : f 2 = f 3
  all_goals simp_all [eq_comm]

theorem orderedAnchor_zero_of_two_ports {n : Nat} (rho : QuartetData n)
    (f : Fin 4 → Fin n) (hports : portCount f ≤ 2) :
    orderedAnchor rho (f 0) (f 1) (f 2) (f 3) = 0 := by
  have h4 : portCount f ≠ 4 := by omega
  have h3 : portCount f ≠ 3 := by omega
  rw [orderedAnchor_by_ports,tripleCount_by_portCount]
  simp [h4,h3]

theorem orderedAnchor_one_of_three_ports {n : Nat} (rho : QuartetData n)
    (f : Fin 4 → Fin n) (hports : portCount f = 3)
    (ha : f 0 ≠ f 1) (hb : f 2 ≠ f 3) :
    orderedAnchor rho (f 0) (f 1) (f 2) (f 3) = 1 := by
  rw [orderedAnchor_by_ports,tripleCount_by_portCount]
  simp [hports,ha,hb]

#print axioms orderedAnchor_by_ports
#print axioms orderedAnchor_zero_of_two_ports
end Nanuq.PortPatterns