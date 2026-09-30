import ThetaFiniteSoundness
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.NormNum

namespace Nanuq.Theta

/-- Distance between two pendant leaves attached at positive positions on the
four arms of the H-tree. The central edge joins even to odd arm tags. -/
def hDistance (k r : Fin 4) (m n : Nat) : Nat :=
  if k = r then (m - n) + (n - m) + 2
  else m + n + 2 + (if k.val % 2 = r.val % 2 then 0 else 1)

def tailPair (ka kb kc kd : Fin 4) (a b c d : Nat) : Prop :=
  ka = kb ∧ (kc ≠ ka ∨ (c < a ∧ c < b)) ∧ (kd ≠ ka ∨ (d < a ∧ d < b))

def centralPair (ka kb kc kd : Fin 4) : Prop :=
  ka.val % 2 = kb.val % 2 ∧ kc.val % 2 = kd.val % 2 ∧ ka.val % 2 ≠ kc.val % 2

def hPairCut (ka kb kc kd : Fin 4) (a b c d : Nat) : Prop :=
  tailPair ka kb kc kd a b c d ∨ tailPair kc kd ka kb c d a b ∨ centralPair ka kb kc kd

set_option maxHeartbeats 2000000 in
/-- A strict four-point minimum is exactly an arm-tail cut or the central cut.
Positions are arbitrary naturals, so this is not a bounded-leaf computation. -/
theorem hDistance_pair_cut (ka kb kc kd : Fin 4) (a b c d : Nat)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    (hDistance ka kb a b + hDistance kc kd c d <
        hDistance ka kc a c + hDistance kb kd b d ∧
      hDistance ka kb a b + hDistance kc kd c d <
        hDistance ka kd a d + hDistance kb kc b c) ↔
      hPairCut ka kb kc kd a b c d := by
  fin_cases ka <;> fin_cases kb <;> fin_cases kc <;> fin_cases kd
  all_goals norm_num [hDistance, hPairCut, tailPair, centralPair]
  all_goals omega

#print axioms hDistance_pair_cut
end Nanuq.Theta
