import QuartetSemantics

/-! With two switchings, uniform-distinct-quartet averaging agrees exactly with
the switching average, including the case where both switchings display the
same quartet. This is the normalization step for level-one local networks. -/
namespace Nanuq.Quartet

def twoChoices (a b : Resolution) : Bool → Resolution := fun s => if s then b else a

theorem twoChoices_average (a b : Resolution) :
    sourceMean (twoChoices a b) =
      (separatesFirstPair a + separatesFirstPair b) / 2 ∧
    switchingMean (twoChoices a b) =
      (separatesFirstPair a + separatesFirstPair b) / 2 := by
  cases a <;> cases b <;> decide +kernel

theorem sourceMean_bool_eq_switchingMean (resolve : Bool → Resolution) :
    sourceMean resolve = switchingMean resolve := by
  have heq : resolve = twoChoices (resolve false) (resolve true) := by
    funext s
    cases s <;> rfl
  rw [heq]
  exact (twoChoices_average _ _).1.trans (twoChoices_average _ _).2.symm

theorem bool_discrepancy_zero (resolve : Bool → Resolution) :
    sourceMean resolve - switchingMean resolve = 0 := by
  rw [sourceMean_bool_eq_switchingMean, sub_self]

#print axioms sourceMean_bool_eq_switchingMean
#print axioms bool_discrepancy_zero

end Nanuq.Quartet
