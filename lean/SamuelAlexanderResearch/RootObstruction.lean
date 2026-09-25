import SamuelAlexanderResearch.BinaryPopulation
import SamuelAlexanderResearch.SpeciesBridge

/-!
# No common ancestor for a whole binary natural-date population

The result concerns every `BinaryNatPopulation`, not only the explicit
avoiding construction. Strict identity birth order makes 0 a root. If 1 had
a parent, binary incoming-label coverage would require both false and true
parents, and both parents would have to be 0. Functional labels prohibit this.
Thus 0 and 1 are distinct roots, so the entire population cannot have CA.

No general finite-alphabet root-count theorem or real-date enumeration theorem
is asserted here.
-/

namespace RootObstruction

open SpeciesBridge
open BinaryPopulation

theorem root_zero {E : LabelledGraph} (population : BinaryNatPopulation E) :
    Root (ForgetLabels E) 0 := by
  intro u hu
  have hlt := population.2.1.1 u 0 hu
  omega

theorem root_one {E : LabelledGraph} (population : BinaryNatPopulation E) :
    Root (ForgetLabels E) 1 := by
  intro u hu
  have nonroot : ¬ Root (ForgetLabels E) 1 := fun hroot => hroot u hu
  obtain ⟨uf, hf⟩ := population.2.2.2 1 nonroot false
  obtain ⟨ut, ht⟩ := population.2.2.2 1 nonroot true
  have huf := population.2.1.1 uf 1 ⟨false, hf⟩
  have hut := population.2.1.1 ut 1 ⟨true, ht⟩
  have sameParent : uf = ut := by omega
  subst ut
  have bad : false = true := population.1 uf 1 false true hf ht
  cases bad

/-- Directed ancestry is strict in the given identity birth order. -/
theorem descendant_strict {E : LabelledGraph} (population : BinaryNatPopulation E)
    {u w : Nat} (h : Descendant (ForgetLabels E) u w) : u < w := by
  induction h with
  | edge he => exact population.2.1.1 _ _ he
  | snoc _ he ih =>
    have hlt := population.2.1.1 _ _ he
    omega

/-- A strict directed path cannot end at a parentless vertex. -/
theorem no_descendant_of_root {G : Graph} {v : Nat} (hroot : Root G v)
    (u : Nat) : ¬ Descendant G u v := by
  intro h
  cases h with
  | edge he => exact hroot _ he
  | snoc _ he => exact hroot _ he

/-- The obstruction applies to every binary population in this natural-date model. -/
theorem population_not_commonAncestor {E : LabelledGraph}
    (population : BinaryNatPopulation E) :
    ¬ CommonAncestor (ForgetLabels E) Whole := by
  rintro ⟨a, _, hancestor⟩
  by_cases ha : a = 0
  · subst a
    exact no_descendant_of_root (root_one population) 0
      (hancestor 1 trivial (by omega))
  · exact no_descendant_of_root (root_zero population) a
      (hancestor 0 trivial (by omega))

/-- Two explicit distinct roots and whole-population CA failure. -/
theorem population_root_obstruction {E : LabelledGraph}
    (population : BinaryNatPopulation E) :
    Root (ForgetLabels E) 0 ∧ Root (ForgetLabels E) 1 ∧
    ¬ CommonAncestor (ForgetLabels E) Whole :=
  ⟨root_zero population, root_one population, population_not_commonAncestor population⟩

end RootObstruction

#print axioms RootObstruction.root_zero
#print axioms RootObstruction.root_one
#print axioms RootObstruction.descendant_strict
#print axioms RootObstruction.population_not_commonAncestor
#print axioms RootObstruction.population_root_obstruction
