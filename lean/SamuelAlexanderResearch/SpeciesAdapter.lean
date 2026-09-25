import SamuelAlexanderResearch.AncestryViews
import SamuelAlexanderResearch.BinaryPopulation

/-!
# Adapter to the current Alexander research package

This adapter identifies the generic strict-path relation with the existing
SpeciesBridge.Descendant and the index erasure with BinaryPopulation.ForgetLabels.
It proves neither biological validity nor the preservation of species predicates
under arbitrary graph transformations.
-/

namespace AncestryViews

theorem reach_iff_species_descendant {E : SpeciesBridge.Graph} {a b : Nat} :
    Reach E a b ↔ SpeciesBridge.Descendant E a b := by
  constructor
  · intro h
    induction h with
    | edge he => exact .edge he
    | snoc _ he ih => exact .snoc ih he
  · intro h
    induction h with
    | edge he => exact .edge he
    | snoc _ he ih => exact .snoc ih he

theorem erasure_eq_existing_forget (E : BinaryPopulation.LabelledGraph) :
    EraseIndex (fun label a b => E a b label) = BinaryPopulation.ForgetLabels E := rfl

theorem fixed_index_to_species_descendant {I : Type u}
    {E : I -> Nat -> Nat -> Prop} {i : I} {a b : Nat}
    (h : Reach (E i) a b) :
    SpeciesBridge.Descendant (EraseIndex E) a b :=
  reach_iff_species_descendant.mp (fixed_index_path_survives h)

theorem species_descendant_need_not_have_one_index :
    SpeciesBridge.Descendant (EraseIndex SplitLocus) 0 2 ∧
    ¬ (exists i, Reach (SplitLocus i) 0 2) :=
  ⟨reach_iff_species_descendant.mp erased_two_step_path, no_fixed_index_path⟩

end AncestryViews

#print axioms AncestryViews.reach_iff_species_descendant
#print axioms AncestryViews.erasure_eq_existing_forget
#print axioms AncestryViews.fixed_index_to_species_descendant
#print axioms AncestryViews.species_descendant_need_not_have_one_index
