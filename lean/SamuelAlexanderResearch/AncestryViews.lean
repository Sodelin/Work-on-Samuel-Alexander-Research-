import Std

/-!
# Indexed ancestry and loss of information under label erasure

This is a small relation-theoretic interface, motivated by locus-specific
genetic inheritance. It is not a formalization of the complete ancestral
recombination graph literature, an inference algorithm, or a species model.
The propositions are elementary interface facts; no novelty is claimed.

The index may denote a locus, but no genome interval, recombination event,
mutation process, or observation likelihood is postulated here.
-/

namespace AncestryViews

/-- A nonempty directed path. -/
inductive Reach {V : Type u} (R : V -> V -> Prop) : V -> V -> Prop where
  | edge {a b : V} : R a b -> Reach R a b
  | snoc {a b c : V} : Reach R a b -> R b c -> Reach R a c

/-- Forget which index justified an edge. -/
def EraseIndex {V : Type u} {I : Type v}
    (R : I -> V -> V -> Prop) : V -> V -> Prop :=
  fun a b => exists i, R i a b

/-- Sound edges give sound path conclusions. This assumes edge soundness. -/
theorem reach_mono {V : Type u} {R S : V -> V -> Prop}
    (hRS : forall a b, R a b -> S a b) {a b : V}
    (h : Reach R a b) : Reach S a b := by
  induction h with
  | edge he => exact .edge (hRS _ _ he)
  | snoc _ he ih => exact .snoc ih (hRS _ _ he)

/-- An entire path at one fixed index survives index erasure. -/
theorem fixed_index_path_survives {V : Type u} {I : Type v}
    {R : I -> V -> V -> Prop} {i : I} {a b : V}
    (h : Reach (R i) a b) : Reach (EraseIndex R) a b :=
  reach_mono (fun _ _ he => ⟨i, he⟩) h

/-- Time order is preserved along a nonempty path. -/
theorem reach_time_increases {V : Type u} {R : V -> V -> Prop}
    (time : V -> Nat)
    (hTime : forall a b, R a b -> time a < time b)
    {a b : V} (h : Reach R a b) : time a < time b := by
  induction h with
  | edge he => exact hTime _ _ he
  | snoc _ he ih => exact Nat.lt_trans ih (hTime _ _ he)

/-- All indexed edges must respect the same clock for this conclusion. -/
theorem erased_path_time_increases {V : Type u} {I : Type v}
    {R : I -> V -> V -> Prop} (time : V -> Nat)
    (hTime : forall i a b, R i a b -> time a < time b)
    {a b : V} (h : Reach (EraseIndex R) a b) : time a < time b := by
  apply reach_time_increases time ?_ h
  intro x y hxy
  obtain ⟨i, hi⟩ := hxy
  exact hTime i x y hi

/-- Minimal two-index example: 0 -> 1 at false; 1 -> 2 at true. -/
def SplitLocus (i : Bool) (a b : Nat) : Prop :=
  if i then a = 1 ∧ b = 2 else a = 0 ∧ b = 1

theorem splitLocus_time (i : Bool) (a b : Nat)
    (h : SplitLocus i a b) : a < b := by
  cases i <;> simp only [SplitLocus, Bool.false_eq_true, if_false, if_true] at h
  all_goals omega

theorem erased_two_step_path : Reach (EraseIndex SplitLocus) 0 2 := by
  have h01 : EraseIndex SplitLocus 0 1 := ⟨false, by simp [SplitLocus]⟩
  have h12 : EraseIndex SplitLocus 1 2 := ⟨true, by simp [SplitLocus]⟩
  exact .snoc (.edge h01) h12

private theorem false_path_ends_at_one {a b : Nat}
    (h : Reach (SplitLocus false) a b) : b = 1 := by
  cases h with
  | edge he => exact he.2
  | snoc _ he => exact he.2

private theorem true_path_starts_at_one {a b : Nat}
    (h : Reach (SplitLocus true) a b) : a = 1 := by
  induction h with
  | edge he => exact he.1
  | snoc _ _ ih => exact ih

theorem no_fixed_index_path : ¬ exists i, Reach (SplitLocus i) 0 2 := by
  rintro ⟨i, hi⟩
  cases i with
  | false => have bad := false_path_ends_at_one hi; omega
  | true => have bad := true_path_starts_at_one hi; omega

/-- Taking transitive closure and taking the union over indices need not commute. -/
theorem erasure_converse_fails :
    Reach (EraseIndex SplitLocus) 0 2 ∧
    ¬ (exists i, Reach (SplitLocus i) 0 2) :=
  ⟨erased_two_step_path, no_fixed_index_path⟩

/-- Two different indexed histories can have exactly the same erased graph. -/
def SameLocus (i : Bool) (a b : Nat) : Prop :=
  i = false ∧ ((a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 2))

theorem erased_histories_agree (a b : Nat) :
    EraseIndex SplitLocus a b ↔ EraseIndex SameLocus a b := by
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨false, rfl, ?_⟩
    cases i with
    | false => exact Or.inl hi
    | true => exact Or.inr hi
  · rintro ⟨i, _, h⟩
    rcases h with h | h
    · exact ⟨false, h⟩
    · exact ⟨true, h⟩

theorem same_locus_two_step_path : Reach (SameLocus false) 0 2 := by
  have h01 : SameLocus false 0 1 := ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
  have h12 : SameLocus false 1 2 := ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩
  exact .snoc (.edge h01) h12

/-- The erased graph alone cannot determine this fixed-index ancestry fact. -/
theorem erased_graph_does_not_determine_fixed_index_ancestry :
    (forall a b, EraseIndex SplitLocus a b ↔ EraseIndex SameLocus a b) ∧
    (¬ exists i, Reach (SplitLocus i) 0 2) ∧
    (exists i, Reach (SameLocus i) 0 2) :=
  ⟨erased_histories_agree, no_fixed_index_path,
    ⟨false, same_locus_two_step_path⟩⟩

end AncestryViews

#print axioms AncestryViews.reach_mono
#print axioms AncestryViews.fixed_index_path_survives
#print axioms AncestryViews.reach_time_increases
#print axioms AncestryViews.erased_path_time_increases
#print axioms AncestryViews.erasure_converse_fails
#print axioms AncestryViews.erased_graph_does_not_determine_fixed_index_ancestry
