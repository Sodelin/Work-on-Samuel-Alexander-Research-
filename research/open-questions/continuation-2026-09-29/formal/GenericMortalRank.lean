import GenericPruning

/-!
# Exact finite ranks outside the live core

A finitely branching labelled graph may realize the target at some states
and fail at others. The complement of the live core is forward closed. On
this mortal region, the canonical natural rank is the attained maximum
remaining matching length and is pointwise least among decreasing natural
certificates. Global avoidance is not a hypothesis.
-/

namespace GenericMortalRank

open GenericCertificate GenericPruning
universe u v
variable {α : Type u}

abbrev Mortal (R : α → α → Prop) := {x // ¬ core R x}

def MortalStep (R : α → α → Prop) (y x : Mortal R) : Prop := R y.1 x.1

theorem mortal_forward_closed (R : α → α → Prop) {x y : α}
    (hx : ¬ core R x) (hy : R y x) : ¬ core R y := by
  intro hc
  apply hx
  intro n
  cases n with
  | zero => trivial
  | succ n => exact ⟨y,hy,hc n⟩

theorem mortal_wellFounded (R : α → α → Prop) : WellFounded (MortalStep R) := by
  rw [wellFounded_iff_isEmpty_descending_chain]
  refine ⟨?_⟩
  rintro ⟨f,hf⟩
  apply (f 0).2
  exact live_implies_core R ⟨fun n => (f n).1, rfl, hf⟩

theorem finite_mortal_children (R : α → α → Prop)
    (fin : ∀ x, Finite {y // R y x}) (x : Mortal R) :
    Finite {y // MortalStep R y x} := by
  let := fin x.1
  let f : {y // MortalStep R y x} → {y // R y x.1} := fun y => ⟨y.1.1,y.2⟩
  apply Finite.of_injective f
  intro a b hab
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : {y // R y x.1} => z.1) hab

theorem chainLength_iff_survives (R : α → α → Prop) (x : Mortal R) (n : Nat) :
    ChainLength (MortalStep R) x n ↔ survives R n x.1 := by
  constructor
  · intro h
    induction h with
    | zero => trivial
    | cons hy hc ih => exact ⟨_,hy,ih⟩
  · intro h
    induction n generalizing x with
    | zero => exact ChainLength.zero x
    | succ n ih =>
      obtain ⟨y,hy,hs⟩ := h
      let y' : Mortal R := ⟨y,mortal_forward_closed R x.2 hy⟩
      exact ChainLength.cons (y := y') hy (ih y' hs)

noncomputable def height (R : α → α → Prop)
    (fin : ∀ x, Finite {y // R y x}) : Mortal R → Nat :=
  finiteHeight (MortalStep R) (finite_mortal_children R fin) (mortal_wellFounded R)

theorem height_decreases (R : α → α → Prop)
    (fin : ∀ x, Finite {y // R y x}) {x y : Mortal R} (hy : R y.1 x.1) :
    height R fin y < height R fin x :=
  finiteHeight_decreases _ _ _ hy

theorem height_attained_and_bounds (R : α → α → Prop)
    (fin : ∀ x, Finite {y // R y x}) (x : Mortal R) :
    survives R (height R fin x) x.1 ∧
      ∀ n, survives R n x.1 → n ≤ height R fin x := by
  constructor
  · apply (chainLength_iff_survives R x _).mp
    exact finiteHeight_attained _ _ _ x
  · intro n hn
    apply chainLength_le_height _ _ _
    exact (chainLength_iff_survives R x n).mpr hn

theorem height_least (R : α → α → Prop)
    (fin : ∀ x, Finite {y // R y x}) (rank : Mortal R → Nat)
    (cert : ∀ {x y}, R y.1 x.1 → rank y < rank x) :
    ∀ x, height R fin x ≤ rank x :=
  finiteHeight_least _ _ _ rank cert

theorem survives_iff_le_height (R : α → α → Prop)
    (fin : ∀ x, Finite {y // R y x}) (x : Mortal R) (n : Nat) :
    survives R n x.1 ↔ n ≤ height R fin x := by
  constructor
  · exact (height_attained_and_bounds R fin x).2 n
  · intro hn
    exact survives_mono R hn (height_attained_and_bounds R fin x).1

/-- A concrete state has exactly one of two behaviors, without global avoidance. -/
theorem live_or_finite_maximum (R : α → α → Prop)
    (fin : ∀ x, Finite {y // R y x}) (x : α) :
    Live R x ∨ ∃ h : Nat, survives R h x ∧ ∀ n, survives R n x → n ≤ h := by
  classical
  by_cases hx : core R x
  · exact Or.inl ((core_iff_live R fin x).mp hx)
  · exact Or.inr ⟨height R fin ⟨x,hx⟩, height_attained_and_bounds R fin ⟨x,hx⟩⟩

variable {V : Type u} {Label : Type v}

theorem matching_state_dichotomy (E : Graph V Label) (s : Nat → Label)
    (fin : FiniteLabelChildren E) (x : State E s) :
    Live (Step E s) x ∨ ∃ h : Nat, survives (Step E s) h x ∧
      ∀ n, survives (Step E s) n x → n ≤ h :=
  live_or_finite_maximum _ (finite_state_children E s fin) x

#print axioms GenericMortalRank.mortal_forward_closed
#print axioms GenericMortalRank.mortal_wellFounded
#print axioms GenericMortalRank.chainLength_iff_survives
#print axioms GenericMortalRank.height_decreases
#print axioms GenericMortalRank.height_attained_and_bounds
#print axioms GenericMortalRank.height_least
#print axioms GenericMortalRank.survives_iff_le_height
#print axioms GenericMortalRank.live_or_finite_maximum
#print axioms GenericMortalRank.matching_state_dichotomy

end GenericMortalRank
