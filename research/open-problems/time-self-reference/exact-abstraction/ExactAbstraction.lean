import Mathlib.Logic.Function.Basic
set_option autoImplicit false

/-! Exact deterministic abstraction through a surjective observation.
This is the standard quotient/congruence factorization criterion. The example
exhibits loss of a changing rule bit inside a fixed, finite joint-state model.
It does not address arbitrary changes of semantics, language or metamodel. -/
namespace ExactAbstraction
universe u v w
variable {A : Type u} {X : Type v} {Z : Type w}

/-- States with the same current observation have the same next observation,
provided the same control is applied. -/
def FibreCompatible (F : A → X → X) (c : X → Z) : Prop :=
  ∀ a x y, c x = c y → c (F a x) = c (F a y)

/-- An exact deterministic update on observed states exists exactly when the
observation fibres are respected by every controlled concrete update. -/
theorem exact_factor_iff (F : A → X → X) (c : X → Z)
    (onto : Function.Surjective c) :
    (∃ Fbar : A → Z → Z, ∀ a x, c (F a x) = Fbar a (c x)) ↔
      FibreCompatible F c := by
  constructor
  · rintro ⟨Fbar, h⟩ a x y hxy
    rw [h, h, hxy]
  · intro compatible
    classical
    let representative : Z → X := fun z => Classical.choose (onto z)
    have represented : ∀ z, c (representative z) = z :=
      fun z => Classical.choose_spec (onto z)
    refine ⟨fun a z => c (F a (representative z)), ?_⟩
    intro a x
    exact compatible a x (representative (c x)) (represented (c x)).symm

/-- Surjectivity also makes the exact abstract update unique on all of Z. -/
theorem exact_factor_unique (F : A → X → X) (c : X → Z)
    (onto : Function.Surjective c) (G H : A → Z → Z)
    (hG : ∀ a x, c (F a x) = G a (c x))
    (hH : ∀ a x, c (F a x) = H a (c x)) : G = H := by
  funext a z
  obtain ⟨x, rfl⟩ := onto z
  exact (hG a x).symm.trans (hH a x)

/-- Run the concrete system with an externally supplied control sequence. -/
def trajectory (F : A → X → X) (input : Nat → A) (x : X) : Nat → X
  | 0 => x
  | t + 1 => F (input t) (trajectory F input x t)

/-- Every finite prefix is preserved, with the identical control sequence. -/
theorem trajectory_preservation (F : A → X → X) (Fbar : A → Z → Z)
    (c : X → Z) (commutes : ∀ a x, c (F a x) = Fbar a (c x))
    (input : Nat → A) (x : X) (t : Nat) :
    c (trajectory F input x t) = trajectory Fbar input (c x) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [trajectory, commutes, ih]

/-- The fibre criterion gives one abstract model preserving every trajectory. -/
theorem compatible_gives_trajectories (F : A → X → X) (c : X → Z)
    (onto : Function.Surjective c) (compatible : FibreCompatible F c) :
    ∃ Fbar : A → Z → Z,
      (∀ a x, c (F a x) = Fbar a (c x)) ∧
      ∀ (input : Nat → A) x t,
        c (trajectory F input x t) = trajectory Fbar input (c x) t := by
  obtain ⟨Fbar, commutes⟩ := (exact_factor_iff F c onto).mpr compatible
  exact ⟨Fbar, commutes, trajectory_preservation F Fbar c commutes⟩

namespace TwoBit

/-- x is the visible result; r chooses which constant-output rule acts next. -/
abbrev JointState := Bool × Bool

def observe (s : JointState) : Bool := s.1

/-- Apply the currently stored rule and toggle the stored rule for next time.
The two-bit joint-state update itself is fixed. -/
def jointStep (s : JointState) : JointState := (s.2, !s.2)

def controlledStep (_ : Unit) : JointState → JointState := jointStep

lemma observe_surjective : Function.Surjective observe :=
  fun x => ⟨(x, false), rfl⟩

/-- The discarded rule bit changes the next observed result. -/
theorem projection_collision :
    observe (false, false) = observe (false, true) ∧
    observe (jointStep (false, false)) ≠ observe (jointStep (false, true)) := by
  decide

theorem not_fibre_compatible : ¬ FibreCompatible controlledStep observe := by
  intro compatible
  exact projection_collision.2
    (compatible () (false, false) (false, true) projection_collision.1)

/-- No deterministic autonomous update on the visible result alone can work
for every joint state, including both possible stored rules. -/
theorem no_state_only_update :
    ¬ ∃ g : Bool → Bool, ∀ s, observe (jointStep s) = g (observe s) := by
  rintro ⟨g, commutes⟩
  apply not_fibre_compatible
  exact (exact_factor_iff controlledStep observe observe_surjective).mp
    ⟨fun _ => g, fun _ s => commutes s⟩

/-- Direct algebra of the fixed joint map: its third iterate equals its first. -/
theorem third_step_eq_first (s : JointState) :
    jointStep (jointStep (jointStep s)) = jointStep s := by
  rcases s with ⟨x, r⟩
  cases x <;> cases r <;> rfl

theorem step_ne_self (s : JointState) : jointStep s ≠ s := by
  rcases s with ⟨x, r⟩
  cases x <;> cases r <;> decide

def orbit (s : JointState) : Nat → JointState :=
  trajectory controlledStep (fun _ => ()) s

/-- Period two from time one onward, for every initial joint state. -/
theorem period_two_after_first (s : JointState) (t : Nat) :
    orbit s (t + 3) = orbit s (t + 1) := by
  change jointStep (jointStep (jointStep (orbit s t))) = jointStep (orbit s t)
  exact third_step_eq_first _

/-- Adjacent states differ, so the eventual cycle has exact period two. -/
theorem exact_period_two_after_first (s : JointState) (t : Nat) :
    orbit s (t + 3) = orbit s (t + 1) ∧
      orbit s (t + 2) ≠ orbit s (t + 1) := by
  refine ⟨period_two_after_first s t, ?_⟩
  change jointStep (orbit s (t + 1)) ≠ orbit s (t + 1)
  exact step_ne_self _

example : (List.range 5).map (orbit (false, false)) =
    [(false, false), (false, true), (true, false), (false, true), (true, false)] := by
  decide

example : (List.range 5).map (orbit (false, true)) =
    [(false, true), (true, false), (false, true), (true, false), (false, true)] := by
  decide

#eval (List.range 5).map (orbit (false, false))
#eval (List.range 5).map (orbit (false, true))
end TwoBit

#print axioms exact_factor_iff
#print axioms exact_factor_unique
#print axioms trajectory_preservation
#print axioms compatible_gives_trajectories
#print axioms TwoBit.projection_collision
#print axioms TwoBit.no_state_only_update
#print axioms TwoBit.period_two_after_first
#print axioms TwoBit.exact_period_two_after_first
end ExactAbstraction
