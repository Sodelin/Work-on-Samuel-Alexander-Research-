import PredictiveState
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

/-! Two general limits on interpreting time/history observations.
These are mathematical null models and counterexamples, not biological fits. -/
namespace HistoryObservation
open PredictiveState

/-- A permanent type and an external clock; controls do not change the type. -/
def stableStep {A U : Type} (_ : A) (s : Nat × U) : Nat × U := (s.1 + 1, s.2)

theorem stable_run {A U : Type} (word : List A) (s : Nat × U) :
    run stableStep word s = (s.1 + word.length, s.2) := by
  induction word generalizing s with
  | nil => simp [run]
  | cons a word ih =>
    rw [run, ih]
    simp [stableStep, Nat.add_comm, Nat.add_left_comm]

/-- A same-unit, time-matched response difference rejects THIS fixed-type,
clock-only null. Merely comparing different selected cells does not. -/
theorem stable_type_matched_history_null {A U O : Type} (g : Nat → U → O)
    (left right : List A) (sameTime : left.length = right.length) (s : Nat × U) :
    (fun z : Nat × U => g z.1 z.2) (run stableStep left s) =
      (fun z : Nat × U => g z.1 z.2) (run stableStep right s) := by
  rw [stable_run, stable_run, sameTime]

/-- A history-affected visible measurement can select different permanent
types. The associated uniform four-row probability table is checked separately. -/
def selectionVisible (history permanentType : Bool) : Bool := history != permanentType

def selectionResponse (_history permanentType : Bool) : Bool := permanentType

theorem selection_no_history_effect (h k permanentType : Bool) :
    selectionResponse h permanentType = selectionResponse k permanentType := rfl

theorem selected_history_perfectly_predicts (h permanentType : Bool)
    (selected : selectionVisible h permanentType = false) :
    selectionResponse h permanentType = h := by
  cases h <;> cases permanentType <;> simp_all [selectionVisible, selectionResponse]

/-- A countdown to a visible event. None is a permanently silent system. -/
def delayedStep (_ : Unit) : Option Nat → Option Nat
  | none => none
  | some n => some (n - 1)

def delayedObserve : Option Nat → Bool
  | none => false
  | some n => decide (n = 0)

theorem delayed_run (word : List Unit) (n : Nat) :
    run delayedStep word (some n) = some (n - word.length) := by
  induction word generalizing n with
  | nil => simp [run]
  | cons a word ih =>
    rw [run, delayedStep, ih]
    congr 1
    simp only [List.length_cons]
    omega

theorem silent_run (word : List Unit) : run delayedStep word none = none := by
  induction word with
  | nil => rfl
  | cons a word ih => exact ih

/-- For every finite experimental horizon, there is a later distinguishing
event. There is no uniform finite horizon for arbitrary infinite state spaces. -/
theorem arbitrary_delayed_distinction (n : Nat) :
    (∀ word : List Unit, word.length ≤ n →
      delayedObserve (run delayedStep word (some (n + 1))) =
        delayedObserve (run delayedStep word none)) ∧
    delayedObserve (run delayedStep (List.replicate (n + 1) ()) (some (n + 1))) ≠
      delayedObserve (run delayedStep (List.replicate (n + 1) ()) none) := by
  constructor
  · intro word hlen
    rw [delayed_run, silent_run]
    have hpos : n + 1 - word.length ≠ 0 := by omega
    simp [delayedObserve, hpos]
  · rw [delayed_run, silent_run]
    simp [delayedObserve]

end HistoryObservation
