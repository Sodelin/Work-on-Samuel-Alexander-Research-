import PredictiveState
import Mathlib.Data.Fintype.Prod

set_option autoImplicit false

/-! Full mechanization of the previously written controlled-abstraction bridge.
The Boolean transitions are stipulated mathematics, not fitted cell dynamics. -/
namespace ControlledMemory
open PredictiveState

inductive Action where
  | wait | prime | probe | reset
  deriving DecidableEq, Repr

structure Cell where
  visible : Bool
  memory : Bool
  nuisance : Bool
  deriving DecidableEq, Repr

abbrev Summary := Bool × Bool
abbrev History := Bool × List Bool

def parity : List Bool → Bool
  | [] => false
  | b :: h => if b then !(parity h) else parity h

theorem parity_append_false (h : List Bool) : parity (h ++ [false]) = parity h := by
  induction h with
  | nil => rfl
  | cons b h ih => cases b <;> simp [parity, ih]

theorem parity_append_true (h : List Bool) : parity (h ++ [true]) = !(parity h) := by
  induction h with
  | nil => rfl
  | cons b h ih => cases b <;> simp [parity, ih]

def summaryStep : Action → Summary → Summary
  | .wait, z => z
  | .prime, z => (z.1, !z.2)
  | .probe, z => (z.2, z.2)
  | .reset, _ => (false, false)

def cellStep : Action → Cell → Cell
  | .wait, s => ⟨s.visible, s.memory, !s.nuisance⟩
  | .prime, s => ⟨s.visible, !s.memory, !s.nuisance⟩
  | .probe, s => ⟨s.memory, s.memory, !s.nuisance⟩
  | .reset, s => ⟨false, false, !s.nuisance⟩

def historyStep : Action → History → History
  | .wait, (v, h) => (v, h ++ [false])
  | .prime, (v, h) => (v, h ++ [true])
  | .probe, (_, h) => (parity h, h ++ [false])
  | .reset, _ => (false, [])

def cellSummary (s : Cell) : Summary := (s.visible, s.memory)
def historySummary (s : History) : Summary := (s.1, parity s.2)

theorem cell_commutes (a : Action) (s : Cell) :
    cellSummary (cellStep a s) = summaryStep a (cellSummary s) := by cases a <;> rfl

theorem history_commutes (a : Action) (s : History) :
    historySummary (historyStep a s) = summaryStep a (historySummary s) := by
  rcases s with ⟨v, h⟩
  cases a <;> simp [historyStep, historySummary, summaryStep,
    parity_append_false, parity_append_true, parity]

theorem cellSummary_onto : Function.Surjective cellSummary :=
  fun (v, m) => ⟨⟨v, m, false⟩, rfl⟩

theorem historySummary_onto : Function.Surjective historySummary := by
  rintro ⟨v, m⟩
  cases m
  · exact ⟨(v, []), rfl⟩
  · exact ⟨(v, [true]), rfl⟩

theorem parity_replicate_false (n : Nat) : parity (List.replicate n false) = false := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [List.replicate_succ, parity] using ih

def recent (n : Nat) (h : List Bool) : List Bool := h.drop (h.length - n)

/-- One bit can summarize arbitrary history, but no fixed suffix window can
replace that bit for this process. The witnesses are finite, including n = 0. -/
theorem no_finite_suffix_decoder (n : Nat) :
    ¬ ∃ decode : List Bool → Bool, ∀ h, decode (recent n h) = parity h := by
  rintro ⟨decode, correct⟩
  have h0 := correct (List.replicate n false)
  have h1 := correct (true :: List.replicate n false)
  simp [recent, parity_replicate_false] at h0
  simp [recent, parity, parity_replicate_false, Nat.add_comm] at h1
  exact Bool.noConfusion (h0.symm.trans h1)

/-- No bound on the stored record length or on the intervention horizon. -/
theorem cross_model_all_words (s : Cell) (h : History)
    (related : cellSummary s = historySummary h) (word : List Action) :
    cellSummary (run cellStep word s) = historySummary (run historyStep word h) := by
  rw [run_commutes cellStep summaryStep cellSummary cell_commutes,
    run_commutes historyStep summaryStep historySummary history_commutes, related]

theorem cross_model_all_times (s : Cell) (h : History)
    (related : cellSummary s = historySummary h) (input : Nat → Action) (t : Nat) :
    cellSummary (ExactAbstraction.trajectory cellStep input s t) =
      historySummary (ExactAbstraction.trajectory historyStep input h t) := by
  rw [ExactAbstraction.trajectory_preservation cellStep summaryStep cellSummary cell_commutes,
    ExactAbstraction.trajectory_preservation historyStep summaryStep historySummary history_commutes,
    related]

universe u v w r

/-- The previous packet's open refinement obligation, for arbitrary types. -/
theorem probe_refinement_factor {A : Type u} {X : Type v} {O : Type w} {R : Type r}
    (T : A → X → X) (p : X → O) (probe : A)
    (c : X → R) (G : A → R → R) (d : R → O)
    (hobs : ∀ x, d (c x) = p x) (hstep : ∀ a x, c (T a x) = G a (c x)) (x : X) :
    (p x, p (T probe x)) = (d (c x), d (G probe (c x))) := by
  rw [← hobs x, ← hobs (T probe x), hstep]

theorem cell_future_iff (s t : Cell) :
    FutureEq cellStep Cell.visible s t ↔ cellSummary s = cellSummary t := by
  constructor
  · intro h
    exact Prod.ext (h []) (h [.probe])
  · intro h
    exact exact_refinement_future cellStep Cell.visible cellSummary summaryStep Prod.fst
      (fun _ => rfl) cell_commutes h

theorem history_future_iff (s t : History) :
    FutureEq historyStep Prod.fst s t ↔ historySummary s = historySummary t := by
  constructor
  · intro h
    exact Prod.ext (h []) (h [.probe])
  · intro h
    exact exact_refinement_future historyStep Prod.fst historySummary summaryStep Prod.fst
      (fun _ => rfl) history_commutes h

/-- Every exact output-preserving model needs at least four attained codes;
the two-bit summary attains this bound. This is not Shannon entropy. -/
theorem at_least_four {R : Type r} [Fintype R]
    (c : Cell → R) (G : Action → R → R) (d : R → Bool)
    (hobs : ∀ s, d (c s) = s.visible)
    (hstep : ∀ a s, c (cellStep a s) = G a (c s)) : 4 ≤ Fintype.card R := by
  have h := distinguishable_card_le cellStep Cell.visible c G d hobs hstep
    (fun z : Bool × Bool => (⟨z.1, z.2, false⟩ : Cell))
    (fun j k hne heq => hne ((cell_future_iff _ _).mp heq))
  simpa using h

theorem memory_required_at_fixed_visible {R : Type r}
    (c : Cell → R) (G : Action → R → R) (d : R → Bool)
    (hobs : ∀ s, d (c s) = s.visible)
    (hstep : ∀ a s, c (cellStep a s) = G a (c s)) (v : Bool) :
    c ⟨v, false, false⟩ ≠ c ⟨v, true, false⟩ := by
  intro h
  have hf := exact_refinement_future cellStep Cell.visible c G d hobs hstep h
  have bad : false = true := hf [.probe]
  cases bad

/-- The collision is reachable from the same initialization by two histories. -/
theorem reachable_probe_witness :
    (run cellStep [.reset, .wait] ⟨false, false, false⟩).visible =
      (run cellStep [.reset, .prime] ⟨false, false, false⟩).visible ∧
    (run cellStep [.reset, .wait, .probe] ⟨false, false, false⟩).visible ≠
      (run cellStep [.reset, .prime, .probe] ⟨false, false, false⟩).visible := by decide

theorem all_summaries_reachable : ∀ z : Summary, ∃ word : List Action,
    cellSummary (run cellStep word ⟨false, false, false⟩) = z := by
  rintro ⟨v, m⟩
  cases v <;> cases m
  · exact ⟨[], rfl⟩
  · exact ⟨[.prime], rfl⟩
  · exact ⟨[.prime, .probe, .prime], rfl⟩
  · exact ⟨[.prime, .probe], rfl⟩

inductive PassiveAction where
  | wait | prime | reset

def admit : PassiveAction → Action
  | .wait => .wait
  | .prime => .prime
  | .reset => .reset

def passiveStep : PassiveAction → Bool → Bool
  | .wait, v => v
  | .prime, v => v
  | .reset, _ => false

theorem passive_visible_exact (a : PassiveAction) (s : Cell) :
    (cellStep (admit a) s).visible = passiveStep a s.visible := by cases a <;> rfl

theorem passive_future_iff (s t : Cell) :
    FutureEq (fun a => cellStep (admit a)) Cell.visible s t ↔ s.visible = t.visible := by
  constructor
  · exact future_observe
  · intro h
    exact exact_refinement_future _ _ Cell.visible passiveStep id
      (fun _ => rfl) passive_visible_exact h

/-- Changing the probe breaks the old summary: the nuisance bit becomes relevant. -/
def changedProbe (s : Cell) : Bool := s.memory != s.nuisance

theorem changed_probe_refutes_summary :
    cellSummary ⟨false, false, false⟩ = cellSummary ⟨false, false, true⟩ ∧
    changedProbe ⟨false, false, false⟩ ≠ changedProbe ⟨false, false, true⟩ := by decide

end ControlledMemory
