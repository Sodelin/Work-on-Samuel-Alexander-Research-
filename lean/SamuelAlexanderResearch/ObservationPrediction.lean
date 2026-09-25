import Std

/-!
# Observation, recovery, and deterministic prediction

Elementary factorization and state-aggregation facts. No novelty is claimed.
The observation function and state dynamics are supplied mathematical objects;
their empirical validity, measurability, statistical estimation, and any
interpretation involving consciousness or psychological mechanisms are outside
these theorems.
-/

namespace ObservationPrediction

def ConstantOnFibres {State : Type u} {Observation : Type v} {Answer : Type w}
    (observe : State -> Observation) (target : State -> Answer) : Prop :=
  forall a b, observe a = observe b -> target a = target b

/-- Recovery on realizable observations; unused observations may return none. -/
def Recoverable {State : Type u} {Observation : Type v} {Answer : Type w}
    (observe : State -> Observation) (target : State -> Answer) : Prop :=
  exists decode : Observation -> Option Answer,
    forall state, decode (observe state) = some (target state)

theorem recoverable_implies_constant {State : Type u} {Observation : Type v}
    {Answer : Type w} {observe : State -> Observation} {target : State -> Answer}
    (h : Recoverable observe target) : ConstantOnFibres observe target := by
  obtain ⟨decode, correct⟩ := h
  intro a b same
  have ha := correct a
  have hb := correct b
  rw [same] at ha
  exact Option.some.inj (ha.symm.trans hb)

theorem constant_implies_recoverable {State : Type u} {Observation : Type v}
    {Answer : Type w} {observe : State -> Observation} {target : State -> Answer}
    (h : ConstantOnFibres observe target) : Recoverable observe target := by
  classical
  let decode : Observation -> Option Answer := fun value =>
    if witness : exists state, observe state = value then
      some (target (Classical.choose witness))
    else none
  refine ⟨decode, ?_⟩
  intro state
  have witness : exists other, observe other = observe state := ⟨state, rfl⟩
  simp only [decode, dif_pos witness]
  exact congrArg some (h _ _ (Classical.choose_spec witness))

theorem recoverable_iff_constant_on_fibres {State : Type u}
    {Observation : Type v} {Answer : Type w}
    (observe : State -> Observation) (target : State -> Answer) :
    Recoverable observe target ↔ ConstantOnFibres observe target :=
  ⟨recoverable_implies_constant, constant_implies_recoverable⟩

theorem collision_obstructs_recovery {State : Type u} {Observation : Type v}
    {Answer : Type w} {observe : State -> Observation} {target : State -> Answer}
    {a b : State} (same : observe a = observe b) (different : target a ≠ target b) :
    ¬ Recoverable observe target := by
  intro recover
  exact different (recoverable_implies_constant recover a b same)

theorem recoverable_from_fine_of_coarse {State : Type u} {Fine : Type v}
    {Coarse : Type w} {Answer : Type x}
    (fine : State -> Fine) (forget : Fine -> Coarse) (target : State -> Answer)
    (h : Recoverable (fun state => forget (fine state)) target) :
    Recoverable fine target := by
  obtain ⟨decode, correct⟩ := h
  exact ⟨fun value => decode (forget value), correct⟩

def HasExactPredictor {State : Type u} {Observation : Type v}
    (observe : State -> Observation) (step : State -> State) : Prop :=
  exists predict : Observation -> Observation,
    forall state, predict (observe state) = observe (step state)

theorem exact_predictor_iff {State : Type u} {Observation : Type v}
    (observe : State -> Observation) (step : State -> State) :
    HasExactPredictor observe step ↔
      ConstantOnFibres observe (fun state => observe (step state)) := by
  constructor
  · rintro ⟨predict, correct⟩ a b same
    calc
      observe (step a) = predict (observe a) := (correct a).symm
      _ = predict (observe b) := congrArg predict same
      _ = observe (step b) := correct b
  · intro stable
    classical
    let predict : Observation -> Observation := fun value =>
      if witness : exists state, observe state = value then
        observe (step (Classical.choose witness))
      else value
    refine ⟨predict, ?_⟩
    intro state
    have witness : exists other, observe other = observe state := ⟨state, rfl⟩
    simp only [predict, dif_pos witness]
    exact stable _ _ (Classical.choose_spec witness)

def advance {State : Type u} (step : State -> State) : Nat -> State -> State
  | 0, state => state
  | n + 1, state => step (advance step n state)

theorem compatible_observations_agree_in_future {State : Type u}
    {Observation : Type v} (observe : State -> Observation) (step : State -> State)
    (stable : ConstantOnFibres observe (fun state => observe (step state)))
    {a b : State} (same : observe a = observe b) (n : Nat) :
    observe (advance step n a) = observe (advance step n b) := by
  induction n with
  | zero => exact same
  | succ n ih => exact stable _ _ ih

def visible (state : Bool × Bool) : Bool := state.1
def hidden (state : Bool × Bool) : Bool := state.2
def revealNext (state : Bool × Bool) : Bool × Bool := (state.2, state.2)

theorem hidden_bit_not_recoverable : ¬ Recoverable visible hidden := by
  apply collision_obstructs_recovery (a := (false, false)) (b := (false, true))
  · rfl
  · decide

theorem same_current_observation_does_not_ensure_prediction :
    ¬ HasExactPredictor visible revealNext := by
  intro predictor
  have stable := (exact_predictor_iff visible revealNext).mp predictor
  have bad := stable (false, false) (false, true) rfl
  change false = true at bad
  cases bad

theorem full_state_recovers_target {State : Type u} {Answer : Type v}
    (target : State -> Answer) : Recoverable (fun state : State => state) target :=
  ⟨fun state => some (target state), fun _ => rfl⟩

end ObservationPrediction

#print axioms ObservationPrediction.recoverable_implies_constant
#print axioms ObservationPrediction.constant_implies_recoverable
#print axioms ObservationPrediction.recoverable_iff_constant_on_fibres
#print axioms ObservationPrediction.collision_obstructs_recovery
#print axioms ObservationPrediction.recoverable_from_fine_of_coarse
#print axioms ObservationPrediction.exact_predictor_iff
#print axioms ObservationPrediction.compatible_observations_agree_in_future
#print axioms ObservationPrediction.hidden_bit_not_recoverable
#print axioms ObservationPrediction.same_current_observation_does_not_ensure_prediction
#print axioms ObservationPrediction.full_state_recovers_target
