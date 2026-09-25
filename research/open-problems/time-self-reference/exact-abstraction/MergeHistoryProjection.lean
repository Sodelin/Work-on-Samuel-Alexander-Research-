import ExactAbstraction
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Fin
set_option autoImplicit false

/-! A bounded merge-history obstruction for an unordered current partition.
A split restores immediate predecessor trees. This models one structural
operator in the pinned IPDm implementation, not policies or stochastic runs. -/
namespace MergeHistoryProjection

abbrev Site := Fin 4

inductive History where
  | leaf (site : Site)
  | merge (left right : History)
  deriving DecidableEq, Repr

abbrev Forest := List History

def leafList : History → List Site
  | .leaf i => [i]
  | .merge l r => leafList l ++ leafList r

def flatLeaves (f : Forest) : List Site := f.flatMap leafList

def blocks (f : Forest) : Finset (Finset Site) :=
  (f.map (fun t => (leafList t).toFinset)).toFinset

/-- All four persistent sites occur exactly once; thus the block family is a
partition, with neither repeated sites nor missing sites. -/
def Legal (f : Forest) : Prop :=
  (flatLeaves f).Nodup ∧ (flatLeaves f).toFinset = Finset.univ

instance legal_decidable (f : Forest) : Decidable (Legal f) := by
  unfold Legal
  infer_instance

/-- Restore the immediate parents of the designated first composite.
For a nonsplittable first root this totalized function does nothing. -/
def splitFirst : Forest → Forest
  | .merge l r :: rest => l :: r :: rest
  | f => f

def canSplit : Forest → Bool
  | .merge _ _ :: _ => true
  | _ => false

lemma split_preserves_leaves (f : Forest) : flatLeaves (splitFirst f) = flatLeaves f := by
  cases f with
  | nil => rfl
  | cons t rest =>
    cases t <;> simp [splitFirst, flatLeaves, leafList, List.append_assoc]

lemma split_preserves_legal (f : Forest) (h : Legal f) : Legal (splitFirst f) := by
  simpa only [Legal, split_preserves_leaves] using h

abbrev State := {f : Forest // Legal f}

def splitState (s : State) : State := ⟨splitFirst s.val, split_preserves_legal s.val s.property⟩

inductive Action where
  | splitFirst
  deriving DecidableEq, Repr

def update (_ : Action) (s : State) : State := splitState s

/-- Abstract observations are the attainable unordered partitions. Restricting
to the image makes the projection explicitly surjective for the shared theorem. -/
abbrev Observation := Set.range (fun s : State => blocks s.val)

def observe (s : State) : Observation := ⟨blocks s.val, ⟨s, rfl⟩⟩

lemma observe_surjective : Function.Surjective observe := by
  rintro ⟨p, s, hs⟩
  exact ⟨s, Subtype.ext hs⟩

/-- An ordered adjacent merge helper used only to exhibit the two legal histories. -/
def mergeAdjacent : Nat → Forest → Forest
  | 0, p :: q :: rest => .merge p q :: rest
  | n + 1, p :: rest => p :: mergeAdjacent n rest
  | _, f => f

def a : History := .leaf 0
def b : History := .leaf 1
def c : History := .leaf 2
def d : History := .leaf 3

def initial : Forest := [a, b, c, d]
def leftIntermediate : Forest := [.merge a b, c, d]
def rightIntermediate : Forest := [a, .merge b c, d]
def leftForest : Forest := [.merge (.merge a b) c, d]
def rightForest : Forest := [.merge a (.merge b c), d]

def leftState : State := ⟨leftForest, by decide⟩
def rightState : State := ⟨rightForest, by decide⟩

/-- Both witnesses arise by two genuine adjacent merges, with site 3 retained. -/
theorem adjacent_merge_histories :
    mergeAdjacent 0 initial = leftIntermediate ∧
    mergeAdjacent 0 leftIntermediate = leftForest ∧
    mergeAdjacent 1 initial = rightIntermediate ∧
    mergeAdjacent 0 rightIntermediate = rightForest := by
  decide

theorem legal_histories :
    Legal initial ∧ Legal leftIntermediate ∧ Legal rightIntermediate ∧
      Legal leftForest ∧ Legal rightForest := by
  decide

/-- Both designated roots can be split, and both states retain a separate spectator. -/
theorem admissible_splits_with_spectator :
    canSplit leftState.val = true ∧ canSplit rightState.val = true ∧
      leftState.val.length = 2 ∧ rightState.val.length = 2 := by
  decide

/-- Equality is equality of unordered finite sets of unordered site sets. -/
theorem same_current_partition :
    blocks leftState.val = ({{0, 1, 2}, {3}} : Finset (Finset Site)) ∧
      blocks rightState.val = ({{0, 1, 2}, {3}} : Finset (Finset Site)) := by
  decide

theorem distinct_restored_partitions :
    blocks (splitState leftState).val = ({{0, 1}, {2}, {3}} : Finset (Finset Site)) ∧
    blocks (splitState rightState).val = ({{0}, {1, 2}, {3}} : Finset (Finset Site)) ∧
    blocks (splitState leftState).val ≠ blocks (splitState rightState).val := by
  decide

lemma same_observation : observe leftState = observe rightState := by
  apply Subtype.ext
  exact same_current_partition.1.trans same_current_partition.2.symm

lemma different_next_observations :
    observe (update .splitFirst leftState) ≠ observe (update .splitFirst rightState) := by
  intro h
  exact distinct_restored_partitions.2.2 (congrArg Subtype.val h)

/-- The common exact-abstraction criterion detects this history loss. -/
theorem not_fibre_compatible : ¬ ExactAbstraction.FibreCompatible update observe := by
  intro compatible
  exact different_next_observations
    (compatible .splitFirst leftState rightState same_observation)

theorem no_exact_partition_model :
    ¬ ∃ reduced : Action → Observation → Observation,
      ∀ action s, observe (update action s) = reduced action (observe s) := by
  intro h
  exact not_fibre_compatible
    ((ExactAbstraction.exact_factor_iff update observe observe_surjective).mp h)

/-- Even allowing an arbitrary output block family, a current-partition-only
split cannot be exact on every state where the chosen split is admissible. -/
theorem no_partition_only_admissible_split :
    ¬ ∃ reduced : Finset (Finset Site) → Finset (Finset Site),
      ∀ s : State, canSplit s.val = true →
        blocks (splitState s).val = reduced (blocks s.val) := by
  rintro ⟨reduced, exactOn⟩
  have hL := exactOn leftState admissible_splits_with_spectator.1
  have hR := exactOn rightState admissible_splits_with_spectator.2.1
  have same : blocks leftState.val = blocks rightState.val :=
    same_current_partition.1.trans same_current_partition.2.symm
  apply distinct_restored_partitions.2.2
  exact hL.trans ((congrArg reduced same).trans hR.symm)

#print axioms split_preserves_legal
#print axioms adjacent_merge_histories
#print axioms legal_histories
#print axioms admissible_splits_with_spectator
#print axioms same_current_partition
#print axioms distinct_restored_partitions
#print axioms no_exact_partition_model
#print axioms no_partition_only_admissible_split
end MergeHistoryProjection
