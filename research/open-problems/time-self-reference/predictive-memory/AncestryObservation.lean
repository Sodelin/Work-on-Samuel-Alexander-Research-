import PredictiveState
import SamuelAlexanderResearch.AncestralRestriction

set_option autoImplicit false

/-!
A proved mapping to existing ancestry-restriction definitions. The actions in
this module are graph-processing operations, NOT cell interventions or the
stochastic generation of a Wong ARG. Enlarging the queried sample set exposes
the exact boundary of the preservation claim.
-/
namespace AncestryObservation
open AncestryViews AncestralRestriction PredictiveState

universe u
variable {V : Type u}
abbrev Rel (V : Type u) := V → V → Prop

def compress (S : V → Prop) (R : Rel V) : Rel V := Restrict R S

abbrev Action (S : V → Prop) := { A : V → Prop // ∀ v, A v → S v }

def restrictStep (S : V → Prop) (a : Action S) (R : Rel V) : Rel V :=
  Restrict R a.val

theorem larger_after_smaller (R : Rel V) (S A : V → Prop)
    (subset : ∀ v, A v → S v) : Restrict (Restrict R A) S = Restrict R A := by
  funext x y
  apply propext
  constructor
  · exact fun h => h.1
  · intro h
    exact ⟨h, ancestral_mono_samples subset (restriction_resolved h)⟩

/-- Exact one-step commutation, using the existing nested-restriction theorem. -/
theorem restriction_commutes (S : V → Prop) (a : Action S) (R : Rel V) :
    compress S (restrictStep S a R) = restrictStep S a (compress S R) := by
  change Restrict (Restrict R a.val) S = Restrict (Restrict R S) a.val
  rw [larger_after_smaller R S a.val a.property]
  funext x y
  exact propext (restriction_nested a.property).symm

/-- The Royal Society track's trajectory theorem applies to these actual
ancestry operations, for every sequence of admitted sample subsets. -/
theorem restriction_all_words (S : V → Prop) (word : List (Action S)) (R : Rel V) :
    compress S (run (restrictStep S) word R) =
      run (restrictStep S) word (compress S R) :=
  run_commutes _ _ _ (restriction_commutes S) word R

/-- Every fixed-sample reachability query factors through the compressed graph. -/
theorem sample_query_factors (S : V → Prop) (R : Rel V) (s : V) (hs : S s) (a : V) :
    Reach (compress S R) a s ↔ Reach R a s := sample_path_iff hs

def indexedCompress (S : Nat → Prop) (R : Bool → Nat → Nat → Prop) := AtLocus R S

theorem same_existing_samples :
    indexedCompress (fun n => n = 2) SplitLocus =
      indexedCompress (fun n => n = 2) VisibleTail := by
  funext i a b
  exact propext (raw_graph_not_identified_by_sample_relations.1 i a b)

/-- The lost edge carries material for a newly requested sample. -/
theorem expanded_sample_distinguishes :
    indexedCompress (fun n => n = 1 ∨ n = 2) SplitLocus false 0 1 ∧
      ¬ indexedCompress (fun n => n = 1 ∨ n = 2) VisibleTail false 0 1 := by
  constructor
  · exact ⟨by simp [SplitLocus], Or.inl (Or.inl rfl)⟩
  · intro h
    exact raw_graph_not_identified_by_sample_relations.2.2 h.1

/-- No decoder can recover all enlarged-sample relations from the previously
sample-compressed relation, even for these two time-ordered acyclic examples. -/
theorem no_universal_sample_expansion :
    ¬ ∃ recover : (Bool → Nat → Nat → Prop) → (Bool → Nat → Nat → Prop),
      ∀ R, recover (indexedCompress (fun n => n = 2) R) =
        indexedCompress (fun n => n = 1 ∨ n = 2) R := by
  rintro ⟨recover, correct⟩
  have same := congrArg recover same_existing_samples
  rw [correct, correct] at same
  have heq := congrFun (congrFun (congrFun same false) 0) 1
  exact expanded_sample_distinguishes.2 (heq.mp expanded_sample_distinguishes.1)

end AncestryObservation
