import SamuelAlexanderResearch.BinaryAvoidance
import SamuelAlexanderResearch.SpeciesBridge

/-!
# Actual binary avoiding populations that are specieslike clusters

This module joins the explicit labelled `P_s` from `BinaryAvoidance` to the
unlabelled graph geometry in `SpeciesBridge`. It proves the population axioms
with natural-number birthdates, functional edge labels, roots exactly 0 and 1,
and one incoming parent of each Bool label at each non-root. The complete
negative endpoint supplies a maximal specieslike population with REF that
avoids every target which is not eventually periodic.

Real-valued date bounds and Alexander's positive unavoidability theorem remain
outside this Std-only development. The final equivalence is explicitly
conditional on the latter positive theorem for the displayed population model.

Construction: classification manuscript, Section 2,
https://github.com/avg-netizen/biological-unavoidability/blob/main/paper.md
-/

namespace BinaryPopulation

open SpeciesBridge
open BinaryAvoidance

abbrev LabelledGraph := Nat -> Nat -> Bool -> Prop

def ForgetLabels (E : LabelledGraph) : Graph :=
  fun u w => exists label, E u w label

def UniqueLabels (E : LabelledGraph) : Prop :=
  forall u w a b, E u w a -> E u w b -> a = b

/-- The population axioms, with identity natural-number birthdates.

The natural-date biosphere package includes increasing parent dates, finite
date prefixes, finite children, and infinitely many vertices. We add finite
roots, incoming-label coverage at non-roots, and functional edge labels.
-/
def BinaryNatPopulation (E : LabelledGraph) : Prop :=
  UniqueLabels E ∧ NaturalDateBiosphere (ForgetLabels E) ∧
  FiniteSupport (Root (ForgetLabels E)) ∧
  forall w, ¬ Root (ForgetLabels E) w ->
    forall label, exists u, E u w label

def Realizes (E : LabelledGraph) (target : Nat -> Bool) : Prop :=
  exists path : Nat -> Nat,
    forall k, E (path k) (path (k + 1)) (target k)

/-- Forgetting labels in the avoiding construction gives exactly `PsEdge`. -/
theorem forget_edge_iff (s : Nat -> Bool) (u w : Nat) :
    ForgetLabels (Edge s) u w ↔ PsEdge u w := by
  constructor
  · rintro ⟨label, hw, h⟩
    exact ⟨hw, h.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)⟩
  · rintro ⟨hw, h | h⟩
    · exact ⟨row s w, hw, Or.inl ⟨h, rfl⟩⟩
    · exact ⟨!(row s w), hw, Or.inr ⟨h, rfl⟩⟩

theorem forget_edge_eq (s : Nat -> Bool) : ForgetLabels (Edge s) = PsEdge := by
  funext u w
  exact propext (forget_edge_iff s u w)

theorem edge_unique_labels (s : Nat -> Bool) : UniqueLabels (Edge s) := by
  intro u w a b ha hb
  obtain ⟨_, ⟨hsa, hla⟩ | ⟨hsa, hla⟩⟩ := ha
  · obtain ⟨_, ⟨hsb, hlb⟩ | ⟨hsb, hlb⟩⟩ := hb
    · exact hla.trans hlb.symm
    · omega
  · obtain ⟨_, ⟨hsb, hlb⟩ | ⟨hsb, hlb⟩⟩ := hb
    · omega
    · exact hla.trans hlb.symm

private theorem bool_eq_complement_of_ne {a b : Bool} (h : a ≠ b) :
    a = !b := by
  cases a <;> cases b <;> simp_all

private theorem bool_ne_complement (a : Bool) : a ≠ !a := by
  cases a <;> decide

theorem incoming_each_label (s : Nat -> Bool) (w : Nat) (hw : 2 <= w)
    (label : Bool) : exists u, Edge s u w label := by
  by_cases h : label = row s w
  · exact ⟨w - 1, hw, Or.inl ⟨by omega, h⟩⟩
  · exact ⟨w - 2, hw, Or.inr ⟨by omega, bool_eq_complement_of_ne h⟩⟩

/-- Each label has at most one incoming parent in this particular graph. -/
theorem incoming_parent_unique (s : Nat -> Bool) (w : Nat) (label : Bool)
    {u v : Nat} (hu : Edge s u w label) (hv : Edge s v w label) : u = v := by
  obtain ⟨_, ⟨hsu, hlu⟩ | ⟨hsu, hlu⟩⟩ := hu
  · obtain ⟨_, ⟨hsv, hlv⟩ | ⟨hsv, hlv⟩⟩ := hv
    · omega
    · exact False.elim (bool_ne_complement (row s w) (hlu.symm.trans hlv))
  · obtain ⟨_, ⟨hsv, hlv⟩ | ⟨hsv, hlv⟩⟩ := hv
    · exact False.elim (bool_ne_complement (row s w) (hlv.symm.trans hlu))
    · omega

theorem incoming_parents_iff (s : Nat -> Bool) (w : Nat) (hw : 2 <= w)
    (u : Nat) : ForgetLabels (Edge s) u w ↔ u = w - 1 ∨ u = w - 2 := by
  rw [forget_edge_iff]
  unfold PsEdge
  omega

theorem two_distinct_parents (s : Nat -> Bool) (w : Nat) (hw : 2 <= w) :
    Edge s (w - 1) w (row s w) ∧
    Edge s (w - 2) w (!(row s w)) ∧ w - 1 ≠ w - 2 := by
  exact ⟨⟨hw, Or.inl ⟨by omega, rfl⟩⟩,
    ⟨hw, Or.inr ⟨by omega, rfl⟩⟩, by omega⟩

theorem roots_exactly_zero_one (s : Nat -> Bool) (v : Nat) :
    Root (ForgetLabels (Edge s)) v ↔ v = 0 ∨ v = 1 := by
  rw [forget_edge_eq]
  exact psRoot_iff v

theorem roots_finite (s : Nat -> Bool) :
    FiniteSupport (Root (ForgetLabels (Edge s))) := by
  refine ⟨[0, 1], ?_⟩
  intro v hv
  have := (roots_exactly_zero_one s v).mp hv
  simpa using this

theorem child_zero_iff (s : Nat -> Bool) (w : Nat) :
    ForgetLabels (Edge s) 0 w ↔ w = 2 := by
  rw [forget_edge_iff]
  unfold PsEdge
  omega

theorem children_positive_iff (s : Nat -> Bool) (u w : Nat) (hu : 1 <= u) :
    ForgetLabels (Edge s) u w ↔ w = u + 1 ∨ w = u + 2 := by
  rw [forget_edge_iff]
  unfold PsEdge
  omega

theorem children_finite (s : Nat -> Bool) (u : Nat) :
    FiniteSupport (ForgetLabels (Edge s) u) := by
  rw [forget_edge_eq]
  exact psChildren_finite u

/-- Non-strict natural-date sublevels, as used in the population manuscript. -/
theorem finite_birthdate_sublevel (date : Nat) :
    FiniteSupport (fun v => v <= date) :=
  (finiteSupport_iff_bounded _).mpr ⟨date + 1, fun _ h => by omega⟩

theorem edge_is_binaryNatPopulation (s : Nat -> Bool) :
    BinaryNatPopulation (Edge s) := by
  refine ⟨edge_unique_labels s, ?_, roots_finite s, ?_⟩
  · rw [forget_edge_eq]
    exact psNaturalDateBiosphere
  · intro w hroot label
    have hw : 2 <= w := by
      by_cases h : 2 <= w
      · exact h
      · have hr : Root (ForgetLabels (Edge s)) w :=
          (roots_exactly_zero_one s w).mpr (by omega)
        exact False.elim (hroot hr)
    exact incoming_each_label s w hw label

theorem edge_whole_specieslike (s : Nat -> Bool) :
    Specieslike (ForgetLabels (Edge s)) Whole := by
  rw [forget_edge_eq]
  exact psWhole_specieslike

theorem edge_whole_maximalSpecieslike (s : Nat -> Bool) :
    MaximalSpecieslike (ForgetLabels (Edge s)) Whole := by
  rw [forget_edge_eq]
  exact psWhole_maximalSpecieslike

theorem edge_whole_reflection (s : Nat -> Bool) :
    Reflection (ForgetLabels (Edge s)) Whole :=
  whole_reflection _

theorem edge_whole_not_commonAncestor (s : Nat -> Bool) :
    ¬ CommonAncestor (ForgetLabels (Edge s)) Whole := by
  rw [forget_edge_eq]
  exact psWhole_not_commonAncestor

theorem realizes_self_iff (s : Nat -> Bool) :
    Realizes (Edge s) s ↔ exists path, Matches s path := Iff.rfl

theorem edge_avoids_aperiodic_target (s : Nat -> Bool)
    (aperiodic : ¬ EventuallyPeriodic s) : ¬ Realizes (Edge s) s :=
  aperiodic_target_avoided s aperiodic

/-- The full, explicit negative endpoint for natural-date binary populations. -/
theorem explicit_specieslike_avoider (s : Nat -> Bool)
    (aperiodic : ¬ EventuallyPeriodic s) :
    BinaryNatPopulation (Edge s) ∧
    MaximalSpecieslike (ForgetLabels (Edge s)) Whole ∧
    Reflection (ForgetLabels (Edge s)) Whole ∧
    ¬ CommonAncestor (ForgetLabels (Edge s)) Whole ∧
    ¬ Realizes (Edge s) s :=
  ⟨edge_is_binaryNatPopulation s, edge_whole_maximalSpecieslike s,
    edge_whole_reflection s, edge_whole_not_commonAncestor s,
    edge_avoids_aperiodic_target s aperiodic⟩

theorem aperiodic_specieslike_counterexample (s : Nat -> Bool)
    (aperiodic : ¬ EventuallyPeriodic s) :
    exists E : LabelledGraph, BinaryNatPopulation E ∧
      MaximalSpecieslike (ForgetLabels E) Whole ∧
      Reflection (ForgetLabels E) Whole ∧
      ¬ CommonAncestor (ForgetLabels E) Whole ∧ ¬ Realizes E s :=
  ⟨Edge s, explicit_specieslike_avoider s aperiodic⟩

def SpecieslikeUnavoidable (s : Nat -> Bool) : Prop :=
  forall E : LabelledGraph, BinaryNatPopulation E ->
    Specieslike (ForgetLabels E) Whole -> Realizes E s

/-- Complete negative implication; no unavoidability theorem is assumed. -/
theorem specieslike_unavoidable_implies_eventuallyPeriodic (s : Nat -> Bool)
    (unavoidable : SpecieslikeUnavoidable s) : EventuallyPeriodic s := by
  classical
  by_cases periodic : EventuallyPeriodic s
  · exact periodic
  · have realizes := unavoidable (Edge s) (edge_is_binaryNatPopulation s)
      (edge_whole_specieslike s)
    exact False.elim (edge_avoids_aperiodic_target s periodic realizes)

/-- Conditional classification: the missing positive theorem is an explicit
parameter, whereas the negative endpoint is proved by the actual construction.
This is not an unconditional end-to-end formalization of the classification. -/
theorem specieslike_classification_of_positive
    (positive : forall (s : Nat -> Bool), EventuallyPeriodic s ->
      forall E : LabelledGraph, BinaryNatPopulation E -> Realizes E s)
    (s : Nat -> Bool) : SpecieslikeUnavoidable s ↔ EventuallyPeriodic s := by
  constructor
  · exact specieslike_unavoidable_implies_eventuallyPeriodic s
  · intro periodic E population _
    exact positive s periodic E population

end BinaryPopulation

#print axioms BinaryPopulation.forget_edge_eq
#print axioms BinaryPopulation.edge_is_binaryNatPopulation
#print axioms BinaryPopulation.explicit_specieslike_avoider
#print axioms BinaryPopulation.aperiodic_specieslike_counterexample
#print axioms BinaryPopulation.specieslike_unavoidable_implies_eventuallyPeriodic
#print axioms BinaryPopulation.specieslike_classification_of_positive
