import FounderMaximal
import SpeciesReindex
import SpeciesSeed

/-! The complete existence result in the original real-birthdate graph.
The rank enumeration is internal to the proof. Both the conclusion and every
maximality competitor use the original graph, birth function, and real duration. -/
namespace RealSpeciesTheorem
open SpeciesBridge FounderMaximal SpeciesReindex

noncomputable section

theorem windowSpecies_iff {birth : Nat → ℝ} (e : BirthOrder.OrderedEnumeration birth)
    (E : Graph) (S : NatSet) (duration : ℝ) :
    WindowSpecies (pullGraph e E) (pulledBirth e) duration (pullSet e S) ↔
      WindowSpecies E birth duration S :=
  and_congr (specieslike_iff e E S)
    (and_congr (reflection_iff e E S) (window_iff e E S duration))

theorem push_maximal {birth : Nat → ℝ} (e : BirthOrder.OrderedEnumeration birth)
    (E : Graph) (duration : ℝ) (T : NatSet)
    (hT : MaximalWindowSpecies (pullGraph e E) (pulledBirth e) duration T) :
    MaximalWindowSpecies E birth duration (pushSet e T) := by
  refine ⟨(windowSpecies_iff e E (pushSet e T) duration).mp ?_, ?_⟩
  · simpa only [pull_push] using hT.1
  · intro U hTU hU v hv
    have hinc : ∀ i, T i → pullSet e U i := by
      intro i hi
      apply hTU (e.toFun i)
      simpa only [pushSet, e.index_toFun] using hi
    have hback := hT.2 (pullSet e U) hinc ((windowSpecies_iff e E U duration).mpr hU)
    exact hback (e.index v) (by simpa only [pullSet, e.toFun_index] using hv)

/-- Conditional extension in the actual graph, with no Nat ordering premise. -/
theorem maximal_window_extension (E : Graph) (birth : Nat → ℝ)
    (finite : RealFounderWindow.StrictFiniteSublevels birth)
    (chronological : RealFounderWindow.Chronological E birth)
    (children : ∀ v, FiniteSupport (E v))
    (duration : ℝ) (S : NatSet) (hS : WindowSpecies E birth duration S) :
    ∃ M, (∀ v, S v → M v) ∧ MaximalWindowSpecies E birth duration M := by
  let e := actualEnumeration birth finite
  obtain ⟨T, hST, hT⟩ := maximal_window_extension_ordered
    (pullGraph_strict e E chronological) (pulled_finite_children e E children)
    (pulled_strict_sublevels e finite) duration (pullSet e S)
    ((windowSpecies_iff e E S duration).mpr hS)
  refine ⟨pushSet e T, ?_, push_maximal e E duration T hT⟩
  intro v hv
  exact hST (e.index v) (by simpa only [pullSet, e.toFun_index] using hv)

/-- The per-organism seed is proved, rather than supplied as an assumption. -/
theorem every_vertex_has_seed (E : Graph) (birth : Nat → ℝ)
    (finite : RealFounderWindow.StrictFiniteSublevels birth)
    (chronological : RealFounderWindow.Chronological E birth)
    (children : ∀ v, FiniteSupport (E v)) (v : Nat) :
    ∃ S, S v ∧ Specieslike E S ∧ CommonAncestor E S ∧ Reflection E S := by
  let e := actualEnumeration birth finite
  obtain ⟨T, hv, hspec, hCA, hREF⟩ := SpeciesSeed.exists_seed (pullGraph e E)
    (pullGraph_strict e E chronological) (pulled_finite_children e E children) (e.index v)
  refine ⟨pushSet e T, hv, ?_, ?_, ?_⟩
  · apply (specieslike_iff e E (pushSet e T)).mp
    simpa only [pull_push] using hspec
  · apply (commonAncestor_iff e E (pushSet e T)).mp
    simpa only [pull_push] using hCA
  · apply (reflection_iff e E (pushSet e T)).mp
    simpa only [pull_push] using hREF

/-- Every organism belongs to a maximal connected, convex, IAP, reflecting
cluster with founders confined to any prescribed nonnegative real birth window.
Maximality is among clusters with those same fixed constraints. -/
theorem every_vertex_in_maximal_real_window (E : Graph) (birth : Nat → ℝ)
    (finite : RealFounderWindow.StrictFiniteSublevels birth)
    (chronological : RealFounderWindow.Chronological E birth)
    (children : ∀ v, FiniteSupport (E v))
    (duration : ℝ) (nonnegative : 0 ≤ duration) (v : Nat) :
    ∃ M, M v ∧ MaximalWindowSpecies E birth duration M := by
  obtain ⟨S, hv, hspec, hCA, hREF⟩ :=
    every_vertex_has_seed E birth finite chronological children v
  have hS : WindowSpecies E birth duration S :=
    ⟨hspec, hREF, RealFounderWindow.commonAncestor_window chronological hCA duration nonnegative⟩
  obtain ⟨M, hSM, hM⟩ := maximal_window_extension E birth finite chronological children duration S hS
  exact ⟨M, hSM v hv, hM⟩

end
end RealSpeciesTheorem
#print axioms RealSpeciesTheorem.windowSpecies_iff
#print axioms RealSpeciesTheorem.push_maximal
#print axioms RealSpeciesTheorem.maximal_window_extension
#print axioms RealSpeciesTheorem.every_vertex_has_seed
#print axioms RealSpeciesTheorem.every_vertex_in_maximal_real_window
