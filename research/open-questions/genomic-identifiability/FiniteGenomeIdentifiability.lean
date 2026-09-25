import WongAlexander

/-!
A direct corollary of the checked opposite-completion theorem.
This concerns abstract population completions preserving a finite gARG's raw
edges and ancestry. It is not a theorem about DNA observation, biological
owner maps, statistical species-tree inference, or arbitrary species concepts.
No independent novelty is claimed for this elementary recovery obstruction.
-/
namespace FiniteGenomeIdentifiability
open AncestryViews SpeciesBridge SpeciesGlobalIAP WongAlexander
universe u v
variable {Node : Type u} {Coord : Type v} [Fintype Node] [LinearOrder Coord]

/-- A topology-compatible abstract completion, with both birth-date interfaces. -/
def Compatible (G : WongGARG.GARG Node Coord) (E : Graph) : Prop :=
  ∃ code : Node → Nat,
    Function.Injective code ∧
    RealDatedBiosphere E ∧ NaturalDateBiosphere E ∧
    FiniteSupport (Root E) ∧ WeaklyConnected E Whole ∧
    (∀ a b, E (code a) (code b) ↔ G.Topology a b) ∧
    (∀ a b, Descendant E (code a) (code b) ↔ Reach G.Topology a b)

/-- The same observed finite gARG admits both truth values of whole specieslikeness. -/
theorem opposite_compatible_completions (G : WongGARG.GARG Node Coord) :
    ∃ A B : Graph, Compatible G A ∧ Compatible G B ∧
      Specieslike A Whole ∧ ¬ Specieslike B Whole := by
  obtain ⟨code, A, B, injective, realA, realB, naturalA, naturalB,
    rootsA, rootsB, connectedA, connectedB, edges, paths,
    _inspeciesA, maximalA, notIAPB⟩ :=
      actual_garg_opposite_infinite_completions G
  refine ⟨A, B, ?_, ?_, maximalA.1, ?_⟩
  · exact ⟨code, injective, realA, naturalA, rootsA, connectedA,
      fun a b => (edges a b).1, fun a b => (paths a b).1⟩
  · exact ⟨code, injective, realB, naturalB, rootsB, connectedB,
      fun a b => (edges a b).2, fun a b => (paths a b).2⟩
  · intro speciesB
    exact notIAPB speciesB.2.1

/-- No verdict based only on this finite gARG is correct for all compatible completions. -/
theorem no_exact_specieslike_verdict (G : WongGARG.GARG Node Coord) :
    ¬ ∃ verdict : Prop, ∀ E : Graph, Compatible G E →
      (verdict ↔ Specieslike E Whole) := by
  rintro ⟨verdict, correct⟩
  obtain ⟨A, B, compatibleA, compatibleB, speciesA, notSpeciesB⟩ :=
    opposite_compatible_completions G
  exact notSpeciesB ((correct B compatibleB).mp ((correct A compatibleA).mpr speciesA))

/-- In particular, no chosen decoder of finite gARGs has that universal guarantee. -/
theorem no_exact_specieslike_decoder (G : WongGARG.GARG Node Coord)
    (decode : WongGARG.GARG Node Coord → Prop) :
    ¬ ∀ E : Graph, Compatible G E →
      (decode G ↔ Specieslike E Whole) := by
  intro correct
  exact no_exact_specieslike_verdict G ⟨decode G, correct⟩
end FiniteGenomeIdentifiability

#print axioms FiniteGenomeIdentifiability.opposite_compatible_completions
#print axioms FiniteGenomeIdentifiability.no_exact_specieslike_verdict
#print axioms FiniteGenomeIdentifiability.no_exact_specieslike_decoder
