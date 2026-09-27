import AncestryObservation
import WongAlexander

set_option autoImplicit false

/-! Instantiation in the repository's actual finite interval-gARG structure.
Only graph observation/processing is transferred. No claim about the marked
stochastic ARG generator, organism ownership, or biological species is made. -/
namespace WongPredictiveBridge
open AncestryViews AncestryObservation SpeciesBridge

universe u v
variable {Node : Type u} {Coord : Type v} [Fintype Node] [LinearOrder Coord]

theorem extracted_is_compress (G : WongGARG.GARG Node Coord) (x : Coord) :
    G.ExtractedAt x = compress (fun s => s ∈ G.samples) (G.AtLocus x) := by
  funext a b
  exact propext (WongAlexander.extracted_edge_iff_restrict G x a b)

/-- A genuine controlled commutation instance, with controls interpreted as
successive graph restrictions to subsets of the original sample set. -/
theorem actual_garg_restriction_all_words (G : WongGARG.GARG Node Coord) (x : Coord)
    (word : List (Action (fun s => s ∈ G.samples))) :
    compress (fun s => s ∈ G.samples)
      (PredictiveState.run (restrictStep (fun s => s ∈ G.samples)) word (G.AtLocus x)) =
    PredictiveState.run (restrictStep (fun s => s ∈ G.samples)) word (G.ExtractedAt x) := by
  rw [extracted_is_compress]
  exact restriction_all_words _ _ _

def finiteView (code : Node → Nat) (E : Graph) :
    (Node → Node → Prop) × (Node → Node → Prop) :=
  (fun a b => E (code a) (code b), fun a b => Descendant E (code a) (code b))

/-- Even the exact old edges AND old ancestry paths cannot decide global IAP
over all admissible infinite completions. This is a consequence of the existing
opposite-completion theorem, not a new biological classification theorem. -/
theorem no_global_iap_decoder (G : WongGARG.GARG Node Coord) :
    ∃ code : Node → Nat, Function.Injective code ∧
      ¬ ∃ decode : ((Node → Node → Prop) × (Node → Node → Prop)) → Prop,
        ∀ E : Graph, WongAlexander.RealDatedBiosphere E →
          FiniteSupport (Root E) → WeaklyConnected E Whole →
          finiteView code E = (G.Topology, fun a b => Reach G.Topology a b) →
          (decode (finiteView code E) ↔ IAP E Whole) := by
  obtain ⟨code, E, F, injective, realE, realF, _, _, rootsE, rootsF, connectedE, connectedF,
    edges, paths, _, maximalE, notIAPF⟩ :=
      WongAlexander.actual_garg_opposite_infinite_completions G
  refine ⟨code, injective, ?_⟩
  rintro ⟨decode, correct⟩
  have viewE : finiteView code E = (G.Topology, fun a b => Reach G.Topology a b) := by
    apply Prod.ext
    · funext a b
      exact propext (edges a b).1
    · funext a b
      exact propext (paths a b).1
  have viewF : finiteView code F = (G.Topology, fun a b => Reach G.Topology a b) := by
    apply Prod.ext
    · funext a b
      exact propext (edges a b).2
    · funext a b
      exact propext (paths a b).2
  have observed : decode (finiteView code E) :=
    (correct E realE rootsE connectedE viewE).mpr maximalE.1.2.1
  rw [viewE.trans viewF.symm] at observed
  exact notIAPF ((correct F realF rootsF connectedF viewF).mp observed)

end WongPredictiveBridge
