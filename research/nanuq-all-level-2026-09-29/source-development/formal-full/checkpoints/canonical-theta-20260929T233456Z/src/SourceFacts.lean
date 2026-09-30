import GraphGalls
import GraphPorts
import GraphBlobs
import GraphSwitchingCuts
import GraphSwitchingFinite
import GraphBridgeSplits
import SourceResolve

namespace Nanuq.Source.RootedBinary

variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]

/-- Proved raw graph prerequisites for the later metric theorem.
This is not the source metric theorem or canonical-blob coverage. -/
theorem raw_graph_foundations (N : RootedBinary V E X) (hg : N.graph.GalledDetour) :
    N.graph.bridgeQuotient.IsTree ∧
    ∀ e, N.graph.IsBridge e →
      ¬ N.graph.IsHybrid (N.graph.target e) ∧
      0 < (N.sideTaxa e (N.graph.source e)).card ∧
      0 < (N.sideTaxa e (N.graph.target e)).card ∧
      (N.sideTaxa e (N.graph.source e)).card +
        (N.sideTaxa e (N.graph.target e)).card = Fintype.card X := by
  refine ⟨N.blob_quotient_is_tree, ?_⟩
  intro e he
  exact ⟨N.graph.galled_bridge_not_hybrid_target hg he, N.bridge_port_masses he⟩

/-- Every actual switching supplies a proved raw quartet resolution and the
distinct displayed quartet set is nonempty. No resolver is an input. -/
theorem raw_quartet_foundations (N : RootedBinary V E X) :
    (∀ S : N.Switching, S.graph.IsTree) ∧
    (∀ (S : N.Switching) (q : Fin 4 ↪ X),
      S.graph.Resolves (fun i => N.leaf (q i)) (S.resolve q)) ∧
    (∀ q : Fin 4 ↪ X, (N.rawDisplayedQuartets q).Nonempty) :=
  ⟨fun S => S.selected_is_tree, fun S q => S.resolve_spec q,
    fun q => N.rawDisplayedQuartets_nonempty q⟩

end Nanuq.Source.RootedBinary

#print axioms Nanuq.Source.RootedBinary.raw_graph_foundations
#print axioms Nanuq.Source.RootedBinary.raw_quartet_foundations
#print axioms Nanuq.Source.RootedBinary.rawQuartetMean_of_bridge
