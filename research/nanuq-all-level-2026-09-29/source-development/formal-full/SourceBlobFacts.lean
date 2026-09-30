import SourceFacts
import GraphMedianUnique
import GraphPortFibers

namespace Nanuq.Source.RootedBinary

variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]

/-- Actual quotient ports are exhaustive positive taxon fibers, and each triple
has one unique branching blob. These are derived graph facts, not input fields. -/
theorem raw_blob_foundations (N : RootedBinary V E X) :
    (∀ (b : N.graph.Blob) (hb : N.NonleafBlob b),
      Function.Surjective (N.blobProjection b hb) ∧
        ∀ p : N.BlobPort b, 0 < (N.portTaxa b hb p).card) ∧
    (∀ q : Fin 3 ↪ X, ∃! b, N.ThreeWayBlob q b) :=
  ⟨fun b hb => ⟨N.blobProjection_surjective b hb,
    fun p => N.actual_port_mass_positive b hb p⟩,
    fun q => N.existsUnique_three_way_blob q⟩

end Nanuq.Source.RootedBinary

#print axioms Nanuq.Source.RootedBinary.raw_blob_foundations
#print axioms Nanuq.Source.RootedBinary.port_transport_between_blobs
