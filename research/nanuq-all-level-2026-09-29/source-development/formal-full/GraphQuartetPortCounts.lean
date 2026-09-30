import GraphMedianUnique
import AnchorPortCounts

/-! Four-triple counts for the actual port projections of raw RootedBinary
networks. Existence and uniqueness come from the proved graph median theorem. -/
namespace Nanuq.Source.RootedBinary

open scoped BigOperators
open Nanuq.PortPatterns
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X)

noncomputable def quartetPortMap (q : Fin 4 ↪ X)
    (b : {b : N.graph.Blob // N.NonleafBlob b}) : Fin 4 → N.BlobPort b.val :=
  fun i => N.blobProjection b.val b.property (q i)

theorem unique_omitted_triple_port (q : Fin 4 ↪ X) (i : Fin 4) :
    ∃! b : {b : N.graph.Blob // N.NonleafBlob b}, tripleInjective (N.quartetPortMap q b) i := by
  classical
  let q3 : Fin 3 ↪ X := (omitTriple i).trans q
  obtain ⟨b,⟨hb,hbi⟩,hu⟩ := N.existsUnique_three_way_blob q3
  refine ⟨⟨b,hb⟩,?_,?_⟩
  · exact hbi
  · intro c hc
    apply Subtype.ext
    exact hu c.val ⟨c.property,hc⟩

theorem sum_quartet_tripleCount (q : Fin 4 ↪ X) :
    (∑ b : {b : N.graph.Blob // N.NonleafBlob b}, tripleCount (N.quartetPortMap q b)) = 4 := by
  classical
  exact sum_tripleCount_of_unique (N.quartetPortMap q) (N.unique_omitted_triple_port q)

/-- The actual raw graph has either one four-port median blob and no
three-port median blobs, or exactly two three-port median blobs and no
four-port median blob, for every injected quartet. -/
theorem quartet_branching_port_counts (q : Fin 4 ↪ X) :
    ((Finset.univ.filter (fun b : {b : N.graph.Blob // N.NonleafBlob b} =>
        portCount (N.quartetPortMap q b) = 4)).card = 1 ∧
      (Finset.univ.filter (fun b : {b : N.graph.Blob // N.NonleafBlob b} =>
        portCount (N.quartetPortMap q b) = 3)).card = 0) ∨
    ((Finset.univ.filter (fun b : {b : N.graph.Blob // N.NonleafBlob b} =>
        portCount (N.quartetPortMap q b) = 4)).card = 0 ∧
      (Finset.univ.filter (fun b : {b : N.graph.Blob // N.NonleafBlob b} =>
        portCount (N.quartetPortMap q b) = 3)).card = 2) := by
  classical
  exact branching_port_counts_of_unique (N.quartetPortMap q) (N.unique_omitted_triple_port q)

#print axioms unique_omitted_triple_port
#print axioms sum_quartet_tripleCount
#print axioms quartet_branching_port_counts
end Nanuq.Source.RootedBinary