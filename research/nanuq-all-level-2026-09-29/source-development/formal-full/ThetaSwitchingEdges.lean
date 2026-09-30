import ThetaPathMembership

namespace Nanuq.Theta

@[simp] theorem u_not_mem_terminalPath_tail (t : Counts) (s : Switching) (x : Leaf) :
    Vertex.u ∉ (terminalPath t s x).tail := by
  rw [terminalPath_eq_based, based_path_eq]
  simp only [List.tail_cons]
  by_cases hp : (switchedArm s x).val % 2 = 1 <;>
    simp [hp, armTailPath, List.mem_map]

/-- Conversely, an actual switching edge has a non-root child that occurs on
at least one valid leaf path. Together with the forward theorem this eliminates
all artificial or empty descendant predicates from the support argument. -/
theorem switching_edge_child_spec (t : Counts) (s : Switching) (y z : Vertex)
    (he : (y,z) ∈ switchingEdges t s) :
    z ≠ Vertex.u ∧ ∃ x ∈ circular t, z ∈ terminalPath t s x := by
  simp only [switchingEdges, List.mem_eraseDups, List.mem_flatMap] at he
  obtain ⟨x,hx,hpair⟩ := he
  have htail := (List.of_mem_zip hpair).2
  refine ⟨?_,x,hx,?_⟩
  · intro hz
    subst z
    exact u_not_mem_terminalPath_tail t s x htail
  · exact List.mem_of_mem_tail htail

theorem exists_switching_edge_iff (t : Counts) (s : Switching) (z : Vertex) :
    (∃ y, (y,z) ∈ switchingEdges t s) ↔
      z ≠ Vertex.u ∧ ∃ x ∈ circular t, z ∈ terminalPath t s x := by
  constructor
  · rintro ⟨y,hy⟩
    exact switching_edge_child_spec t s y z hy
  · rintro ⟨hzu,x,hx,hz⟩
    exact exists_switching_edge_of_path t s x hx z hz hzu

#print axioms switching_edge_child_spec
#print axioms exists_switching_edge_iff
end Nanuq.Theta