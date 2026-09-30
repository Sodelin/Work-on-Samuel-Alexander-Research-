import ThetaPathLengths
import ThetaSupport

/-! Concrete switched-tree descendant predicates and edge existence. -/
namespace Nanuq.Theta

@[simp] theorem arm_mem_terminalPath (t : Counts) (s : Switching) (x : Leaf)
    (k : Fin 4) (r : Nat) :
    Vertex.arm k r ∈ terminalPath t s x ↔
      switchedArm s x = k ∧ r < attachmentDepth t s x := by
  rw [terminalPath_eq_based]
  by_cases hp : (switchedArm s x).val % 2 = 1 <;>
    simp [armPath, hp, List.mem_map, eq_comm, and_comm]

@[simp] theorem v_mem_terminalPath (t : Counts) (s : Switching) (x : Leaf) :
    Vertex.v ∈ terminalPath t s x ↔ (switchedArm s x).val % 2 = 1 := by
  rw [terminalPath_eq_based]
  by_cases hp : (switchedArm s x).val % 2 = 1 <;>
    simp [armPath, hp, List.mem_map]

@[simp] theorem terminal_mem_terminalPath (t : Counts) (s : Switching) (x y : Leaf) :
    Vertex.terminal y ∈ terminalPath t s x ↔ y = x := by
  rw [terminalPath_eq_based]
  by_cases hp : (switchedArm s x).val % 2 = 1 <;>
    simp [armPath, hp, List.mem_map]

@[simp] theorem u_mem_terminalPath (t : Counts) (s : Switching) (x : Leaf) :
    Vertex.u ∈ terminalPath t s x := by
  rw [terminalPath_eq_based]
  simp [armPath]

/-- Every list entry after the head is a child in some adjacent pair. -/
theorem exists_predecessor_of_mem_tail {A : Type*} (l : List A) (x : A)
    (hx : x ∈ l.tail) : ∃ y, (y,x) ∈ l.zip l.tail := by
  cases l with
  | nil => simp at hx
  | cons a rest =>
    induction rest generalizing a with
    | nil => simp at hx
    | cons b bs ih =>
      simp only [List.tail_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ⟨a, by simp⟩
      · obtain ⟨y,hy⟩ := ih b hx
        exact ⟨y, by simpa using List.mem_cons_of_mem (a,b) hy⟩

theorem nonroot_mem_terminalPath_tail (t : Counts) (s : Switching) (x : Leaf)
    (z : Vertex) (hz : z ∈ terminalPath t s x) (hzu : z ≠ Vertex.u) :
    z ∈ (terminalPath t s x).tail := by
  rw [terminalPath_eq_based, based_path_eq] at hz ⊢
  simp only [List.tail_cons, List.mem_cons] at hz ⊢
  exact hz.resolve_left hzu

/-- A non-root vertex on a valid taxon's path is the child of an actual
switching edge, not merely an abstract descendant-set predicate. -/
theorem exists_switching_edge_of_path (t : Counts) (s : Switching) (x : Leaf)
    (hx : x ∈ circular t) (z : Vertex)
    (hz : z ∈ terminalPath t s x) (hzu : z ≠ Vertex.u) :
    ∃ y, (y,z) ∈ switchingEdges t s := by
  obtain ⟨y,hy⟩ := exists_predecessor_of_mem_tail (terminalPath t s x) z
    (nonroot_mem_terminalPath_tail t s x z hz hzu)
  refine ⟨y, ?_⟩
  simp only [switchingEdges, List.mem_eraseDups, List.mem_flatMap]
  exact ⟨x,hx,hy⟩

#print axioms arm_mem_terminalPath
#print axioms exists_switching_edge_of_path
end Nanuq.Theta