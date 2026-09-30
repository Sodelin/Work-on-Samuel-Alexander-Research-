import ThetaSwitchingEdges
import CircularBasis

/-! The executable displayed-split predicate has exactly the intended
existential edge/circular-interval semantics. -/
namespace Nanuq.Theta

open Nanuq.Reconstruction

def pathRealizesGap (t : Counts) (s : Switching) (z : Vertex)
    (i j : Fin (circular t).length) : Prop :=
  (∀ k, z ∈ terminalPath t s (leafIndex t k) ↔ inArc i j k) ∨
  (∀ k, z ∈ terminalPath t s (leafIndex t k) ↔ ¬ inArc i j k)

private theorem side_compare_iff (t : Counts) (s : Switching) (z : Vertex) (i j k : Nat) :
    (decide (z ∈ terminalPath t s (leafAt t k)) == onGapSide i j k) = true ↔
      (z ∈ terminalPath t s (leafAt t k) ↔ i < k ∧ k ≤ j) := by
  unfold onGapSide
  by_cases hp : z ∈ terminalPath t s (leafAt t k) <;>
    by_cases hq : i < k ∧ k ≤ j <;> simp [hp,hq]

private theorem complement_compare_iff (t : Counts) (s : Switching) (z : Vertex) (i j k : Nat) :
    (decide (z ∈ terminalPath t s (leafAt t k)) == !(onGapSide i j k)) = true ↔
      (z ∈ terminalPath t s (leafAt t k) ↔ ¬ (i < k ∧ k ≤ j)) := by
  unfold onGapSide
  by_cases hp : z ∈ terminalPath t s (leafAt t k) <;>
    by_cases hq : i < k ∧ k ≤ j <;> simp [hp,hq]

theorem all_gap_side_iff (t : Counts) (s : Switching) (z : Vertex)
    (i j : Fin (circular t).length) :
    ((List.range (circular t).length).all fun k =>
      decide (z ∈ terminalPath t s (leafAt t k)) == onGapSide i.val j.val k) = true ↔
      ∀ k, z ∈ terminalPath t s (leafIndex t k) ↔ inArc i j k := by
  rw [List.all_eq_true]
  constructor
  · intro h k
    exact (side_compare_iff t s z i.val j.val k.val).mp (h k.val (List.mem_range.mpr k.isLt))
  · intro h k hk
    exact (side_compare_iff t s z i.val j.val k).mpr (h ⟨k,List.mem_range.mp hk⟩)

theorem all_gap_complement_iff (t : Counts) (s : Switching) (z : Vertex)
    (i j : Fin (circular t).length) :
    ((List.range (circular t).length).all fun k =>
      decide (z ∈ terminalPath t s (leafAt t k)) == !(onGapSide i.val j.val k)) = true ↔
      ∀ k, z ∈ terminalPath t s (leafIndex t k) ↔ ¬ inArc i j k := by
  rw [List.all_eq_true]
  constructor
  · intro h k
    exact (complement_compare_iff t s z i.val j.val k.val).mp (h k.val (List.mem_range.mpr k.isLt))
  · intro h k hk
    exact (complement_compare_iff t s z i.val j.val k).mpr (h ⟨k,List.mem_range.mp hk⟩)

@[simp] theorem mem_switchings (s : Switching) : s ∈ switchings := by
  rcases s with ⟨s1,s2⟩
  cases s1 <;> cases s2 <;> simp [switchings]

/-- This bridge does not assume positivity or any finite arm-length bound.
The Boolean evaluator searches precisely the real switching edges. -/
theorem displayedSplit_iff (t : Counts) (i j : Fin (circular t).length) :
    displayedSplit t i.val j.val = true ↔
      ∃ s y z, (y,z) ∈ switchingEdges t s ∧ pathRealizesGap t s z i j := by
  unfold displayedSplit
  constructor
  · intro h
    obtain ⟨s,_hs,he⟩ := List.any_eq_true.mp h
    obtain ⟨⟨y,z⟩,hyz,hside⟩ := List.any_eq_true.mp he
    refine ⟨s,y,z,hyz,?_⟩
    simp only [Bool.or_eq_true] at hside
    rcases hside with h | h
    · exact Or.inl ((all_gap_side_iff t s z i j).mp h)
    · exact Or.inr ((all_gap_complement_iff t s z i j).mp h)
  · rintro ⟨s,y,z,he,hgap⟩
    apply List.any_eq_true.mpr
    refine ⟨s,mem_switchings s,?_⟩
    apply List.any_eq_true.mpr
    refine ⟨(y,z),he,?_⟩
    simp only [Bool.or_eq_true]
    rcases hgap with h | h
    · exact Or.inl ((all_gap_side_iff t s z i j).mpr h)
    · exact Or.inr ((all_gap_complement_iff t s z i j).mpr h)

#print axioms displayedSplit_iff
end Nanuq.Theta