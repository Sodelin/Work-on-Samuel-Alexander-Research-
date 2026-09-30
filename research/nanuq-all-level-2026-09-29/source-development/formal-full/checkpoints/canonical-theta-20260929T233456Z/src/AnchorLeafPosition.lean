import AnchorCompressionOrder
import ThetaPathMembership

/-! Explicit canonical positions; these are proved inverse to the evaluator's list indexing. -/
namespace Nanuq.Theta

private theorem getD_middle {A : Type*} (pre mid post : List A) (d : A)
    (i : Nat) (hi : i < mid.length) :
    (pre ++ mid ++ post).getD (pre.length + i) d = mid.getD i d := by
  simp only [List.append_assoc, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (Nat.le_add_right _ _)]
  simp only [Nat.add_sub_cancel_left]
  rw [List.getElem?_append_left hi]

private theorem range_arm_getD (k : Fin 4) (n j : Nat) (hj : j < n) :
    ((List.range n).map (Leaf.arm k)).getD j Leaf.c1 = Leaf.arm k j := by
  rw [← List.getElem_eq_getD (h := by simpa using hj) Leaf.c1]
  simp

private theorem reverse_range_arm_getD (k : Fin 4) (n j : Nat) (hj : j < n) :
    ((List.range n).reverse.map (Leaf.arm k)).getD (n - 1 - j) Leaf.c1 = Leaf.arm k j := by
  rw [← List.getElem_eq_getD (h := by simpa using (show n - 1 - j < n by omega)) Leaf.c1]
  simp only [List.getElem_map, List.getElem_reverse, List.length_range,
    List.getElem_range]
  congr 1
  omega

def leafPosition (t : Counts) : Leaf → Nat
  | Leaf.c1 => 0
  | Leaf.c2 => 1 + t.b1 + t.b2
  | Leaf.arm k j =>
      if k = 0 then 2 + t.b1 + t.b2 + t.a2 + j
      else if k = 1 then t.b1 - j
      else if k = 2 then 1 + t.b1 + t.b2 + t.a2 - j
      else 1 + t.b1 + j

theorem leafPosition_lt (t : Counts) {x : Leaf} (hx : x ∈ circular t) :
    leafPosition t x < (circular t).length := by
  rw [circular_length]
  cases x with
  | c1 => simp [leafPosition, Counts.total]
  | c2 => simp only [leafPosition, Counts.total]; omega
  | arm k j =>
    have hj := (arm_mem_circular_iff t k j).mp hx
    fin_cases k <;> simp +decide [Counts.armLength, leafPosition, Counts.total] at hj ⊢ <;> omega

theorem leafAt_leafPosition (t : Counts) {x : Leaf} (hx : x ∈ circular t) :
    leafAt t (leafPosition t x) = x := by
  cases x with
  | c1 => simp [leafAt, leafPosition, circular]
  | c2 =>
    have hm := getD_middle
      ([Leaf.c1] ++ ((List.range t.b1).reverse.map (Leaf.arm 1)) ++
        ((List.range t.b2).map (Leaf.arm 3)))
      [Leaf.c2]
      (((List.range t.a2).reverse.map (Leaf.arm 2)) ++
        ((List.range t.a1).map (Leaf.arm 0))) Leaf.c1 0 (by simp)
    simp only [List.length_append, List.length_map, List.length_reverse, List.length_range,
      List.length_singleton, Nat.add_zero, List.getD_cons_zero] at hm
    simpa only [leafAt, leafPosition, circular, List.append_assoc] using hm
  | arm k j =>
    have hj := (arm_mem_circular_iff t k j).mp hx
    fin_cases k
    · have hj' : j < t.a1 := by simpa [Counts.armLength] using hj
      have hm := getD_middle
        ([Leaf.c1] ++ ((List.range t.b1).reverse.map (Leaf.arm 1)) ++
          ((List.range t.b2).map (Leaf.arm 3)) ++ [Leaf.c2] ++
          ((List.range t.a2).reverse.map (Leaf.arm 2)))
        ((List.range t.a1).map (Leaf.arm 0)) [] Leaf.c1 j (by simpa using hj')
      rw [range_arm_getD _ _ _ hj'] at hm
      simpa [leafAt, leafPosition, circular, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hm
    · have hj' : j < t.b1 := by simpa [Counts.armLength] using hj
      have hm := getD_middle [Leaf.c1]
        ((List.range t.b1).reverse.map (Leaf.arm 1))
        (((List.range t.b2).map (Leaf.arm 3)) ++ [Leaf.c2] ++
          ((List.range t.a2).reverse.map (Leaf.arm 2)) ++
          ((List.range t.a1).map (Leaf.arm 0))) Leaf.c1 (t.b1 - 1 - j)
        (by simpa using (show t.b1 - 1 - j < t.b1 by omega))
      rw [reverse_range_arm_getD _ _ _ hj'] at hm
      have he : 1 + (t.b1 - 1 - j) = t.b1 - j := by omega
      simpa [leafAt, leafPosition, circular, List.append_assoc, he] using hm
    · have hj' : j < t.a2 := by simpa [Counts.armLength] using hj
      have hm := getD_middle
        ([Leaf.c1] ++ ((List.range t.b1).reverse.map (Leaf.arm 1)) ++
          ((List.range t.b2).map (Leaf.arm 3)) ++ [Leaf.c2])
        ((List.range t.a2).reverse.map (Leaf.arm 2))
        ((List.range t.a1).map (Leaf.arm 0)) Leaf.c1 (t.a2 - 1 - j)
        (by simpa using (show t.a2 - 1 - j < t.a2 by omega))
      rw [reverse_range_arm_getD _ _ _ hj'] at hm
      have he : 1 + t.b1 + t.b2 + 1 + (t.a2 - 1 - j) =
          1 + t.b1 + t.b2 + t.a2 - j := by omega
      simp only [List.length_append, List.length_map, List.length_reverse, List.length_range,
        List.length_singleton, Nat.add_zero] at hm
      rw [he] at hm
      simpa +decide [leafAt, leafPosition, circular] using hm
    · have hj' : j < t.b2 := by simpa [Counts.armLength] using hj
      have hm := getD_middle
        ([Leaf.c1] ++ ((List.range t.b1).reverse.map (Leaf.arm 1)))
        ((List.range t.b2).map (Leaf.arm 3))
        ([Leaf.c2] ++ ((List.range t.a2).reverse.map (Leaf.arm 2)) ++
          ((List.range t.a1).map (Leaf.arm 0))) Leaf.c1 j (by simpa using hj')
      rw [range_arm_getD _ _ _ hj'] at hm
      simp only [List.length_append, List.length_map, List.length_reverse, List.length_range,
        List.length_singleton] at hm
      simpa +decide [leafAt, leafPosition, circular, List.append_assoc, Nat.add_comm, Nat.add_left_comm] using hm

theorem leafPosition_leafIndex (t : Counts) (i : Fin (circular t).length) :
    leafPosition t (leafIndex t i) = i.val := by
  let j : Fin (circular t).length :=
    ⟨leafPosition t (leafIndex t i), leafPosition_lt t (leafIndex_mem_circular t i)⟩
  have hji : leafIndex t j = leafIndex t i :=
    leafAt_leafPosition t (leafIndex_mem_circular t i)
  exact congrArg Fin.val ((leafIndex_injective t) hji)

#print axioms leafAt_leafPosition
#print axioms leafPosition_leafIndex
end Nanuq.Theta


