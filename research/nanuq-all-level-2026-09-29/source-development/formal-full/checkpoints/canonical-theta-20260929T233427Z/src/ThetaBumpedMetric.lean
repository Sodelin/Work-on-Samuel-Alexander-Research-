import ThetaPathLengths

namespace Nanuq.Theta

theorem hDistance_comm (k r : Fin 4) (m n : Nat) :
    hDistance k r m n = hDistance r k n m := by
  by_cases hkr : k = r
  · subst r
    simp [hDistance, Nat.add_comm]
  · simp [hDistance, hkr, Ne.symm hkr, eq_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

theorem hDistance_raise_left (k r : Fin 4) (m n : Nat) (h : k = r → n ≤ m) :
    hDistance k r (m + 1) n = hDistance k r m n + 1 := by
  by_cases hkr : k = r
  · subst r
    have hn := h rfl
    simp [hDistance]
    omega
  · simp [hDistance, hkr]
    omega

theorem hDistance_raise_right (k r : Fin 4) (m n : Nat) (h : k = r → m ≤ n) :
    hDistance k r m (n + 1) = hDistance k r m n + 1 := by
  calc
    hDistance k r m (n + 1) = hDistance r k (n + 1) m := hDistance_comm _ _ _ _
    _ = hDistance r k n m + 1 := hDistance_raise_left r k n m (fun e => h e.symm)
    _ = hDistance k r m n + 1 := by rw [hDistance_comm r k n m]

theorem attachmentDepth_le (t : Counts) (s : Switching) (x : Leaf) (hx : x ∈ circular t) :
    attachmentDepth t s x ≤ t.armLength (switchedArm s x) := by
  cases x with
  | c1 => rfl
  | c2 => rfl
  | arm k j =>
    have hj := (arm_mem_circular_iff t k j).mp hx
    dsimp only [attachmentDepth, switchedArm]
    omega

theorem hybridBump_cases (x : Leaf) : hybridBump x = 0 ∨ hybridBump x = 1 := by
  cases x <;> simp [hybridBump]

theorem hybrid_depth_eq (t : Counts) (s : Switching) (x : Leaf) (hx : hybridBump x = 1) :
    attachmentDepth t s x = t.armLength (switchedArm s x) := by
  cases x <;> simp_all [hybridBump, attachmentDepth]

theorem switched_hybrids_different (s : Switching) (x y : Leaf)
    (hx : hybridBump x = 1) (hy : hybridBump y = 1) (hxy : x ≠ y) :
    switchedArm s x ≠ switchedArm s y := by
  rcases s with ⟨s1,s2⟩
  cases x <;> cases y <;> cases s1 <;> cases s2 <;>
    simp_all [hybridBump, switchedArm]

/-- Raising each hybrid pendant edge by one yields strictly positive arm
positions. Every pair distance changes by exactly its two pendant increments. -/
theorem metricPosition_distance (t : Counts) (s : Switching) (x y : Leaf)
    (hx : x ∈ circular t) (hy : y ∈ circular t) (hxy : x ≠ y) :
    hDistance (switchedArm s x) (switchedArm s y)
      (metricPosition t s x) (metricPosition t s y) =
      treeDistance t s x y + hybridBump x + hybridBump y := by
  rw [treeDistance_eq_hDistance t s x y hxy]
  dsimp only [metricPosition]
  rcases hybridBump_cases x with hx0 | hx1 <;> rcases hybridBump_cases y with hy0 | hy1
  · simp [hx0,hy0]
  · simp only [hx0,hy1,Nat.add_zero]
    apply hDistance_raise_right
    intro heq
    rw [hybrid_depth_eq t s y hy1]
    simpa only [heq] using attachmentDepth_le t s x hx
  · simp only [hx1,hy0,Nat.add_zero]
    apply hDistance_raise_left
    intro heq
    rw [hybrid_depth_eq t s x hx1]
    simpa only [heq] using attachmentDepth_le t s y hy
  · have hne := switched_hybrids_different s x y hx1 hy1 hxy
    simp only [hx1,hy1,hDistance,if_neg hne]
    omega

#print axioms metricPosition_distance
end Nanuq.Theta
