import ThetaPathLengths

/-! The actual switched H-tree point ordering is preserved by arm compression. -/
namespace Nanuq.Theta

@[simp] theorem switchedArm_compressLeaf (W : Finset Leaf) (s : Switching) (x : Leaf) :
    switchedArm s (compressLeaf W x) = switchedArm s x := by
  cases x <;> rfl

theorem metricPosition_lt_iff_compressed (t : Counts) (W : Finset Leaf)
    (hvalid : ∀ l ∈ W, l ∈ circular t) (s : Switching)
    (x y : Leaf) (hx : x ∈ W) (hy : y ∈ W)
    (hsame : switchedArm s x = switchedArm s y) :
    metricPosition t s x < metricPosition t s y ↔
      metricPosition (compressedCounts W) s (compressLeaf W x) <
        metricPosition (compressedCounts W) s (compressLeaf W y) := by
  cases x with
  | c1 =>
    cases y with
    | c1 => simp
    | c2 =>
      rcases s with ⟨a, b⟩
      cases a <;> cases b <;> simp +decide [switchedArm] at hsame
    | arm k j =>
      have hj := (arm_mem_circular_iff t k j).mp (hvalid _ hy)
      have hr := armRank_lt_count W k hy
      change t.armLength (switchedArm s .c1) + 1 < j + 1 ↔
        (compressedCounts W).armLength (switchedArm s .c1) + 1 < armRank W k j + 1
      change switchedArm s .c1 = k at hsame
      rw [hsame, compressedCounts_armLength]
      omega
  | c2 =>
    cases y with
    | c1 =>
      rcases s with ⟨a, b⟩
      cases a <;> cases b <;> simp +decide [switchedArm] at hsame
    | c2 => simp
    | arm k j =>
      have hj := (arm_mem_circular_iff t k j).mp (hvalid _ hy)
      have hr := armRank_lt_count W k hy
      change t.armLength (switchedArm s .c2) + 1 < j + 1 ↔
        (compressedCounts W).armLength (switchedArm s .c2) + 1 < armRank W k j + 1
      change switchedArm s .c2 = k at hsame
      rw [hsame, compressedCounts_armLength]
      omega
  | arm k i =>
    cases y with
    | c1 =>
      have hi := (arm_mem_circular_iff t k i).mp (hvalid _ hx)
      have hr := armRank_lt_count W k hx
      change i + 1 < t.armLength (switchedArm s .c1) + 1 ↔
        armRank W k i + 1 < (compressedCounts W).armLength (switchedArm s .c1) + 1
      change k = switchedArm s .c1 at hsame
      rw [← hsame, compressedCounts_armLength]
      omega
    | c2 =>
      have hi := (arm_mem_circular_iff t k i).mp (hvalid _ hx)
      have hr := armRank_lt_count W k hx
      change i + 1 < t.armLength (switchedArm s .c2) + 1 ↔
        armRank W k i + 1 < (compressedCounts W).armLength (switchedArm s .c2) + 1
      change k = switchedArm s .c2 at hsame
      rw [← hsame, compressedCounts_armLength]
      omega
    | arm r j =>
      change k = r at hsame
      subst r
      change i + 1 < j + 1 ↔ armRank W k i + 1 < armRank W k j + 1
      simpa using (armRank_lt_iff W k hx hy).symm

#print axioms metricPosition_lt_iff_compressed

end Nanuq.Theta

