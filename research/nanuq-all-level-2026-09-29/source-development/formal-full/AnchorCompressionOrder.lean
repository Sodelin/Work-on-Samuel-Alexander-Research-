import AnchorCompression

/-! Rank compression maps selected labels injectively to valid compressed leaves. -/
namespace Nanuq.Theta

theorem armRank_eq_iff (W : Finset Leaf) (k : Fin 4) {i j : Nat}
    (hi : Leaf.arm k i ∈ W) (hj : Leaf.arm k j ∈ W) :
    armRank W k i = armRank W k j ↔ i = j := by
  constructor
  · intro hr
    rcases lt_trichotomy i j with hij | hij | hji
    · have hlt := armRank_strictMonoOn_selected W k hi hij
      rw [hr] at hlt
      exact False.elim ((Nat.lt_irrefl _) hlt)
    · exact hij
    · have hlt := armRank_strictMonoOn_selected W k hj hji
      rw [hr] at hlt
      exact False.elim ((Nat.lt_irrefl _) hlt)
  · rintro rfl
    rfl

theorem arm_mem_circular_iff (t : Counts) (k : Fin 4) (j : Nat) :
    Leaf.arm k j ∈ circular t ↔ j < t.armLength k := by
  fin_cases k <;>
    simp +decide [circular, Counts.armLength, Leaf.arm.injEq]

theorem leafIndex_mem_circular (t : Counts) (i : Fin (circular t).length) :
    leafIndex t i ∈ circular t := by
  have hi : leafIndex t i = (circular t)[i.val] :=
    (List.getElem_eq_getD (h := i.isLt) Leaf.c1).symm
  rw [hi]
  exact List.getElem_mem i.isLt

theorem compressLeaf_mem_circular (W : Finset Leaf) {l : Leaf} (hl : l ∈ W) :
    compressLeaf W l ∈ circular (compressedCounts W) := by
  cases l with
  | c1 => simp [compressLeaf, circular]
  | c2 => simp [compressLeaf, circular]
  | arm k j =>
    simp only [compressLeaf, arm_mem_circular_iff, compressedCounts_armLength]
    exact armRank_lt_count W k hl

theorem compressLeaf_injective_on (W : Finset Leaf) {a b : Leaf}
    (ha : a ∈ W) (hb : b ∈ W) (hab : compressLeaf W a = compressLeaf W b) :
    a = b := by
  cases a <;> cases b <;> simp only [compressLeaf, Leaf.arm.injEq] at hab
  all_goals try contradiction
  all_goals try rfl
  case arm.arm k i r j =>
    obtain ⟨hkr, hrank⟩ := hab
    subst r
    exact congrArg (Leaf.arm k) ((armRank_eq_iff W k ha hb).mp hrank)

/-- The actual six named leaves are all valid leaves of the original theta. -/
theorem sixWitnesses_subset_circular (t : Counts)
    (p q i j : Fin (circular t).length) {l : Leaf}
    (hl : l ∈ sixWitnesses t p q i j) : l ∈ circular t := by
  simp only [sixWitnesses, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact leafIndex_mem_circular t _

/-- Both hybrid leaves are retained, and no new ordinary leaf is added. -/
theorem retainedWitnesses_subset_circular (t : Counts)
    (p q i j : Fin (circular t).length) {l : Leaf}
    (hl : l ∈ retainedWitnesses t p q i j) : l ∈ circular t := by
  simp only [retainedWitnesses, Finset.mem_union, Finset.mem_insert,
    Finset.mem_singleton] at hl
  rcases hl with hl | rfl | rfl
  · exact sixWitnesses_subset_circular t p q i j hl
  · simp [circular]
  · simp [circular]

#print axioms armRank_eq_iff
#print axioms compressLeaf_mem_circular
#print axioms compressLeaf_injective_on
#print axioms retainedWitnesses_subset_circular

end Nanuq.Theta


