import AnchorThetaBridge
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.FinCases

/-!
The combinatorial selection and order-preservation part of six-witness
compression. These theorems do not by themselves prove quartet invariance.
-/
namespace Nanuq.Theta

def armTag : Leaf → Option (Fin 4)
  | .c1 => none
  | .c2 => none
  | .arm k _ => some k

def armSet (W : Finset Leaf) (k : Fin 4) : Finset Leaf :=
  W.filter (fun l => armTag l = some k)

def armCount (W : Finset Leaf) (k : Fin 4) : Nat := (armSet W k).card

def compressedCounts (W : Finset Leaf) : Counts :=
  ⟨armCount W 0, armCount W 1, armCount W 2, armCount W 3⟩

def armPosition : Leaf → Nat
  | .c1 => 0
  | .c2 => 0
  | .arm _ j => j

def prefixSet (W : Finset Leaf) (k : Fin 4) (j : Nat) : Finset Leaf :=
  W.filter (fun l => armTag l = some k ∧ armPosition l < j)

def armRank (W : Finset Leaf) (k : Fin 4) (j : Nat) : Nat :=
  (prefixSet W k j).card

def compressLeaf (W : Finset Leaf) : Leaf → Leaf
  | .c1 => .c1
  | .c2 => .c2
  | .arm k j => .arm k (armRank W k j)

@[simp] theorem mem_prefixSet (W : Finset Leaf) (k : Fin 4) (j r : Nat) :
    Leaf.arm k r ∈ prefixSet W k j ↔ Leaf.arm k r ∈ W ∧ r < j := by
  unfold prefixSet
  rw [Finset.mem_filter]
  simp only [armTag, armPosition, and_self, true_and]

theorem prefixSet_mono (W : Finset Leaf) (k : Fin 4) {i j : Nat} (hij : i ≤ j) :
    prefixSet W k i ⊆ prefixSet W k j := by
  intro l hl
  obtain ⟨hw, ht, hr⟩ := Finset.mem_filter.mp hl
  exact Finset.mem_filter.mpr ⟨hw, ht, lt_of_lt_of_le hr hij⟩

theorem prefixSet_subset_armSet (W : Finset Leaf) (k : Fin 4) (j : Nat) :
    prefixSet W k j ⊆ armSet W k := by
  intro l hl
  obtain ⟨hw, ht, _⟩ := Finset.mem_filter.mp hl
  exact Finset.mem_filter.mpr ⟨hw, ht⟩

theorem armRank_strictMonoOn_selected (W : Finset Leaf) (k : Fin 4)
    {i j : Nat} (hi : Leaf.arm k i ∈ W) (hij : i < j) :
    armRank W k i < armRank W k j := by
  unfold armRank
  apply Finset.card_lt_card
  apply (Finset.ssubset_iff_subset_ne).mpr
  refine ⟨prefixSet_mono W k (le_of_lt hij), ?_⟩
  intro heq
  have hj : Leaf.arm k i ∈ prefixSet W k j := (mem_prefixSet W k j i).mpr ⟨hi, hij⟩
  rw [← heq] at hj
  exact (Nat.lt_irrefl i) ((mem_prefixSet W k i i).mp hj).2

theorem armRank_lt_count (W : Finset Leaf) (k : Fin 4) {j : Nat}
    (hj : Leaf.arm k j ∈ W) :
    armRank W k j < armCount W k := by
  unfold armRank armCount
  apply Finset.card_lt_card
  apply (Finset.ssubset_iff_subset_ne).mpr
  refine ⟨prefixSet_subset_armSet W k j, ?_⟩
  intro heq
  have hmem : Leaf.arm k j ∈ armSet W k := Finset.mem_filter.mpr ⟨hj, rfl⟩
  rw [← heq] at hmem
  exact (Nat.lt_irrefl j) ((mem_prefixSet W k j j).mp hmem).2

theorem armRank_lt_iff (W : Finset Leaf) (k : Fin 4) {i j : Nat}
    (hi : Leaf.arm k i ∈ W) (hj : Leaf.arm k j ∈ W) :
    armRank W k i < armRank W k j ↔ i < j := by
  constructor
  · intro hr
    by_contra! hji
    rcases lt_or_eq_of_le hji with hji | rfl
    · exact (not_lt_of_gt (armRank_strictMonoOn_selected W k hj hji)) hr
    · exact (Nat.lt_irrefl _) hr
  · exact armRank_strictMonoOn_selected W k hi

theorem compressedCounts_armLength (W : Finset Leaf) (k : Fin 4) :
    (compressedCounts W).armLength k = armCount W k := by
  fin_cases k <;> simp +decide [Counts.armLength, compressedCounts]

theorem compressedCounts_total_le (W : Finset Leaf) :
    (compressedCounts W).total ≤ W.card := by
  have hcount (k : Fin 4) :
      armCount W k = ∑ l ∈ W, if armTag l = some k then 1 else 0 := by
    simp only [armCount, armSet, Finset.card_eq_sum_ones, Finset.sum_filter]
  have hone (l : Leaf) :
      (∑ k : Fin 4, if armTag l = some k then (1 : Nat) else 0) ≤ 1 := by
    cases l with
    | c1 => simp [armTag]
    | c2 => simp [armTag]
    | arm k j => simp [armTag, eq_comm]
  calc
    (compressedCounts W).total = ∑ k : Fin 4, armCount W k := by
      simp +decide [compressedCounts, Counts.total, Fin.sum_univ_succ]
      omega
    _ = ∑ k : Fin 4, ∑ l ∈ W, if armTag l = some k then 1 else 0 := by
      simp_rw [hcount]
    _ = ∑ l ∈ W, ∑ k : Fin 4, if armTag l = some k then 1 else 0 := by
      rw [Finset.sum_comm]
    _ ≤ ∑ _l ∈ W, 1 := Finset.sum_le_sum (fun l _ => hone l)
    _ = W.card := by simp

/-- The six actual labels occurring in one anchor coefficient. -/
def sixWitnesses (t : Counts) (p q i j : Fin (circular t).length) : Finset Leaf :=
  [leafIndex t p, leafIndex t q, leafIndex t i,
    leafIndex t (Nanuq.Weighted.cyclicNext i), leafIndex t j,
    leafIndex t (Nanuq.Weighted.cyclicNext j)].toFinset

def retainedWitnesses (t : Counts) (p q i j : Fin (circular t).length) : Finset Leaf :=
  sixWitnesses t p q i j ∪ {Leaf.c1, Leaf.c2}

theorem sixWitnesses_card_le (t : Counts) (p q i j : Fin (circular t).length) :
    (sixWitnesses t p q i j).card ≤ 6 := by
  exact List.toFinset_card_le _

theorem compressed_sixWitnesses_total_le (t : Counts)
    (p q i j : Fin (circular t).length) :
    (compressedCounts (sixWitnesses t p q i j)).total ≤ 6 :=
  (compressedCounts_total_le _).trans (sixWitnesses_card_le t p q i j)

/-- Adding the hybrid leaves does not affect any ordinary-arm count. -/
theorem armSet_add_hybrids (W : Finset Leaf) (k : Fin 4) :
    armSet (W ∪ {Leaf.c1, Leaf.c2}) k = armSet W k := by
  ext l
  simp only [armSet, Finset.mem_filter, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  cases l <;> simp [armTag]

theorem compressedCounts_add_hybrids (W : Finset Leaf) :
    compressedCounts (W ∪ {Leaf.c1, Leaf.c2}) = compressedCounts W := by
  simp only [compressedCounts, armCount, armSet_add_hybrids]

/-- An explicit cyclic adjacency relation, including the wrap-around gap. -/
def CyclicAdjacent {A : Type*} (a b : A) (l : List A) : Prop :=
  (∃ pre post, l = pre ++ a :: b :: post) ∨
    (∃ middle, l = b :: middle ++ [a])

/-- Deleting other elements preserves adjacency of a retained boundary pair. -/
theorem CyclicAdjacent.filter {A : Type*} (keep : A → Bool)
    {a b : A} {l : List A} (hab : CyclicAdjacent a b l)
    (ha : keep a = true) (hb : keep b = true) :
    CyclicAdjacent a b (l.filter keep) := by
  rcases hab with ⟨pre, post, rfl⟩ | ⟨middle, rfl⟩
  · exact Or.inl ⟨pre.filter keep, post.filter keep, by simp [ha, hb]⟩
  · exact Or.inr ⟨middle.filter keep, by simp [ha, hb]⟩

#print axioms armRank_lt_iff
#print axioms armRank_lt_count
#print axioms compressed_sixWitnesses_total_le
#print axioms CyclicAdjacent.filter

end Nanuq.Theta




