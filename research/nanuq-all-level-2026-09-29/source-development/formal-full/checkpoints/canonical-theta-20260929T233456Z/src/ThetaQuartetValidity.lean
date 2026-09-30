import ThetaFiniteSoundness

namespace Nanuq.Theta

theorem commonPrefixLength_comm (xs ys : List Vertex) :
    commonPrefixLength xs ys = commonPrefixLength ys xs := by
  induction xs generalizing ys with
  | nil => cases ys <;> rfl
  | cons x xs ih =>
    cases ys with
    | nil => rfl
    | cons y ys =>
      by_cases hxy : x = y
      · subst y
        simp [commonPrefixLength, ih]
      · simp [commonPrefixLength, hxy, Ne.symm hxy]

theorem treeDistance_comm (t : Counts) (s : Switching) (a b : Leaf) :
    treeDistance t s a b = treeDistance t s b a := by
  simp only [treeDistance, commonPrefixLength_comm, Nat.add_comm]

theorem quartet_resolves_iff (t : Counts) (s : Switching) (a b c d : Leaf) :
    (quartet t s a b c d).isSome = true ↔
      (treeDistance t s a b + treeDistance t s c d < treeDistance t s a c + treeDistance t s b d ∧
       treeDistance t s a b + treeDistance t s c d < treeDistance t s a d + treeDistance t s b c) ∨
      (treeDistance t s a c + treeDistance t s b d < treeDistance t s a b + treeDistance t s c d ∧
       treeDistance t s a c + treeDistance t s b d < treeDistance t s a d + treeDistance t s b c) ∨
      (treeDistance t s a d + treeDistance t s b c < treeDistance t s a b + treeDistance t s c d ∧
       treeDistance t s a d + treeDistance t s b c < treeDistance t s a c + treeDistance t s b d) := by
  dsimp only [quartet]
  split_ifs <;> simp_all

theorem resolves_swap_first (t : Counts) (s : Switching) (a b c d : Leaf) :
    (quartet t s b a c d).isSome = true ↔ (quartet t s a b c d).isSome = true := by
  simp only [quartet_resolves_iff, treeDistance_comm, Nat.add_comm]
  omega

theorem resolves_swap_middle (t : Counts) (s : Switching) (a b c d : Leaf) :
    (quartet t s a c b d).isSome = true ↔ (quartet t s a b c d).isSome = true := by
  simp only [quartet_resolves_iff, treeDistance_comm, Nat.add_comm]
  omega

theorem resolves_swap_last (t : Counts) (s : Switching) (a b c d : Leaf) :
    (quartet t s a b d c).isSome = true ↔ (quartet t s a b c d).isSome = true := by
  simp only [quartet_resolves_iff, treeDistance_comm, Nat.add_comm]
  omega

structure FourIndices where
  a : Nat
  b : Nat
  c : Nat
  d : Nat

def cmpFirst (w : FourIndices) : FourIndices :=
  if w.a ≤ w.b then w else ⟨w.b,w.a,w.c,w.d⟩
def cmpMiddle (w : FourIndices) : FourIndices :=
  if w.b ≤ w.c then w else ⟨w.a,w.c,w.b,w.d⟩
def cmpLast (w : FourIndices) : FourIndices :=
  if w.c ≤ w.d then w else ⟨w.a,w.b,w.d,w.c⟩

def sortFour (w : FourIndices) : FourIndices :=
  cmpFirst (cmpMiddle (cmpFirst (cmpLast (cmpMiddle (cmpFirst w)))))

def resolvesAt (t : Counts) (s : Switching) (w : FourIndices) : Prop :=
  (quartet t s (leafAt t w.a) (leafAt t w.b) (leafAt t w.c) (leafAt t w.d)).isSome = true

theorem resolves_cmpFirst (t : Counts) (s : Switching) (w : FourIndices) :
    resolvesAt t s (cmpFirst w) ↔ resolvesAt t s w := by
  unfold cmpFirst
  split_ifs
  · rfl
  · exact resolves_swap_first t s _ _ _ _

theorem resolves_cmpMiddle (t : Counts) (s : Switching) (w : FourIndices) :
    resolvesAt t s (cmpMiddle w) ↔ resolvesAt t s w := by
  unfold cmpMiddle
  split_ifs
  · rfl
  · exact resolves_swap_middle t s _ _ _ _

theorem resolves_cmpLast (t : Counts) (s : Switching) (w : FourIndices) :
    resolvesAt t s (cmpLast w) ↔ resolvesAt t s w := by
  unfold cmpLast
  split_ifs
  · rfl
  · exact resolves_swap_last t s _ _ _ _

theorem resolves_sortFour (t : Counts) (s : Switching) (w : FourIndices) :
    resolvesAt t s (sortFour w) ↔ resolvesAt t s w := by
  simp only [sortFour, resolves_cmpFirst, resolves_cmpMiddle, resolves_cmpLast]

set_option maxHeartbeats 1000000 in
theorem sortFour_spec (a b c d n : Nat)
    (ha : a < n) (hb : b < n) (hc : c < n) (hd : d < n)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    let w := sortFour ⟨a,b,c,d⟩
    w.a < w.b ∧ w.b < w.c ∧ w.c < w.d ∧ w.d < n := by
  dsimp only [sortFour, cmpFirst, cmpMiddle, cmpLast]
  split_ifs <;> dsimp at * <;> omega

theorem resolves_sorted_of_check {t : Counts} (h : checkQuartets t = true)
    (a b c d : Nat) (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hd : d < (circular t).length) (s : Switching) :
    (quartet t s (leafAt t a) (leafAt t b) (leafAt t c) (leafAt t d)).isSome = true := by
  have hp := List.all_eq_true.mp h (a,b) (mem_pairs.mpr ⟨hab,lt_trans hbc (lt_trans hcd hd)⟩)
  have hq := List.all_eq_true.mp hp (c,d) (mem_pairs.mpr ⟨hcd,hd⟩)
  have hall : (switchings.all fun r =>
      (quartet t r (leafAt t a) (leafAt t b) (leafAt t c) (leafAt t d)).isSome) = true := by
    have hparts :
        (switchings.all fun r =>
          (quartet t r (leafAt t a) (leafAt t b) (leafAt t c) (leafAt t d)).isSome) = true ∧
        (1 ≤ (distinctQuartets t (leafAt t a) (leafAt t b) (leafAt t c) (leafAt t d)).length ∧
          (distinctQuartets t (leafAt t a) (leafAt t b) (leafAt t c) (leafAt t d)).length ≤ 2) := by
      simpa [hbc] using hq
    exact hparts.1
  have hs : s ∈ switchings := by
    rcases s with ⟨s1,s2⟩
    cases s1 <;> cases s2 <;> decide
  exact List.all_eq_true.mp hall s hs

theorem resolves_of_check {t : Counts} (h : checkQuartets t = true)
    (a b c d : Nat)
    (ha : a < (circular t).length) (hb : b < (circular t).length)
    (hc : c < (circular t).length) (hd : d < (circular t).length)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) (s : Switching) :
    (quartet t s (leafAt t a) (leafAt t b) (leafAt t c) (leafAt t d)).isSome = true := by
  have hs := sortFour_spec a b c d (circular t).length ha hb hc hd hab hac had hbc hbd hcd
  let w := sortFour ⟨a,b,c,d⟩
  have hr : resolvesAt t s w :=
    resolves_sorted_of_check h w.a w.b w.c w.d hs.1 hs.2.1 hs.2.2.1 hs.2.2.2 s
  exact (resolves_sortFour t s ⟨a,b,c,d⟩).mp hr

#print axioms resolves_of_check
end Nanuq.Theta
