import AnchorCompressionOrder

/-! Actual circular successor pairs survive six-witness filtering. -/
namespace Nanuq.Theta

/-- Consecutive in-range list indices form a cyclic adjacent pair. -/
theorem cyclicAdjacent_getD_succ {A : Type*} (l : List A) (fallback : A)
    (i : Nat) (hi : i + 1 < l.length) :
    CyclicAdjacent (l.getD i fallback) (l.getD (i + 1) fallback) l := by
  have hi0 : i < l.length := lt_trans (Nat.lt_succ_self i) hi
  have heq := List.take_append_drop i l
  rw [List.drop_eq_getElem_cons hi0, List.drop_eq_getElem_cons hi] at heq
  apply Or.inl
  refine ⟨l.take i, l.drop (i + 1 + 1), ?_⟩
  simpa only [List.getElem_eq_getD fallback] using heq.symm

/-- Includes the wrap-around successor from the last element to the first. -/
theorem cyclicAdjacent_getD_mod {A : Type*} (l : List A) (fallback : A)
    (hlen : 2 ≤ l.length) (i : Nat) (hi : i < l.length) :
    CyclicAdjacent (l.getD i fallback) (l.getD ((i + 1) % l.length) fallback) l := by
  rcases lt_or_eq_of_le (Nat.succ_le_of_lt hi) with hs | hs
  · rw [Nat.mod_eq_of_lt hs]
    exact cyclicAdjacent_getD_succ l fallback i hs
  · change i + 1 = l.length at hs
    have hi1 : 1 ≤ i := by omega
    have htake : l.take i ++ [l.getD i fallback] = l := by
      simpa only [List.getElem_eq_getD fallback, hs, List.take_length] using
        (List.take_append_getElem hi)
    have hlength : (l.take i).length = i := by
      simp [List.length_take, Nat.min_eq_left (le_of_lt hi)]
    cases hpre : l.take i with
    | nil =>
      simp only [hpre, List.length_nil] at hlength
      omega
    | cons a middle =>
      rw [hpre] at htake
      have hfirst : l.getD 0 fallback = a := by
        rw [← htake]
        simp
      rw [hs, Nat.mod_self, hfirst]
      exact Or.inr ⟨middle, htake.symm⟩

theorem leafIndex_cyclicAdjacent (t : Counts) (i : Fin (circular t).length) :
    CyclicAdjacent (leafIndex t i)
      (leafIndex t (Nanuq.Weighted.cyclicNext i)) (circular t) := by
  have hlen : 2 ≤ (circular t).length := by rw [circular_length]; omega
  exact cyclicAdjacent_getD_mod (circular t) Leaf.c1 hlen i.val i.isLt

/-- The i-boundary is preserved after deleting every non-witness ordinary leaf.
The hybrid leaves are retained even when absent from the six named witnesses. -/
theorem retained_i_boundary_adjacent (t : Counts)
    (p q i j : Fin (circular t).length) :
    CyclicAdjacent (leafIndex t i) (leafIndex t (Nanuq.Weighted.cyclicNext i))
      ((circular t).filter fun l => decide (l ∈ retainedWitnesses t p q i j)) := by
  apply CyclicAdjacent.filter _ (leafIndex_cyclicAdjacent t i)
  · simp [retainedWitnesses, sixWitnesses]
  · simp [retainedWitnesses, sixWitnesses]

theorem retained_j_boundary_adjacent (t : Counts)
    (p q i j : Fin (circular t).length) :
    CyclicAdjacent (leafIndex t j) (leafIndex t (Nanuq.Weighted.cyclicNext j))
      ((circular t).filter fun l => decide (l ∈ retainedWitnesses t p q i j)) := by
  apply CyclicAdjacent.filter _ (leafIndex_cyclicAdjacent t j)
  · simp [retainedWitnesses, sixWitnesses]
  · simp [retainedWitnesses, sixWitnesses]

#print axioms cyclicAdjacent_getD_mod
#print axioms retained_i_boundary_adjacent
#print axioms retained_j_boundary_adjacent

end Nanuq.Theta


