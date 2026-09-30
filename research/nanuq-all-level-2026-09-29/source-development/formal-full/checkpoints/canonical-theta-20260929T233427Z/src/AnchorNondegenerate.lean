import AnchorIndexTransport

/-! A coefficient of a theta with at least three leaves cannot compress to two leaves. -/
namespace Nanuq.Theta

theorem cyclicNext_twice_ne_self {n : Nat} (hn : 3 ≤ n) (i : Fin n) :
    Nanuq.Weighted.cyclicNext (Nanuq.Weighted.cyclicNext i) ≠ i := by
  intro heq
  have hv := congrArg Fin.val heq
  have hi := i.isLt
  change (((i.val + 1) % n) + 1) % n = i.val at hv
  by_cases h1 : i.val + 1 < n
  · rw [Nat.mod_eq_of_lt h1] at hv
    by_cases h2 : i.val + 1 + 1 < n
    · rw [Nat.mod_eq_of_lt h2] at hv
      omega
    · have h2' : i.val + 1 + 1 = n := by omega
      rw [h2', Nat.mod_self] at hv
      omega
  · have h1' : i.val + 1 = n := by omega
    rw [h1', Nat.mod_self] at hv
    have hn1 : 1 < n := by omega
    simp only [Nat.zero_add, Nat.mod_eq_of_lt hn1] at hv
    omega

theorem compressedIndex_injective (t : Counts) (W : Finset Leaf)
    (hvalid : ∀ l ∈ W, l ∈ circular t) (hc1 : Leaf.c1 ∈ W) (hc2 : Leaf.c2 ∈ W)
    (i j : Fin (circular t).length) (hi : leafIndex t i ∈ W) (hj : leafIndex t j ∈ W)
    (heq : compressedIndex t W hvalid hc1 hc2 i hi =
      compressedIndex t W hvalid hc1 hc2 j hj) : i = j := by
  rcases lt_trichotomy i j with hij | hij | hji
  · have hlt := compressedIndex_strictMono t W hvalid hc1 hc2 i j hi hj hij
    rw [heq] at hlt
    exact False.elim ((lt_irrefl _) hlt)
  · exact hij
  · have hlt := compressedIndex_strictMono t W hvalid hc1 hc2 j i hj hi hji
    rw [heq] at hlt
    exact False.elim ((lt_irrefl _) hlt)

theorem compressed_retained_total_pos (t : Counts)
    (hlen : 3 ≤ (circular t).length)
    (p q i j : Fin (circular t).length) (hij : i < j) :
    1 ≤ (compressedCounts (retainedWitnesses t p q i j)).total := by
  let W := retainedWitnesses t p q i j
  have hvalid : ∀ l ∈ W, l ∈ circular t :=
    fun _ hl => retainedWitnesses_subset_circular t p q i j hl
  have hc1 : Leaf.c1 ∈ W := by simp [W, retainedWitnesses]
  have hc2 : Leaf.c2 ∈ W := by simp [W, retainedWitnesses]
  have hi : leafIndex t i ∈ W := by simp [W, retainedWitnesses, sixWitnesses]
  have hj : leafIndex t j ∈ W := by simp [W, retainedWitnesses, sixWitnesses]
  have hin : leafIndex t (Nanuq.Weighted.cyclicNext i) ∈ W := by
    simp [W, retainedWitnesses, sixWitnesses]
  have hjn : leafIndex t (Nanuq.Weighted.cyclicNext j) ∈ W := by
    simp [W, retainedWitnesses, sixWitnesses]
  by_contra hpos
  change ¬ 1 ≤ (compressedCounts W).total at hpos
  have hzero : (compressedCounts W).total = 0 := by omega
  have htwo : (circular (compressedCounts W)).length = 2 := by
    rw [circular_length, hzero]
  have hij' := compressedIndex_strictMono t W hvalid hc1 hc2 i j hi hj hij
  have hib := (compressedIndex t W hvalid hc1 hc2 i hi).isLt
  have hjb := (compressedIndex t W hvalid hc1 hc2 j hj).isLt
  have hiv : (compressedIndex t W hvalid hc1 hc2 i hi).val = 0 := by
    change (compressedIndex t W hvalid hc1 hc2 i hi).val <
      (compressedIndex t W hvalid hc1 hc2 j hj).val at hij'
    omega
  have hjv : (compressedIndex t W hvalid hc1 hc2 j hj).val = 1 := by
    change (compressedIndex t W hvalid hc1 hc2 i hi).val <
      (compressedIndex t W hvalid hc1 hc2 j hj).val at hij'
    omega
  have hni : Nanuq.Weighted.cyclicNext i = j := by
    apply compressedIndex_injective t W hvalid hc1 hc2 _ _ hin hj
    rw [compressedIndex_cyclicNext]
    apply Fin.ext
    change ((compressedIndex t W hvalid hc1 hc2 i hi).val + 1) %
      (circular (compressedCounts W)).length =
        (compressedIndex t W hvalid hc1 hc2 j hj).val
    rw [hiv, hjv, htwo]
  have hnj : Nanuq.Weighted.cyclicNext j = i := by
    apply compressedIndex_injective t W hvalid hc1 hc2 _ _ hjn hi
    rw [compressedIndex_cyclicNext]
    apply Fin.ext
    change ((compressedIndex t W hvalid hc1 hc2 j hj).val + 1) %
      (circular (compressedCounts W)).length =
        (compressedIndex t W hvalid hc1 hc2 i hi).val
    rw [hiv, hjv, htwo]
  exact cyclicNext_twice_ne_self hlen i (by rw [hni, hnj])

#print axioms compressed_retained_total_pos

end Nanuq.Theta


