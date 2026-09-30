import AnchorCanonicalOrder


/-! Ordered and cyclic index transport to the actual compressed canonical cycle. -/
namespace Nanuq.Theta


private theorem getD_after_prefix {A : Type*} (pre post : List A) (a fallback : A) :
    (pre ++ a :: post).getD pre.length fallback = a := by
  induction pre with
  | nil => simp
  | cons x xs ih => simpa using ih

private theorem getD_map_compatible {A B : Type*} (l : List A) (f : A → B)
    (fallback : A) (i : Nat) :
    (l.map f).getD i (f fallback) = f (l.getD i fallback) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, Option.getD_map]


def retainedPrefixLength {A : Type*} (l : List A) (keep : A → Bool) (i : Nat) : Nat :=
  ((l.take i).filter keep).length

theorem retainedPrefixLength_succ {A : Type*} (l : List A) (keep : A → Bool)
    (fallback : A) (i : Nat) (hi : i < l.length) (hkeep : keep (l.getD i fallback) = true) :
    retainedPrefixLength l keep (i + 1) = retainedPrefixLength l keep i + 1 := by
  unfold retainedPrefixLength
  rw [List.take_succ_eq_append_getElem hi]
  simp only [List.getElem_eq_getD fallback, List.filter_append, List.filter_cons,
    hkeep, List.filter_nil, Bool.true_eq, ↓reduceIte, List.length_append,
    List.length_cons, List.length_nil]

theorem retainedPrefixLength_strictMono {A : Type*} (l : List A) (keep : A → Bool)
    (fallback : A) (i j : Nat) (hi : i < l.length) (hij : i < j)
    (hkeep : keep (l.getD i fallback) = true) :
    retainedPrefixLength l keep i < retainedPrefixLength l keep j := by
  have hp : l.take (i + 1) <+: l.take j := by
    simpa only [List.take_take, Nat.min_eq_left (Nat.succ_le_of_lt hij)] using
      (List.take_prefix (i + 1) (l.take j))
  have hle := (hp.filter keep).length_le
  change retainedPrefixLength l keep (i + 1) ≤ retainedPrefixLength l keep j at hle
  rw [retainedPrefixLength_succ l keep fallback i hi hkeep] at hle
  omega

theorem retainedPrefixLength_lt {A : Type*} (l : List A) (keep : A → Bool)
    (fallback : A) (i : Nat) (hi : i < l.length) (hkeep : keep (l.getD i fallback) = true) :
    retainedPrefixLength l keep i < (l.filter keep).length := by
  have hlt := retainedPrefixLength_strictMono l keep fallback i l.length hi hi hkeep
  simpa [retainedPrefixLength] using hlt

theorem getD_filter_retainedPrefixLength {A : Type*} (l : List A) (keep : A → Bool)
    (fallback : A) (i : Nat) (hi : i < l.length) (hkeep : keep (l.getD i fallback) = true) :
    (l.filter keep).getD (retainedPrefixLength l keep i) fallback = l.getD i fallback := by
  have hd : l = l.take i ++ l.getD i fallback :: l.drop (i + 1) := by
    have he := List.take_append_drop i l
    rw [List.drop_eq_getElem_cons hi] at he
    simpa only [List.getElem_eq_getD fallback] using he.symm
  have hf := congrArg (List.filter keep) hd
  simp only [List.filter_append, List.filter_cons, hkeep, Bool.true_eq, ↓reduceIte] at hf
  rw [hf]
  unfold retainedPrefixLength
  exact getD_after_prefix _ _ _ _

def compressedIndex (t : Counts) (W : Finset Leaf)
    (hvalid : ∀ l ∈ W, l ∈ circular t) (hc1 : Leaf.c1 ∈ W) (hc2 : Leaf.c2 ∈ W)
    (i : Fin (circular t).length) (hi : leafIndex t i ∈ W) :
    Fin (circular (compressedCounts W)).length :=
  ⟨retainedPrefixLength (circular t) (fun l => decide (l ∈ W)) i.val, by
    have hlt := retainedPrefixLength_lt (circular t) (fun l => decide (l ∈ W))
      Leaf.c1 i.val i.isLt (by simpa [leafIndex, leafAt] using hi)
    have he := congrArg List.length (compressed_circular_eq t W hvalid hc1 hc2)
    simp only [List.length_map] at he
    exact he ▸ hlt⟩

theorem leafIndex_compressedIndex (t : Counts) (W : Finset Leaf)
    (hvalid : ∀ l ∈ W, l ∈ circular t) (hc1 : Leaf.c1 ∈ W) (hc2 : Leaf.c2 ∈ W)
    (i : Fin (circular t).length) (hi : leafIndex t i ∈ W) :
    leafIndex (compressedCounts W) (compressedIndex t W hvalid hc1 hc2 i hi) =
      compressLeaf W (leafIndex t i) := by
  unfold leafIndex leafAt compressedIndex
  simp only
  rw [← compressed_circular_eq t W hvalid hc1 hc2]
  change (((circular t).filter (fun l => decide (l ∈ W))).map (compressLeaf W)).getD
      (retainedPrefixLength (circular t) (fun l => decide (l ∈ W)) i.val)
      (compressLeaf W Leaf.c1) = _
  rw [getD_map_compatible]
  rw [getD_filter_retainedPrefixLength (circular t) (fun l => decide (l ∈ W))
    Leaf.c1 i.val i.isLt (by simpa [leafIndex, leafAt] using hi)]

theorem compressedIndex_strictMono (t : Counts) (W : Finset Leaf)
    (hvalid : ∀ l ∈ W, l ∈ circular t) (hc1 : Leaf.c1 ∈ W) (hc2 : Leaf.c2 ∈ W)
    (i j : Fin (circular t).length) (hi : leafIndex t i ∈ W) (hj : leafIndex t j ∈ W)
    (hij : i < j) :
    compressedIndex t W hvalid hc1 hc2 i hi < compressedIndex t W hvalid hc1 hc2 j hj :=
  retainedPrefixLength_strictMono (circular t) (fun l => decide (l ∈ W))
    Leaf.c1 i.val j.val i.isLt hij (by simpa [leafIndex, leafAt] using hi)

#print axioms leafIndex_compressedIndex
#print axioms compressedIndex_strictMono


/-- If an original successor is retained, it is also the successor of the
compressed index, including the last-to-first boundary. -/
theorem compressedIndex_cyclicNext (t : Counts) (W : Finset Leaf)
    (hvalid : ∀ l ∈ W, l ∈ circular t) (hc1 : Leaf.c1 ∈ W) (hc2 : Leaf.c2 ∈ W)
    (i : Fin (circular t).length) (hi : leafIndex t i ∈ W)
    (hn : leafIndex t (Nanuq.Weighted.cyclicNext i) ∈ W) :
    compressedIndex t W hvalid hc1 hc2 (Nanuq.Weighted.cyclicNext i) hn =
      Nanuq.Weighted.cyclicNext (compressedIndex t W hvalid hc1 hc2 i hi) := by
  have hkeep : (decide (leafAt t i.val ∈ W)) = true := by
    simpa [leafIndex] using hi
  have hs := retainedPrefixLength_succ (circular t) (fun l => decide (l ∈ W))
    Leaf.c1 i.val i.isLt hkeep
  have hlength := congrArg List.length (compressed_circular_eq t W hvalid hc1 hc2)
  simp only [List.length_map] at hlength
  apply Fin.ext
  change retainedPrefixLength (circular t) (fun l => decide (l ∈ W))
      ((i.val + 1) % (circular t).length) =
    (retainedPrefixLength (circular t) (fun l => decide (l ∈ W)) i.val + 1) %
      (circular (compressedCounts W)).length
  by_cases hb : i.val + 1 < (circular t).length
  · have hbound := (compressedIndex t W hvalid hc1 hc2
      (Nanuq.Weighted.cyclicNext i) hn).isLt
    change retainedPrefixLength (circular t) (fun l => decide (l ∈ W))
      ((i.val + 1) % (circular t).length) <
        (circular (compressedCounts W)).length at hbound
    rw [Nat.mod_eq_of_lt hb, hs] at hbound
    rw [Nat.mod_eq_of_lt hb, hs, Nat.mod_eq_of_lt hbound]
  · have hlast : i.val + 1 = (circular t).length := by omega
    rw [hlast] at hs
    simp only [retainedPrefixLength, List.take_length] at hs
    have hlast' :
        retainedPrefixLength (circular t) (fun l => decide (l ∈ W)) i.val + 1 =
          (circular (compressedCounts W)).length := hs.symm.trans hlength
    rw [hlast, Nat.mod_self, hlast', Nat.mod_self]
    rfl

/-- Four anchor-entry equalities suffice for one circular coefficient. -/
theorem alpha_preserved_of_anchor_entries (t u : Counts)
    (p q i j p' q' i' j' : Nat)
    (h00 : anchor t (leafAt t p) (leafAt t q) (leafAt t i) (leafAt t j) =
      anchor u (leafAt u p') (leafAt u q') (leafAt u i') (leafAt u j'))
    (h11 : anchor t (leafAt t p) (leafAt t q) (leafAt t (next t i)) (leafAt t (next t j)) =
      anchor u (leafAt u p') (leafAt u q') (leafAt u (next u i')) (leafAt u (next u j')))
    (h01 : anchor t (leafAt t p) (leafAt t q) (leafAt t i) (leafAt t (next t j)) =
      anchor u (leafAt u p') (leafAt u q') (leafAt u i') (leafAt u (next u j')))
    (h10 : anchor t (leafAt t p) (leafAt t q) (leafAt t (next t i)) (leafAt t j) =
      anchor u (leafAt u p') (leafAt u q') (leafAt u (next u i')) (leafAt u j')) :
    alpha t p q i j = alpha u p' q' i' j' := by
  unfold alpha
  rw [h00, h11, h01, h10]

/-- Exact alpha transport. The only substantive assumption still required here
is preservation of the leaf-level anchor entries on the retained labels. -/
theorem alpha_preserved_under_compression (t : Counts) (W : Finset Leaf)
    (hvalid : ∀ l ∈ W, l ∈ circular t) (hc1 : Leaf.c1 ∈ W) (hc2 : Leaf.c2 ∈ W)
    (p q i j : Fin (circular t).length)
    (hp : leafIndex t p ∈ W) (hq : leafIndex t q ∈ W)
    (hi : leafIndex t i ∈ W) (hj : leafIndex t j ∈ W)
    (hin : leafIndex t (Nanuq.Weighted.cyclicNext i) ∈ W)
    (hjn : leafIndex t (Nanuq.Weighted.cyclicNext j) ∈ W)
    (hanchor : ∀ a ∈ W, ∀ b ∈ W,
      anchor t (leafIndex t p) (leafIndex t q) a b =
        anchor (compressedCounts W) (compressLeaf W (leafIndex t p))
          (compressLeaf W (leafIndex t q)) (compressLeaf W a) (compressLeaf W b)) :
    alpha t p.val q.val i.val j.val =
      alpha (compressedCounts W)
        (compressedIndex t W hvalid hc1 hc2 p hp).val
        (compressedIndex t W hvalid hc1 hc2 q hq).val
        (compressedIndex t W hvalid hc1 hc2 i hi).val
        (compressedIndex t W hvalid hc1 hc2 j hj).val := by
  have hmap (a : Fin (circular t).length) (ha : leafIndex t a ∈ W) :
      leafAt (compressedCounts W) (compressedIndex t W hvalid hc1 hc2 a ha).val =
        compressLeaf W (leafIndex t a) :=
    leafIndex_compressedIndex t W hvalid hc1 hc2 a ha
  have hni :
      leafAt (compressedCounts W)
        (next (compressedCounts W) (compressedIndex t W hvalid hc1 hc2 i hi).val) =
        compressLeaf W (leafIndex t (Nanuq.Weighted.cyclicNext i)) := by
    change leafIndex (compressedCounts W)
      (Nanuq.Weighted.cyclicNext (compressedIndex t W hvalid hc1 hc2 i hi)) = _
    rw [← compressedIndex_cyclicNext t W hvalid hc1 hc2 i hi hin]
    exact leafIndex_compressedIndex t W hvalid hc1 hc2 _ hin
  have hnj :
      leafAt (compressedCounts W)
        (next (compressedCounts W) (compressedIndex t W hvalid hc1 hc2 j hj).val) =
        compressLeaf W (leafIndex t (Nanuq.Weighted.cyclicNext j)) := by
    change leafIndex (compressedCounts W)
      (Nanuq.Weighted.cyclicNext (compressedIndex t W hvalid hc1 hc2 j hj)) = _
    rw [← compressedIndex_cyclicNext t W hvalid hc1 hc2 j hj hjn]
    exact leafIndex_compressedIndex t W hvalid hc1 hc2 _ hjn
  unfold alpha
  rw [hmap p hp, hmap q hq, hmap i hi, hmap j hj, hni, hnj]
  change
    anchor t (leafIndex t p) (leafIndex t q) (leafIndex t i) (leafIndex t j) +
      anchor t (leafIndex t p) (leafIndex t q)
        (leafIndex t (Nanuq.Weighted.cyclicNext i)) (leafIndex t (Nanuq.Weighted.cyclicNext j)) -
      anchor t (leafIndex t p) (leafIndex t q) (leafIndex t i)
        (leafIndex t (Nanuq.Weighted.cyclicNext j)) -
      anchor t (leafIndex t p) (leafIndex t q)
        (leafIndex t (Nanuq.Weighted.cyclicNext i)) (leafIndex t j) = _
  rw [hanchor _ hi _ hj, hanchor _ hin _ hjn, hanchor _ hi _ hjn, hanchor _ hin _ hj]

#print axioms compressedIndex_cyclicNext
#print axioms alpha_preserved_under_compression

end Nanuq.Theta



