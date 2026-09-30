import CircularThetaCuts
import IntervalBoundary
import ThetaDisplayedSemantics
import ThetaEdgeQuartet

/-! Exact boundary characterization of the actual switched-tree edge support. -/
namespace Nanuq.Theta
open Nanuq.Weighted Nanuq.Reconstruction

variable {n : Nat}

theorem cyclicNext_ne_self_of_two_le (hn : 2 ≤ n) (i : Fin n) : cyclicNext i ≠ i := by
  intro h
  have hv := congrArg Fin.val h
  change (i.val + 1) % n = i.val at hv
  by_cases hs : i.val + 1 < n
  · rw [Nat.mod_eq_of_lt hs] at hv
    omega
  · have he : i.val + 1 = n := by omega
    rw [he, Nat.mod_self] at hv
    omega

theorem inArc_next_left (i j : Fin n) (hij : i < j) : inArc i j (cyclicNext i) := by
  have hs : i.val + 1 < n := by have hj := j.isLt; omega
  simp only [inArc, Fin.lt_def, Fin.le_def, cyclicNext, Nat.mod_eq_of_lt hs]
  omega

theorem not_inArc_next_right (i j : Fin n) (hij : i < j) : ¬ inArc i j (cyclicNext j) := by
  by_cases hs : j.val + 1 < n
  · simp only [inArc, Fin.lt_def, Fin.le_def, cyclicNext, Nat.mod_eq_of_lt hs]
    omega
  · have he : j.val + 1 = n := by have hj := j.isLt; omega
    simp only [inArc, Fin.lt_def, Fin.le_def, cyclicNext, he, Nat.mod_self]
    omega

theorem pathRealizesGap_iff_boundary_partition (t : Counts) (s : Switching) (z : Vertex)
    (i j : Fin (circular t).length) (hij : i < j) :
    pathRealizesGap t s z i j ↔
      cutSeparatesPairs t s z (leafIndex t i) (leafIndex t (cyclicNext j))
        (leafIndex t (cyclicNext i)) (leafIndex t j) := by
  have hai : ¬ inArc i j i := by simp [inArc]
  have haj : inArc i j j := ⟨hij,le_rfl⟩
  have hni := inArc_next_left i j hij
  have hnj := not_inArc_next_right i j hij
  constructor
  · intro h
    rcases h with h | h
    · exact Or.inr ⟨fun hp => hai ((h i).mp hp),
        fun hp => hnj ((h _).mp hp), (h _).mpr hni, (h j).mpr haj⟩
    · exact Or.inl ⟨(h i).mpr hai, (h _).mpr hnj,
        fun hp => (h _).mp hp hni, fun hp => (h j).mp hp haj⟩
  · intro hsep
    have hi : ¬ (z ∈ terminalPath t s (leafIndex t i) ↔
        z ∈ terminalPath t s (leafIndex t (cyclicNext i))) := by
      intro h
      rcases hsep with ⟨ha,_,hb,_⟩ | ⟨ha,_,hb,_⟩
      · exact hb (h.mp ha)
      · exact ha (h.mpr hb)
    have hj : ¬ (z ∈ terminalPath t s (leafIndex t j) ↔
        z ∈ terminalPath t s (leafIndex t (cyclicNext j))) := by
      intro h
      rcases hsep with ⟨_,hd,_,hc⟩ | ⟨_,hd,_,hc⟩
      · exact hc (h.mpr hd)
      · exact hd (h.mp hc)
    obtain ⟨a,b,_hab,hb,hform⟩ := terminalPath_cut_interval t s z
    exact interval_predicate_two_crossings _ a b hb hform i j hij hi hj

theorem displayedSplit_iff_boundary_edge (t : Counts)
    (i j : Fin (circular t).length) (hij : i < j) :
    displayedSplit t i.val j.val = true ↔
      ∃ s y z, (y,z) ∈ switchingEdges t s ∧
        cutSeparatesPairs t s z (leafIndex t i) (leafIndex t (cyclicNext j))
          (leafIndex t (cyclicNext i)) (leafIndex t j) := by
  rw [displayedSplit_iff]
  simp only [pathRealizesGap_iff_boundary_partition t _ _ i j hij]

theorem displayedSplit_of_successor (t : Counts)
    (i j : Fin (circular t).length) (hij : i < j)
    (hs : cyclicNext i = j ∨ cyclicNext j = i) :
    displayedSplit t i.val j.val = true := by
  have hn : 2 ≤ (circular t).length := by rw [circular_length]; omega
  let s : Switching := (false,false)
  rcases hs with hs | hs
  · let x := leafIndex t j
    obtain ⟨y,he⟩ := exists_switching_edge_of_path t s x (leafIndex_mem_circular t j)
      (Vertex.terminal x) (by simp) (by intro h; cases h)
    apply (displayedSplit_iff_boundary_edge t i j hij).mpr
    refine ⟨s,y,Vertex.terminal x,he,Or.inr ?_⟩
    have hne : leafIndex t j ≠ leafIndex t i :=
      fun h => (ne_of_gt hij) (leafIndex_injective t h)
    have hnext : leafIndex t j ≠ leafIndex t (cyclicNext j) :=
      fun h => cyclicNext_ne_self_of_two_le hn j ((leafIndex_injective t h).symm)
    simpa only [terminal_mem_terminalPath, hs, x, not_false_eq_true, and_self] using
      (show (leafIndex t j ≠ leafIndex t i) ∧
        (leafIndex t j ≠ leafIndex t (cyclicNext j)) ∧ True ∧ True from ⟨hne,hnext,trivial,trivial⟩)
  · let x := leafIndex t i
    obtain ⟨y,he⟩ := exists_switching_edge_of_path t s x (leafIndex_mem_circular t i)
      (Vertex.terminal x) (by simp) (by intro h; cases h)
    apply (displayedSplit_iff_boundary_edge t i j hij).mpr
    refine ⟨s,y,Vertex.terminal x,he,Or.inl ?_⟩
    have hne : leafIndex t i ≠ leafIndex t j :=
      fun h => (ne_of_lt hij) (leafIndex_injective t h)
    have hnext : leafIndex t i ≠ leafIndex t (cyclicNext i) :=
      fun h => cyclicNext_ne_self_of_two_le hn i ((leafIndex_injective t h).symm)
    simp only [terminal_mem_terminalPath, hs, x]
    exact ⟨trivial,trivial,hnext,hne⟩

/-- For nonadjacent boundaries the full split is equivalent to the single
boundary quartet resolution in at least one actual switching. -/
theorem displayedSplit_iff_boundary_quartet (t : Counts)
    (i j : Fin (circular t).length) (hij : i < j)
    (hni : cyclicNext i ≠ j) (hnj : cyclicNext j ≠ i) :
    displayedSplit t i.val j.val = true ↔
      ∃ s, quartet t s (leafIndex t i) (leafIndex t (cyclicNext j))
        (leafIndex t (cyclicNext i)) (leafIndex t j) = some Pairing.ab_cd := by
  have hn : 2 ≤ (circular t).length := by rw [circular_length]; omega
  have hab : leafIndex t i ≠ leafIndex t (cyclicNext j) :=
    fun h => hnj ((leafIndex_injective t h).symm)
  have hac : leafIndex t i ≠ leafIndex t (cyclicNext i) :=
    fun h => cyclicNext_ne_self_of_two_le hn i ((leafIndex_injective t h).symm)
  have had : leafIndex t i ≠ leafIndex t j :=
    fun h => (ne_of_lt hij) (leafIndex_injective t h)
  have hbc : leafIndex t (cyclicNext j) ≠ leafIndex t (cyclicNext i) :=
    fun h => (ne_of_gt hij) (cyclicNext_injective (leafIndex_injective t h))
  have hbd : leafIndex t (cyclicNext j) ≠ leafIndex t j :=
    fun h => cyclicNext_ne_self_of_two_le hn j (leafIndex_injective t h)
  have hcd : leafIndex t (cyclicNext i) ≠ leafIndex t j :=
    fun h => hni (leafIndex_injective t h)
  rw [displayedSplit_iff_boundary_edge t i j hij]
  constructor
  · rintro ⟨s,y,z,he,hsep⟩
    exact ⟨s,(quartet_iff_separating_edge t s _ _ _ _
      (leafIndex_mem_circular t _) (leafIndex_mem_circular t _)
      (leafIndex_mem_circular t _) (leafIndex_mem_circular t _)
      hab hac had hbc hbd hcd).mpr ⟨y,z,he,hsep⟩⟩
  · rintro ⟨s,hq⟩
    obtain ⟨y,z,he,hsep⟩ := (quartet_iff_separating_edge t s _ _ _ _
      (leafIndex_mem_circular t _) (leafIndex_mem_circular t _)
      (leafIndex_mem_circular t _) (leafIndex_mem_circular t _)
      hab hac had hbc hbd hcd).mp hq
    exact ⟨s,y,z,he,hsep⟩

#print axioms pathRealizesGap_iff_boundary_partition
#print axioms displayedSplit_of_successor
#print axioms displayedSplit_iff_boundary_quartet
end Nanuq.Theta

