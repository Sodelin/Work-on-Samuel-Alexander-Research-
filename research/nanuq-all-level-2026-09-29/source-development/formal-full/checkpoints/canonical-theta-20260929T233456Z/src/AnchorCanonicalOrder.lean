import AnchorCompressionOrder
import Mathlib.Data.List.Sort

/-! Rank compression identifies retained arm order with consecutive canonical ranks. -/
namespace Nanuq.Theta

theorem armSet_member_form (W : Finset Leaf) (k : Fin 4) {l : Leaf}
    (hl : l ∈ armSet W k) :
    l = Leaf.arm k (armPosition l) := by
  obtain ⟨_, ht⟩ := Finset.mem_filter.mp hl
  cases l with
  | c1 => simp [armTag] at ht
  | c2 => simp [armTag] at ht
  | arm r j =>
    have hr : r = k := Option.some.inj ht
    subst r
    rfl

def armRanks (W : Finset Leaf) (k : Fin 4) : Finset Nat :=
  (armSet W k).image (fun l => armRank W k (armPosition l))

theorem armRanks_eq_range (W : Finset Leaf) (k : Fin 4) :
    armRanks W k = Finset.range (armCount W k) := by
  have hinj : Set.InjOn (fun l => armRank W k (armPosition l)) (armSet W k) := by
    intro a ha b hb hab
    have hwa := (Finset.mem_filter.mp ha).1
    have hwb := (Finset.mem_filter.mp hb).1
    have hfa := armSet_member_form W k ha
    have hfb := armSet_member_form W k hb
    rw [hfa] at hwa
    rw [hfb] at hwb
    have heq := (armRank_eq_iff W k hwa hwb).mp hab
    rw [hfa, hfb, heq]
  have hsubset : armRanks W k ⊆ Finset.range (armCount W k) := by
    intro r hr
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hr
    have hwl := (Finset.mem_filter.mp hl).1
    rw [armSet_member_form W k hl] at hwl
    exact Finset.mem_range.mpr (armRank_lt_count W k hwl)
  apply Finset.eq_of_subset_of_card_le hsubset
  simp only [Finset.card_range, armRanks, Finset.card_image_of_injOn hinj, armCount]
  exact le_refl _

def selectedArm (t : Counts) (W : Finset Leaf) (k : Fin 4) : List Nat :=
  (List.range (t.armLength k)).filter (fun j => decide (Leaf.arm k j ∈ W))

@[simp] theorem mem_selectedArm (t : Counts) (W : Finset Leaf) (k : Fin 4) (j : Nat) :
    j ∈ selectedArm t W k ↔ j < t.armLength k ∧ Leaf.arm k j ∈ W := by
  simp [selectedArm]

theorem selectedArm_rank_mem_iff (t : Counts) (W : Finset Leaf) (k : Fin 4)
    (hvalid : ∀ l ∈ W, l ∈ circular t) (r : Nat) :
    r ∈ (selectedArm t W k).map (armRank W k) ↔ r < armCount W k := by
  rw [← Finset.mem_range, ← armRanks_eq_range]
  constructor
  · intro hr
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hr
    have hw := (mem_selectedArm t W k j).mp hj
    exact Finset.mem_image.mpr ⟨Leaf.arm k j, Finset.mem_filter.mpr ⟨hw.2, rfl⟩, rfl⟩
  · intro hr
    obtain ⟨l, hl, heq⟩ := Finset.mem_image.mp hr
    have hwl := (Finset.mem_filter.mp hl).1
    have hform := armSet_member_form W k hl
    have hlt : armPosition l < t.armLength k := by
      have hmem := hvalid l hwl
      rw [hform] at hmem
      exact (arm_mem_circular_iff t k _).mp hmem
    have hselected : armPosition l ∈ selectedArm t W k := by
      rw [mem_selectedArm]
      exact ⟨hlt, hform ▸ hwl⟩
    exact List.mem_map.mpr ⟨armPosition l, hselected, heq⟩

theorem selectedArm_rank_eq_range (t : Counts) (W : Finset Leaf) (k : Fin 4)
    (hvalid : ∀ l ∈ W, l ∈ circular t) :
    (selectedArm t W k).map (armRank W k) = List.range (armCount W k) := by
  have hsorted : ((selectedArm t W k).map (armRank W k)).SortedLT := by
    apply List.Pairwise.sortedLT
    rw [List.pairwise_map]
    have hbase : (selectedArm t W k).Pairwise (· < ·) :=
      (List.pairwise_lt_range).filter _
    apply hbase.imp_of_mem
    intro a b ha hb hab
    exact armRank_strictMonoOn_selected W k
      ((mem_selectedArm t W k a).mp ha).2 hab
  apply hsorted.eq_of_mem_iff (List.sortedLT_range _)
  intro r
  rw [selectedArm_rank_mem_iff t W k hvalid, List.mem_range]

#print axioms armRanks_eq_range
#print axioms selectedArm_rank_eq_range


theorem filter_compress_arm (t : Counts) (W : Finset Leaf) (k : Fin 4)
    (hvalid : ∀ l ∈ W, l ∈ circular t) :
    ((((List.range (t.armLength k)).map (Leaf.arm k)).filter
      (fun l => decide (l ∈ W))).map (compressLeaf W)) =
      (List.range (armCount W k)).map (Leaf.arm k) := by
  rw [List.filter_map, List.map_map]
  change ((selectedArm t W k).map (fun j => Leaf.arm k (armRank W k j))) = _
  simpa only [List.map_map, Function.comp_def] using
    congrArg (List.map (Leaf.arm k)) (selectedArm_rank_eq_range t W k hvalid)

/-- The retained, rank-compressed leaf cycle is literally the canonical cycle
of the compressed theta counts. -/
theorem compressed_circular_eq (t : Counts) (W : Finset Leaf)
    (hvalid : ∀ l ∈ W, l ∈ circular t) (hc1 : Leaf.c1 ∈ W) (hc2 : Leaf.c2 ∈ W) :
    (((circular t).filter (fun l => decide (l ∈ W))).map (compressLeaf W)) =
      circular (compressedCounts W) := by
  have h0 := filter_compress_arm t W 0 hvalid
  have h1 := filter_compress_arm t W 1 hvalid
  have h2 := filter_compress_arm t W 2 hvalid
  have h3 := filter_compress_arm t W 3 hvalid
  simp +decide only [Counts.armLength, ite_true, ite_false] at h0 h1 h2 h3
  have hfirst : (([Leaf.c1].filter fun l => decide (l ∈ W)).map (compressLeaf W)) =
      [Leaf.c1] := by simp [hc1, compressLeaf]
  have hsecond : (([Leaf.c2].filter fun l => decide (l ∈ W)).map (compressLeaf W)) =
      [Leaf.c2] := by simp [hc2, compressLeaf]
  simp only [circular, List.filter_append, List.map_append, List.map_reverse,
    List.filter_reverse, hfirst, hsecond]
  rw [h0, h1, h2, h3]
  rfl

theorem compressed_retained_circular_eq (t : Counts)
    (p q i j : Fin (circular t).length) :
    (((circular t).filter (fun l => decide (l ∈ retainedWitnesses t p q i j))).map
      (compressLeaf (retainedWitnesses t p q i j))) =
      circular (compressedCounts (retainedWitnesses t p q i j)) := by
  apply compressed_circular_eq
  · exact fun _ hl => retainedWitnesses_subset_circular t p q i j hl
  · simp [retainedWitnesses]
  · simp [retainedWitnesses]

theorem compressed_retained_total_le (t : Counts)
    (p q i j : Fin (circular t).length) :
    (compressedCounts (retainedWitnesses t p q i j)).total ≤ 6 := by
  simp only [retainedWitnesses, compressedCounts_add_hybrids]
  exact compressed_sixWitnesses_total_le t p q i j

#print axioms compressed_circular_eq
#print axioms compressed_retained_circular_eq

end Nanuq.Theta



