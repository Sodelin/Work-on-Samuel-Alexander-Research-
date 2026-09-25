import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import WongGARG

/-! Finite adjacent breakpoint cells, derived from the actual input annotations. -/
namespace WongBreakpointCells
open WongGARG AncestryViews
universe u v
noncomputable section
local instance (α : Type*) : DecidableEq α := Classical.decEq α
local instance (P : Prop) : Decidable P := Classical.propDecidable P

variable {Coord : Type v} [LinearOrder Coord]

def cellPairs (B : Finset Coord) : Finset (Coord × Coord) :=
  (B.product B).filter (fun p => p.1 < p.2 ∧ ∀ z ∈ B, ¬ (p.1 < z ∧ z < p.2))

def makeCell (B : Finset Coord) (p : {p // p ∈ cellPairs B}) : Interval Coord :=
  ⟨p.val.1, p.val.2, (Finset.mem_filter.mp p.property).2.1⟩

def cells (B : Finset Coord) : Finset (Interval Coord) :=
  (cellPairs B).attach.image (makeCell B)

theorem mem_cells_iff (B : Finset Coord) (I : Interval Coord) :
    I ∈ cells B ↔ I.lo ∈ B ∧ I.hi ∈ B ∧ ∀ z ∈ B, ¬ (I.lo < z ∧ z < I.hi) := by
  constructor
  · intro h
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp h
    have hp := Finset.mem_filter.mp p.property
    have hb := Finset.mem_product.mp hp.1
    exact ⟨hb.1, hb.2, hp.2.2⟩
  · rintro ⟨hl, hh, hn⟩
    have hp : (I.lo, I.hi) ∈ cellPairs B :=
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hl, hh⟩, I.proper, hn⟩
    apply Finset.mem_image.mpr
    refine ⟨⟨(I.lo, I.hi), hp⟩, Finset.mem_attach _ _, ?_⟩
    cases I
    rfl

private theorem interval_ext {I J : Interval Coord}
    (hl : I.lo = J.lo) (hh : I.hi = J.hi) : I = J := by
  cases I
  cases J
  cases hl
  cases hh
  rfl

theorem cells_pairwise_disjoint (B : Finset Coord) :
    ∀ I ∈ cells B, ∀ J ∈ cells B, I ≠ J → I.Disjoint J := by
  intro I hI J hJ hne x hx
  obtain ⟨hil, hih, hni⟩ := (mem_cells_iff B I).mp hI
  obtain ⟨hjl, hjh, hnj⟩ := (mem_cells_iff B J).mp hJ
  have hlo : I.lo = J.lo := by
    rcases lt_trichotomy I.lo J.lo with h | h | h
    · exact False.elim (hni J.lo hjl ⟨h, lt_of_le_of_lt hx.2.1 hx.1.2⟩)
    · exact h
    · exact False.elim (hnj I.lo hil ⟨h, lt_of_le_of_lt hx.1.1 hx.2.2⟩)
  have hhi : I.hi = J.hi := by
    rcases lt_trichotomy I.hi J.hi with h | h | h
    · exact False.elim (hnj I.hi hih ⟨hlo ▸ I.proper, h⟩)
    · exact h
    · exact False.elim (hni J.hi hjh ⟨hlo.symm ▸ J.proper, h⟩)
  exact hne (interval_ext hlo hhi)

theorem exists_cell_of_bracket (B : Finset Coord) (x lo hi : Coord)
    (hl : lo ∈ B) (hh : hi ∈ B) (hlo : lo ≤ x) (hhi : x < hi) :
    ∃ I ∈ cells B, I.Contains x := by
  let L := B.filter (fun z => z ≤ x)
  let U := B.filter (fun z => x < z)
  have hL : L.Nonempty := ⟨lo, Finset.mem_filter.mpr ⟨hl, hlo⟩⟩
  have hU : U.Nonempty := ⟨hi, Finset.mem_filter.mpr ⟨hh, hhi⟩⟩
  let a := L.max' hL
  let b := U.min' hU
  have ha := Finset.mem_filter.mp (Finset.max'_mem L hL)
  have hb := Finset.mem_filter.mp (Finset.min'_mem U hU)
  have hab : a < b := lt_of_le_of_lt ha.2 hb.2
  let I : Interval Coord := ⟨a, b, hab⟩
  refine ⟨I, (mem_cells_iff B I).mpr ⟨ha.1, hb.1, ?_⟩, ha.2, hb.2⟩
  intro z hz hbetween
  by_cases hzx : z ≤ x
  · have hza : z ≤ a := Finset.le_max' L z (Finset.mem_filter.mpr ⟨hz, hzx⟩)
    exact (not_lt_of_ge hza) hbetween.1
  · have hbz : b ≤ z := Finset.min'_le U z
      (Finset.mem_filter.mpr ⟨hz, lt_of_not_ge hzx⟩)
    exact (not_lt_of_ge hbz) hbetween.2

variable {Node : Type u} [Fintype Node] (G : GARG Node Coord)

theorem locus_covered {x : Coord} {a b : Node} (h : G.AtLocus x a b) :
    ∃ I ∈ cells G.breakpoints, I.Contains x := by
  obtain ⟨e, he, _, _, I, hI, hx⟩ := h
  exact exists_cell_of_bracket G.breakpoints x I.lo I.hi
    (G.lo_mem_breakpoints he hI) (G.hi_mem_breakpoints he hI) hx.1 hx.2

theorem locus_constant_on_cell {I : Interval Coord} (hI : I ∈ cells G.breakpoints)
    {x : Coord} (hx : I.Contains x) (a b : Node) :
    G.AtLocus x a b ↔ G.AtLocus I.lo a b := by
  apply (G.locus_constant_without_breakpoint hx.1 ?_ a b).symm
  intro z hz hcross
  exact ((mem_cells_iff G.breakpoints I).mp hI).2.2 z hz
    ⟨hcross.1, lt_of_le_of_lt hcross.2 hx.2⟩

end
end WongBreakpointCells

#print axioms WongBreakpointCells.cells_pairwise_disjoint
#print axioms WongBreakpointCells.exists_cell_of_bracket
#print axioms WongBreakpointCells.locus_covered
#print axioms WongBreakpointCells.locus_constant_on_cell
