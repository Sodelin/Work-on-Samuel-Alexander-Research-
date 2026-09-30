import AnchorPortPatterns

namespace Nanuq.PortPatterns
open scoped BigOperators

/-- A map constant outside a selected set can occupy at most one more port
than the number of selected taxa. -/
theorem portCount_le_card_add_one {P : Type*} [DecidableEq P]
    (f : Fin 4 → P) (S : Finset (Fin 4)) (p : P)
    (hconstant : ∀ i, i ∉ S → f i = p) : portCount f ≤ S.card + 1 := by
  have hsubset : Finset.univ.image f ⊆ S.image f ∪ {p} := by
    intro q hq
    obtain ⟨i,_hi,rfl⟩ := Finset.mem_image.mp hq
    by_cases hi : i ∈ S
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i,hi,rfl⟩)
    · exact Finset.mem_union_right _ (by simp [hconstant i hi])
  have hle := Finset.card_le_card hsubset
  have hunion := Finset.card_union_le (S.image f) {p}
  have himage := Finset.card_image_le (s := S) (f := f)
  simp only [Finset.card_singleton] at hunion
  unfold portCount
  omega

/-- Two branch projections related by a bridge must put exactly two of four
taxa toward one another, provided each projection occupies at least three ports. -/
theorem bridge_fiber_card_two {P Q : Type*} [DecidableEq P] [DecidableEq Q]
    (f : Fin 4 → P) (g : Fin 4 → Q) (p : P) (q : Q)
    (htransport : ∀ i, f i ≠ p → g i = q)
    (hf : 3 ≤ portCount f) (hg : 3 ≤ portCount g) :
    (Finset.univ.filter (fun i => f i = p)).card = 2 := by
  let S : Finset (Fin 4) := Finset.univ.filter (fun i => f i = p)
  have hmem (i : Fin 4) : i ∈ S ↔ f i = p := by simp [S]
  have hboundG := portCount_le_card_add_one g S q (fun i hi =>
    htransport i (fun he => hi ((hmem i).mpr he)))
  have hboundF := portCount_le_card_add_one f Sᶜ p (fun i hi => by
    have hs : i ∈ S := by simpa using hi
    exact (hmem i).mp hs)
  have hcard : S.card ≤ 4 := by simpa using Finset.card_le_univ S
  have hcompl : Sᶜ.card = 4 - S.card := by simp [Finset.card_compl]
  change S.card = 2
  omega

#print axioms portCount_le_card_add_one
#print axioms bridge_fiber_card_two
end Nanuq.PortPatterns