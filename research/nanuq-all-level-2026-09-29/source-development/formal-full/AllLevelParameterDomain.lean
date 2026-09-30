import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
Exact real-algebra certification of the independently enumerated all-level
anchor inequality domain. The sixteen expressions below are the normalized
rows of the external finite certificate. This file proves their exact domain
and a counterexample to using only the ten <=4-taxon rows.

The network representation, enumeration completeness, and six-label reduction
are not redefined as hypotheses of a claimed network theorem here: their
external computer-assisted proof status is recorded in ALL-LEVEL-QUALITY.md.
-/
namespace Nanuq.AllLevelParameters

/-- All sixteen normalized coefficient inequalities, with shared-anchor entry 1. -/
def AllRows (c s a o : ℝ) : Prop :=
  0 ≤ o - 1 ∧ 0 ≤ s - 1 ∧ 0 ≤ a - c ∧ 0 ≤ s - c ∧
  0 ≤ o - s ∧ 0 ≤ 2 * a - s ∧ 0 ≤ a ∧ 0 ≤ s - a ∧
  0 ≤ s - o ∧ 0 ≤ s ∧ 0 ≤ c ∧ 0 ≤ 1 - c ∧
  0 ≤ 1 - s ∧ 0 ≤ 1 - a ∧ 0 ≤ 1 - o ∧ (0 : ℝ) ≤ 1

/-- The ten row types first appearing on three or four taxa. -/
def FourTaxonRows (c s a o : ℝ) : Prop :=
  0 ≤ o - 1 ∧ 0 ≤ s - 1 ∧ 0 ≤ a ∧ 0 ≤ s ∧ 0 ≤ c ∧
  0 ≤ 1 - c ∧ 0 ≤ 1 - s ∧ 0 ≤ 1 - a ∧ 0 ≤ 1 - o ∧ (0 : ℝ) ≤ 1

def ExactDomain (c s a o : ℝ) : Prop :=
  s = 1 ∧ o = 1 ∧ (1 : ℝ) / 2 ≤ a ∧ a ≤ 1 ∧ 0 ≤ c ∧ c ≤ a

theorem all_rows_iff_exact_domain (c s a o : ℝ) :
    AllRows c s a o ↔ ExactDomain c s a o := by
  constructor
  · rintro ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16⟩
    unfold ExactDomain
    exact ⟨by linarith, by linarith, by linarith, by linarith, h11, by linarith⟩
  · rintro ⟨hs,ho,ha0,ha1,hc0,hca⟩
    unfold AllRows
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> linarith

theorem four_taxon_rows_iff_box (c s a o : ℝ) :
    FourTaxonRows c s a o ↔
      s = 1 ∧ o = 1 ∧ 0 ≤ a ∧ a ≤ 1 ∧ 0 ≤ c ∧ c ≤ 1 := by
  constructor
  · rintro ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩
    exact ⟨by linarith, by linarith, h3, by linarith, h5, by linarith⟩
  · rintro ⟨hs,ho,ha0,ha1,hc0,hc1⟩
    unfold FourTaxonRows
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> linarith

/-- Four-taxon rows accept a point that the five-taxon row a-c rejects. -/
theorem four_taxon_certificate_insufficient :
    FourTaxonRows 1 1 ((1 : ℝ) / 2) 1 ∧
      ¬ AllRows 1 1 ((1 : ℝ) / 2) 1 := by
  norm_num [FourTaxonRows, AllRows]

/-- The second essential five-taxon constraint is a >= 1/2. -/
theorem four_taxon_certificate_misses_adjacent_lower_bound :
    FourTaxonRows 0 1 0 1 ∧ ¬ AllRows 0 1 0 1 := by
  norm_num [FourTaxonRows, AllRows]

theorem original_and_modified_in_domain :
    ExactDomain 0 1 ((1 : ℝ) / 2) 1 ∧
      ExactDomain ((1 : ℝ) / 2) 1 ((1 : ℝ) / 2) 1 := by
  norm_num [ExactDomain]

#print axioms all_rows_iff_exact_domain
#print axioms four_taxon_rows_iff_box
#print axioms four_taxon_certificate_insufficient
#print axioms four_taxon_certificate_misses_adjacent_lower_bound

end Nanuq.AllLevelParameters
