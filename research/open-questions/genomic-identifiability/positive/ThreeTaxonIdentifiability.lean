import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
An elementary conditional identifiability result for a prescribed three-taxon law.

Source of the model formula: Allman, Degnan, and Rhodes, arXiv:0912.4472v2,
Introduction, example surrounding Eq. (1):
https://arxiv.org/html/0912.4472v2#S1
For c = exp(-t), the matching rooted topology has probability 1 - 2*c/3;
each other rooted topology has probability c/3. For t > 0, 0 < c < 1.

This file checks consequences of that prescribed formula. It does not derive
the multispecies coalescent or formalize the exponential parameter bridge.
The data object is the exact population law of rooted gene-tree topologies.
The target is the rooted topology on three already designated taxa, not
species delimitation, reproductive compatibility, or an arbitrary species
concept. It provides no certainty from finitely many loci or raw sequences.
This is a formalization of a known elementary result, with no novelty claim.
-/

namespace ThreeTaxonIdentifiability

/-- The three rooted binary topologies on a fixed set of three labeled taxa. -/
inductive Topology where
  | ab_c
  | ac_b
  | bc_a
  deriving DecidableEq

/-- `s` is the designated species topology; `g` is a gene-tree topology. -/
noncomputable def law (s : Topology) (c : ℝ) (g : Topology) : ℝ :=
  if g = s then 1 - 2 * c / 3 else c / 3

@[simp] theorem law_self (s : Topology) (c : ℝ) :
    law s c s = 1 - 2 * c / 3 := by
  simp [law]

theorem law_other (s g : Topology) (c : ℝ) (h : g ≠ s) :
    law s c g = c / 3 := by
  simp [law, h]

/-- Nonnegativity requires the stated probability parameter bounds. -/
theorem law_nonnegative (s g : Topology) (c : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) : 0 ≤ law s c g := by
  by_cases h : g = s
  · simp [law, h]
    linarith
  · simp [law, h]
    linarith

/-- The three displayed probabilities sum to one. -/
theorem law_normalized (s : Topology) (c : ℝ) :
    law s c .ab_c + law s c .ac_b + law s c .bc_a = 1 := by
  cases s <;> simp [law] <;> ring

/-- The gap between the matching probability and either alternative is 1-c. -/
theorem probability_gap (s g : Topology) (c : ℝ) (h : g ≠ s) :
    law s c s - law s c g = 1 - c := by
  rw [law_self, law_other s g c h]
  ring

/-- Below the collapsed boundary, the designated topology is a strict maximum. -/
theorem strict_maximum (s g : Topology) (c : ℝ)
    (hc : c < 1) (h : g ≠ s) : law s c g < law s c s := by
  have gap := probability_gap s g c h
  linarith

/-- The exact law has a unique maximizer, namely the designated topology. -/
theorem unique_maximizer (s g : Topology) (c : ℝ) (hc : c < 1) :
    (∀ k, law s c k ≤ law s c g) ↔ g = s := by
  constructor
  · intro maximal
    by_contra h
    have strict := strict_maximum s g c hc h
    have weak := maximal s
    linarith
  · intro h
    subst g
    intro k
    by_cases h : k = s
    · subst k
      exact le_refl _
    · exact le_of_lt (strict_maximum s k c hc h)

/-- Distinct transformed branch lengths may be allowed in the comparison. -/
theorem topology_identifiable (s r : Topology) (c d : ℝ)
    (hc : c < 1) (hd : d < 1) (heq : law s c = law r d) : s = r := by
  by_contra h
  have left := strict_maximum s r c hc (Ne.symm h)
  have right := strict_maximum r s d hd h
  have at_s := congrFun heq s
  have at_r := congrFun heq r
  linarith

/-- In fact both topology and the transformed branch parameter are identifiable. -/
theorem law_identifiable (s r : Topology) (c d : ℝ)
    (hc : c < 1) (hd : d < 1) :
    law s c = law r d ↔ s = r ∧ c = d := by
  constructor
  · intro heq
    have hsr := topology_identifiable s r c d hc hd heq
    refine ⟨hsr, ?_⟩
    subst r
    have h := congrFun heq s
    simp only [law_self] at h
    linarith
  · rintro ⟨rfl, rfl⟩
    rfl

/-- At c=1 (corresponding to t=0), all three probabilities coincide. -/
theorem boundary_uniform (s g : Topology) : law s 1 g = 1 / 3 := by
  by_cases h : g = s <;> norm_num [law, h]

/-- At the collapsed boundary, the law is independent of the resolved label. -/
theorem boundary_same_law (s r : Topology) : law s 1 = law r 1 := by
  funext g
  rw [boundary_uniform, boundary_uniform]

/-- No decoder of the boundary law recovers every resolved label. -/
theorem no_boundary_decoder (decode : (Topology → ℝ) → Topology) :
    ¬ ∀ s, decode (law s 1) = s := by
  intro correct
  have ha := correct Topology.ab_c
  have hb := correct Topology.ac_b
  rw [boundary_same_law Topology.ab_c Topology.ac_b] at ha
  rw [hb] at ha
  cases ha

end ThreeTaxonIdentifiability

#print axioms ThreeTaxonIdentifiability.law_nonnegative
#print axioms ThreeTaxonIdentifiability.law_normalized
#print axioms ThreeTaxonIdentifiability.unique_maximizer
#print axioms ThreeTaxonIdentifiability.law_identifiable
#print axioms ThreeTaxonIdentifiability.boundary_uniform
#print axioms ThreeTaxonIdentifiability.no_boundary_decoder
