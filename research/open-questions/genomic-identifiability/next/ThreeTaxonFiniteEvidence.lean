import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
Finite observations versus the exact three-taxon law.
The prescribed probabilities are the classical three-taxon MSC formula.
This module does not derive that process, delimit species, or supply a sampling
confidence bound. Sample products explicitly assume independent loci.
The labels are rooted relationships on three already designated taxa.
-/
namespace ThreeTaxonFiniteEvidence

inductive Topology where
  | ab_c | ac_b | bc_a
  deriving DecidableEq

noncomputable def law (s : Topology) (c : ℝ) (g : Topology) : ℝ :=
  if g = s then 1 - 2 * c / 3 else c / 3

@[simp] theorem law_self (s : Topology) (c : ℝ) :
    law s c s = 1 - 2 * c / 3 := by simp [law]

theorem law_other (s g : Topology) (c : ℝ) (h : g ≠ s) :
    law s c g = c / 3 := by simp [law, h]

theorem law_normalized (s : Topology) (c : ℝ) :
    law s c .ab_c + law s c .ac_b + law s c .bc_a = 1 := by
  cases s <;> simp [law] <;> ring

theorem law_lower_bound (s g : Topology) (c : ℝ) (hc1 : c ≤ 1) :
    c / 3 ≤ law s c g := by
  by_cases h : g = s
  · simp [law, h]
    linarith
  · simp [law, h]

theorem law_positive (s g : Topology) (c : ℝ)
    (hc0 : 0 < c) (hc1 : c ≤ 1) : 0 < law s c g := by
  have h := law_lower_bound s g c hc1
  linarith

/-- The mass of a specified finite ordered sample under the iid model. -/
noncomputable def sampleMass (s : Topology) (c : ℝ) : List Topology → ℝ
  | [] => 1
  | g :: gs => law s c g * sampleMass s c gs

/-- Every finite sample has positive mass under every label when 0<c≤1. -/
theorem sampleMass_positive (s : Topology) (c : ℝ)
    (hc0 : 0 < c) (hc1 : c ≤ 1) (xs : List Topology) :
    0 < sampleMass s c xs := by
  induction xs with
  | nil => norm_num [sampleMass]
  | cons g gs ih => exact mul_pos (law_positive s g c hc0 hc1) ih

/-- A quantitative lower bound on the mass of each individual sample. -/
theorem sampleMass_lower_bound (s : Topology) (c : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (xs : List Topology) :
    (c / 3) ^ xs.length ≤ sampleMass s c xs := by
  induction xs with
  | nil => simp [sampleMass]
  | cons g gs ih =>
      simp only [List.length_cons, sampleMass, pow_succ]
      have hc3 : 0 ≤ c / 3 := by linarith
      calc
        (c / 3) ^ gs.length * (c / 3) =
            (c / 3) * (c / 3) ^ gs.length := mul_comm _ _
        _ ≤ law s c g * sampleMass s c gs :=
          mul_le_mul (law_lower_bound s g c hc1) ih (pow_nonneg hc3 _) 
            (le_trans hc3 (law_lower_bound s g c hc1))

/-- Distinct labels share every finite sample, even if exact laws differ. -/
theorem finite_sample_support_overlap (s r : Topology) (c d : ℝ)
    (hc0 : 0 < c) (hc1 : c ≤ 1) (hd0 : 0 < d) (hd1 : d ≤ 1)
    (xs : List Topology) :
    0 < sampleMass s c xs ∧ 0 < sampleMass r d xs :=
  ⟨sampleMass_positive s c hc0 hc1 xs,
   sampleMass_positive r d hd0 hd1 xs⟩

/-- Any decoder fails on a possible sample of any prescribed finite length. -/
theorem no_uniform_certain_decoder (n : ℕ) (c : ℝ)
    (hc0 : 0 < c) (hc1 : c ≤ 1) (decode : List Topology → Topology) :
    ¬ ∀ s xs, xs.length = n → 0 < sampleMass s c xs → decode xs = s := by
  intro correct
  let xs := List.replicate n Topology.ab_c
  have ha := correct Topology.ab_c xs (by simp [xs])
    (sampleMass_positive .ab_c c hc0 hc1 xs)
  have hb := correct Topology.ac_b xs (by simp [xs])
    (sampleMass_positive .ac_b c hc0 hc1 xs)
  rw [hb] at ha
  cases ha

/-- A decoder must err on a sample whose singleton mass is at least (c/3)^n.
This is not itself a formalization of total error probability. -/
theorem quantitative_error_witness (n : ℕ) (c : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (decode : List Topology → Topology) :
    ∃ s xs, xs.length = n ∧ decode xs ≠ s ∧
      (c / 3) ^ n ≤ sampleMass s c xs := by
  let xs := List.replicate n Topology.ab_c
  have hlen : xs.length = n := by simp [xs]
  have hlabel : ∃ s : Topology, decode xs ≠ s := by
    cases decode xs with
    | ab_c => exact ⟨.ac_b, by simp⟩
    | ac_b => exact ⟨.ab_c, by simp⟩
    | bc_a => exact ⟨.ab_c, by simp⟩
  obtain ⟨s, hs⟩ := hlabel
  refine ⟨s, xs, hlen, hs, ?_⟩
  simpa only [hlen] using sampleMass_lower_bound s c hc0 hc1 xs

/-- The exact mode gap is 1-c. -/
theorem probability_gap (s g : Topology) (c : ℝ) (h : g ≠ s) :
    law s c s - law s c g = 1 - c := by
  rw [law_self, law_other s g c h]
  ring

/-- Uniform perturbations smaller than half the gap preserve the strict mode.
The estimate q may be empirical frequencies, but no sampling event is assumed. -/
theorem robust_strict_mode (s g : Topology) (c ε : ℝ) (q : Topology → ℝ)
    (hgap : 2 * ε < 1 - c)
    (herror : ∀ k, |q k - law s c k| ≤ ε) (hgs : g ≠ s) : q g < q s := by
  have hs := abs_le.mp (herror s)
  have hg := abs_le.mp (herror g)
  have hp := probability_gap s g c hgs
  linarith

/-- Any maximizer of a sufficiently accurate estimate recovers the label. -/
theorem robust_maximizer_recovers (s r : Topology) (c ε : ℝ)
    (q : Topology → ℝ) (hgap : 2 * ε < 1 - c)
    (herror : ∀ k, |q k - law s c k| ≤ ε)
    (hmax : ∀ k, q k ≤ q r) : r = s := by
  by_contra h
  have hstrict := robust_strict_mode s r c ε q hgap herror h
  have hweak := hmax s
  linarith

/-- At exactly half the gap, a probability vector can tie the correct label
and an alternative, so strict recovery requires a strict error margin. -/
noncomputable def boundaryEstimate (c : ℝ) : Topology → ℝ
  | .ab_c => 1 / 2 - c / 6
  | .ac_b => 1 / 2 - c / 6
  | .bc_a => c / 3

theorem half_gap_tie (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    (∀ g, 0 ≤ boundaryEstimate c g) ∧
    (boundaryEstimate c .ab_c + boundaryEstimate c .ac_b +
      boundaryEstimate c .bc_a = 1) ∧
    (∀ g, |boundaryEstimate c g - law .ab_c c g| ≤ (1 - c) / 2) ∧
    boundaryEstimate c .ab_c = boundaryEstimate c .ac_b := by
  refine ⟨?_, ?_, ?_, rfl⟩
  · intro g
    cases g <;> simp [boundaryEstimate] <;> linarith
  · simp [boundaryEstimate]
    ring
  · intro g
    apply abs_le.mpr
    cases g <;> simp [boundaryEstimate, law] <;> (try constructor) <;> linarith

end ThreeTaxonFiniteEvidence

#print axioms ThreeTaxonFiniteEvidence.sampleMass_positive
#print axioms ThreeTaxonFiniteEvidence.sampleMass_lower_bound
#print axioms ThreeTaxonFiniteEvidence.finite_sample_support_overlap
#print axioms ThreeTaxonFiniteEvidence.no_uniform_certain_decoder
#print axioms ThreeTaxonFiniteEvidence.quantitative_error_witness
#print axioms ThreeTaxonFiniteEvidence.robust_strict_mode
#print axioms ThreeTaxonFiniteEvidence.robust_maximizer_recovers
#print axioms ThreeTaxonFiniteEvidence.half_gap_tie

