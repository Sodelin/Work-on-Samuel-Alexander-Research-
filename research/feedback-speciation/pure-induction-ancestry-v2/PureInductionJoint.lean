import FiniteEpigenetic
import Mathlib.Tactic.FinCases

/-!
Finite pure-induction joint parent/marker process. This draft has not been
compiled. The only released dependency is FiniteEpigenetic; no release file is
modified. Pulse is a distinct first-step marking intervention.
-/

namespace PureInductionJoint

open scoped BigOperators

abbrev BState := Fin 3 × Fin 3
abbrev Table := Fin 2 → Fin 2 → Fin 2
abbrev Homologues := Fin 2 → Fin 2 → Fin 2
abbrev RawNoise := Fin 2 → Fin 2 → Fin 14

def other (d : Fin 2) : Fin 2 := if d = 0 then 1 else 0

def rawParent (u : RawNoise) : Table :=
  fun d s => if (u d s).val % 7 < 6 then d else other d

def rawHomologue (u : RawNoise) : Homologues :=
  fun d s => ⟨(u d s).val / 7, by have h := (u d s).isLt; omega⟩

def bCopies (b : BState) (d : Fin 2) : Nat :=
  if d = 0 then b.1.val else b.2.val

def ordinaryMarker (b : BState) (p : Table) (h : Homologues)
    (d s : Fin 2) : Nat :=
  if (h d s).val < bCopies b (p d s) then 1 else 0

/-- A first-step intervention: a foreign gamete from adult 0 into deme 1 is
marked B even when its source adult is bb. Parenthood is unchanged. -/
def pulseMarker (p : Table) (h : Homologues) (d s : Fin 2) : Nat :=
  if d = 1 ∧ p d s = 0 then 1
  else ordinaryMarker ((0, 0) : BState) p h d s

def pairCounts (f : Fin 2 → Fin 2 → Nat) : Nat × Nat :=
  (f 0 0 + f 0 1, f 1 0 + f 1 1)

def ordinaryStep (b : BState) (p : Table) (h : Homologues) : Nat × Nat :=
  pairCounts (ordinaryMarker b p h)

def pulseInitStep (p : Table) (h : Homologues) : Nat × Nat :=
  pairCounts (pulseMarker p h)

def rawOrdinaryStep (b : BState) (u : RawNoise) : Nat × Nat :=
  ordinaryStep b (rawParent u) (rawHomologue u)

def rawPulseInitStep (u : RawNoise) : Nat × Nat :=
  pulseInitStep (rawParent u) (rawHomologue u)

/-- Each fixed homologue has six local raw tickets and one foreign raw ticket. -/
theorem local_fibre (h : Fin 2) :
    (Finset.univ.filter (fun u : Fin 14 =>
      u.val % 7 < 6 ∧ u.val / 7 = h.val)).card = 6 := by
  fin_cases h <;> decide

theorem foreign_fibre (h : Fin 2) :
    (Finset.univ.filter (fun u : Fin 14 =>
      u.val % 7 = 6 ∧ u.val / 7 = h.val)).card = 1 := by
  fin_cases h <;> decide

/-- The compressed pair (parent table, homologue table) is weighted, not
uniform. Its raw Fin14^4 four-slot pushforward remains a separate proof. -/
def tableWeight (p : Table) : Nat :=
  ∏ d : Fin 2, ∏ s : Fin 2, if p d s = d then 6 else 1

def jointTotal : Nat :=
  ∑ p : Table, ∑ _h : Homologues, tableWeight p

theorem joint_total : jointTotal = 38416 := by
  decide +kernel

def ordinaryNumerator (b : BState) (c : Nat × Nat) : Nat :=
  ∑ p : Table, ∑ h : Homologues,
    if ordinaryStep b p h = c then tableWeight p else 0

def pulseNumerator (c : Nat × Nat) : Nat :=
  ∑ p : Table, ∑ h : Homologues,
    if pulseInitStep p h = c then tableWeight p else 0

/-- Both children choose adults 0 and 1 in ordered slots 0 and 1. -/
def designated (p : Table) : Bool :=
  (p 0 0 == 0) && (p 0 1 == 1) && (p 1 0 == 0) && (p 1 1 == 1)

def designatedNumerator : Nat :=
  ∑ p : Table, ∑ _h : Homologues,
    if designated p then tableWeight p else 0

theorem designated_numerator : designatedNumerator = 576 := by
  decide +kernel

theorem designated_probability : (designatedNumerator : ℚ) / 38416 = 36 / 2401 := by
  rw [designated_numerator]
  norm_num

def embed (b : BState) : FiniteEpigenetic.State :=
  ⟨54 + 9 * b.1.val + b.2.val, by
    have h0 := b.1.isLt
    have h1 := b.2.isLt
    omega⟩

def b01 : BState := (0, 1)
def b22 : BState := (2, 2)

theorem ordinary_01_22_numerator :
    ordinaryNumerator b01 (2, 2) = 36 := by
  decide +kernel

/-- One ordinary count marginal of the actual joint parent/homologue law
equals the frozen pure-induction transition at embedded states 55 -> 74. -/
theorem ordinary_01_22_frozen_cross :
    ordinaryNumerator b01 (2, 2) *
      FiniteEpigenetic.denominator (embed b01).val =
    FiniteEpigenetic.numerator true false (embed b01).val (embed b22).val *
      38416 := by
  rw [ordinary_01_22_numerator]
  decide +kernel

theorem ordinary_01_22_frozen_real :
    (ordinaryNumerator b01 (2, 2) : ℝ) / 38416 =
      (FiniteEpigenetic.kernel true).transition (embed b01) (embed b22) := by
  change (ordinaryNumerator b01 (2, 2) : ℝ) / 38416 =
    (FiniteEpigenetic.numerator true false (embed b01).val (embed b22).val : ℝ) /
      (FiniteEpigenetic.denominator (embed b01).val : ℝ)
  have hden : 0 < FiniteEpigenetic.denominator (embed b01).val := by
    decide +kernel
  have hd : (FiniteEpigenetic.denominator (embed b01).val : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hden)
  apply (div_eq_div_iff (by norm_num : (38416 : ℝ) ≠ 0) hd).2
  have h := congrArg (fun n : Nat => (n : ℝ)) ordinary_01_22_frozen_cross
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using h

theorem pulse_00_01_numerator :
    pulseNumerator (0, 1) = 9408 := by
  decide +kernel

/-- The pulse is compared to frozen initialization, never to ordinary
inheritance from the unmarked (0,0) adults. -/
theorem pulse_00_01_frozen_cross :
    pulseNumerator (0, 1) * FiniteEpigenetic.denominator 54 =
      FiniteEpigenetic.numerator true true 54 (embed b01).val * 38416 := by
  rw [pulse_00_01_numerator]
  decide +kernel

theorem pulse_00_01_frozen_real :
    (pulseNumerator (0, 1) : ℝ) / 38416 =
      FiniteEpigenetic.pulse true (embed b01) := by
  change (pulseNumerator (0, 1) : ℝ) / 38416 =
    (FiniteEpigenetic.numerator true true 54 (embed b01).val : ℝ) /
      (FiniteEpigenetic.denominator 54 : ℝ)
  have hden : 0 < FiniteEpigenetic.denominator 54 := by decide +kernel
  have hd : (FiniteEpigenetic.denominator 54 : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hden)
  apply (div_eq_div_iff (by norm_num : (38416 : ℝ) ≠ 0) hd).2
  have h := congrArg (fun n : Nat => (n : ℝ)) pulse_00_01_frozen_cross
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using h

end PureInductionJoint

#print axioms PureInductionJoint.joint_total
#print axioms PureInductionJoint.designated_probability
#print axioms PureInductionJoint.ordinary_01_22_frozen_real
#print axioms PureInductionJoint.pulse_00_01_frozen_real




