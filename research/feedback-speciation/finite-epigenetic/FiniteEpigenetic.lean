import FiniteFixation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Exact finite counterpart of Planidin et al. (2025), for N=1 diploid per deme,
m=1/4, s=r=1/2, secondary contact, and either mu=0 or mu=1/2, phi=1.
A state stores E-copy and B-copy counts for each adult. The mathematical
correspondence of this free-recombination specialization to the phased
life cycle is separately audited in INDEPENDENT-MODEL-AUDIT.md.
No infinite-population comparison or empirical speciation claim is made.
-/
namespace FiniteEpigenetic
open scoped BigOperators
abbrev State := Fin 81
-- genotype=3*(E copies)+(B copies); state=9*(deme 1 genotype)+(deme 2 genotype).
def genotype (x d : ℕ) : ℕ := if d = 0 then x / 9 else x % 9
def eCount (g : ℕ) : ℕ := g / 3
def bCount (g : ℕ) : ℕ := g % 3
def copies (n bit : ℕ) : ℕ := if bit = 0 then 2-n else n
-- Fitness is the following numerator over 4.
def fitness (g d : ℕ) : ℕ := if d = 0 then 2+eCount g else 4-eCount g
-- Gamete probability numerator; denominator is gameteDen.
def gameteNum (pulse : Bool) (x d h : ℕ) : ℕ :=
  let resident := genotype x d
  let other := genotype x (1-d)
  let otherB := if pulse && d == 1 then 2 else bCount other
  3 * fitness resident d * copies (eCount resident) (h/2) * copies (bCount resident) (h%2) +
    fitness other d * copies (eCount other) (h/2) * copies otherB (h%2)
def gameteDen (x d : ℕ) : ℕ :=
  4 * (3 * fitness (genotype x d) d + fitness (genotype x (1-d)) d)
-- Two independent gametes form one offspring; pure induction resets E after mating.
def offspringNum (epi pulse : Bool) (x d g : ℕ) : ℕ :=
  let u := gameteNum pulse x d 0
  let v := gameteNum pulse x d 1
  let w := gameteNum pulse x d 2
  let z := gameteNum pulse x d 3
  if epi then
    if eCount g = (if d = 0 then 2 else 0) then
      [(u+w)^2, 2*(u+w)*(v+z), (v+z)^2].getD (bCount g) 0
    else 0
  else
    [u*u, 2*u*v, v*v, 2*u*w, 2*u*z+2*v*w, 2*v*z, w*w, 2*w*z, z*z].getD g 0
def numerator (epi pulse : Bool) (x y : ℕ) : ℕ :=
  offspringNum epi pulse x 0 (y/9) * offspringNum epi pulse x 1 (y%9)
def denominator (x : ℕ) : ℕ := (gameteDen x 0)^2 * (gameteDen x 1)^2
def win (x : ℕ) : Bool := bCount (x/9) == 2 && bCount (x%9) == 2
def loss (x : ℕ) : Bool := bCount (x/9) == 0 && bCount (x%9) == 0
def terminal (x : ℕ) : Bool := win x || loss x
def certificateDen (epi : Bool) : ℕ := if epi then 8580 else 3720412
def certificateNum (epi : Bool) (x : ℕ) : ℕ :=
  (if epi then [0, 2145, 4290, 0, 2200, 4400, 0, 2145, 4290, 2145, 4290, 6435, 2090, 4290, 6490, 2145, 4290, 6435, 4290, 6435, 8580, 4180, 6380, 8580, 4290, 6435, 8580, 0, 2106, 4212, 0, 2145, 4290, 0, 2090, 4180, 2184, 4290, 6396, 2145, 4290, 6435, 2200, 4290, 6380, 4368, 6474, 8580, 4290, 6435, 8580, 4400, 6490, 8580, 0, 2145, 4290, 0, 2184, 4368, 0, 2145, 4290, 2145, 4290, 6435, 2106, 4290, 6474, 2145, 4290, 6435, 4290, 6435, 8580, 4212, 6396, 8580, 4290, 6435, 8580] else [0, 930103, 1860206, 0, 958786, 1917572, 0, 930103, 1860206, 930103, 1860206, 2790309, 901420, 1860206, 2818992, 930103, 1860206, 2790309, 1860206, 2790309, 3720412, 1802840, 2761626, 3720412, 1860206, 2790309, 3720412, 0, 907164, 1814328, 0, 930103, 1860206, 0, 901420, 1802840, 953042, 1860206, 2767370, 930103, 1860206, 2790309, 958786, 1860206, 2761626, 1906084, 2813248, 3720412, 1860206, 2790309, 3720412, 1917572, 2818992, 3720412, 0, 930103, 1860206, 0, 953042, 1906084, 0, 930103, 1860206, 930103, 1860206, 2790309, 907164, 1860206, 2813248, 930103, 1860206, 2790309, 1860206, 2790309, 3720412, 1814328, 2767370, 3720412, 1860206, 2790309, 3720412]).getD x 0
def resultNum (epi : Bool) : ℕ := if epi then 1 else 323808055
def resultDen (epi : Bool) : ℕ := if epi then 14 else 4466354606

-- These finite integer propositions are reduced and checked by Lean's kernel.
def IntegerFacts (epi : Bool) : Prop :=
  (0 < certificateDen epi) ∧
  (0 < resultDen epi) ∧
  (∀ x : State, 0 < denominator x) ∧
  (∀ x : State, ∑ y : State, numerator epi false x y = denominator x) ∧
  (∀ x : State, certificateNum epi x ≤ certificateDen epi) ∧
  (∀ x : State, win x = true → certificateNum epi x = certificateDen epi) ∧
  (∀ x : State, loss x = true → certificateNum epi x = 0) ∧
  (∀ x : State, ∑ y : State, numerator epi false x y * certificateNum epi y =
      denominator x * certificateNum epi x) ∧
  (∀ x : State, denominator x ≤
      100 * ∑ y : State, if terminal y then numerator epi false x y else 0) ∧
  (∀ x y : State, win x = true → win y ≠ true → numerator epi false x y = 0) ∧
  (∀ x y : State, loss x = true → loss y ≠ true → numerator epi false x y = 0) ∧
  (∑ y : State, numerator epi true 54 y = denominator 54) ∧
  ((∑ y : State, numerator epi true 54 y * certificateNum epi y) * resultDen epi =
      resultNum epi * denominator 54 * certificateDen epi)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem integer_facts (epi : Bool) : IntegerFacts epi := by
  cases epi <;> unfold IntegerFacts <;> decide +kernel

theorem win_loss_disjoint (x : State) : win x = true → loss x = true → False := by
  revert x
  decide +kernel

noncomputable section
open FiniteFixation
attribute [local instance] Classical.propDecidable

def boundary : Boundary State where
  Win x := win x = true
  Loss x := loss x = true
  disjoint := win_loss_disjoint

private theorem sum_div (f : State → ℝ) (a : ℝ) :
    (∑ x : State, f x) / a = ∑ x : State, f x / a := by
  simp only [div_eq_mul_inv, Finset.sum_mul]

private theorem nat_sum_cast (f : State → ℕ) :
    (∑ x : State, (f x : ℝ)) = ((∑ x : State, f x : ℕ) : ℝ) := by simp

def kernel (epi : Bool) : Kernel State where
  transition x y := (numerator epi false x y : ℝ) / (denominator x : ℝ)
  nonneg x y := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  row_sum x := by
    obtain ⟨hL,hR,hD,hrow,rest⟩ := integer_facts epi
    rw [← sum_div, nat_sum_cast, hrow x]
    exact div_self (by exact_mod_cast (Nat.ne_of_gt (hD x)))

def certificate (epi : Bool) (x : State) : ℝ :=
  (certificateNum epi x : ℝ) / (certificateDen epi : ℝ)

theorem certificate_valid (epi : Bool) :
    Certificate (kernel epi) boundary (certificate epi) := by
  obtain ⟨hL,hR,hD,hrow,hbounds,hwin,hloss,hharm,rest⟩ := integer_facts epi
  have Lpos : 0 < (certificateDen epi : ℝ) := by exact_mod_cast hL
  have Lne : (certificateDen epi : ℝ) ≠ 0 := ne_of_gt Lpos
  constructor
  · intro x
    constructor
    · exact div_nonneg (Nat.cast_nonneg _) (le_of_lt Lpos)
    · exact (div_le_one Lpos).2 (by exact_mod_cast hbounds x)
  · intro x hx
    change (certificateNum epi x : ℝ) / _ = 1
    rw [hwin x hx, div_self Lne]
  · intro x hx
    change (certificateNum epi x : ℝ) / _ = 0
    rw [hloss x hx, Nat.cast_zero, zero_div]
  · intro x
    have Dne : (denominator x : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hD x))
    change (∑ y : State, ((numerator epi false x y : ℝ) / (denominator x : ℝ)) *
      ((certificateNum epi y : ℝ) / (certificateDen epi : ℝ))) =
      (certificateNum epi x : ℝ) / (certificateDen epi : ℝ)
    simp_rw [div_mul_div_comm, ← Nat.cast_mul]
    rw [← sum_div, nat_sum_cast, hharm x]
    push_cast
    field_simp [Dne, Lne]

theorem boundary_absorbing (epi : Bool) : Absorbing (kernel epi) boundary := by
  obtain ⟨hL,hR,hD,hrow,hbounds,hwin,hloss,hharm,hterm,hclosedW,hclosedL,rest⟩ :=
    integer_facts epi
  constructor
  · intro x y hx hy
    change (numerator epi false x y : ℝ) / _ = 0
    rw [hclosedW x y hx hy, Nat.cast_zero, zero_div]
  · intro x y hx hy
    change (numerator epi false x y : ℝ) / _ = 0
    rw [hclosedL x y hx hy, Nat.cast_zero, zero_div]

private theorem terminal_iff (x : State) : boundary.Terminal x ↔ terminal x = true := by
  simp [Boundary.Terminal, boundary, terminal, Bool.or_eq_true]

theorem uniform_terminal (epi : Bool) :
    UniformTerminal (kernel epi) boundary (1/100) := by
  obtain ⟨hL,hR,hD,hrow,hbounds,hwin,hloss,hharm,hterm,rest⟩ := integer_facts epi
  intro x
  have Dpos : 0 < (denominator x : ℝ) := by exact_mod_cast hD x
  have hc : (denominator x : ℝ) ≤
      100 * ((∑ y : State, if terminal y then numerator epi false x y else 0 : ℕ) : ℝ) := by
    exact_mod_cast hterm x
  have he : backward (kernel epi) (indicator boundary.Terminal) x =
      ((∑ y : State, if terminal y then numerator epi false x y else 0 : ℕ) : ℝ) /
        (denominator x : ℝ) := by
    unfold backward
    rw [← nat_sum_cast, sum_div]
    apply Finset.sum_congr rfl
    intro y _
    by_cases hy : terminal y = true
    · have hb : boundary.Terminal y := (terminal_iff y).2 hy
      simp [kernel, indicator, hy, hb]
    · have hb : ¬ boundary.Terminal y := fun h => hy ((terminal_iff y).1 h)
      simp [kernel, indicator, hy, hb]
  rw [he]
  apply (le_div_iff₀ Dpos).2
  linarith

def pulse (epi : Bool) (x : State) : ℝ :=
  (numerator epi true 54 x : ℝ) / (denominator 54 : ℝ)
theorem pulse_nonneg (epi : Bool) (x : State) : 0 ≤ pulse epi x :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
theorem pulse_total (epi : Bool) : ∑ x : State, pulse epi x = 1 := by
  obtain ⟨hL,hR,hD,hrow,hbounds,hwin,hloss,hharm,hterm,hclosedW,hclosedL,hpulse,rest⟩ :=
    integer_facts epi
  unfold pulse
  rw [← sum_div, nat_sum_cast, hpulse]
  exact div_self (by norm_num [denominator, gameteDen, fitness, genotype, eCount])

def fixationValue (epi : Bool) : ℝ := (resultNum epi : ℝ) / (resultDen epi : ℝ)
theorem pulse_certificate_value (epi : Bool) :
    expect (pulse epi) (certificate epi) = fixationValue epi := by
  obtain ⟨hL,hR,hD,hrow,hbounds,hwin,hloss,hharm,hterm,hclosedW,hclosedL,hpulse,hvalue⟩ :=
    integer_facts epi
  have Lpos : 0 < (certificateDen epi : ℝ) := by exact_mod_cast hL
  have Rpos : 0 < (resultDen epi : ℝ) := by exact_mod_cast hR
  have Dpos : 0 < (denominator 54 : ℝ) := by
    norm_num [denominator, gameteDen, fitness, genotype, eCount]
  have hc : ((∑ x : State, numerator epi true 54 x * certificateNum epi x : ℕ) : ℝ) *
      (resultDen epi : ℝ) = (resultNum epi : ℝ) * (denominator 54 : ℝ) *
        (certificateDen epi : ℝ) := by exact_mod_cast hvalue
  unfold expect pulse certificate fixationValue
  simp_rw [div_mul_div_comm, ← Nat.cast_mul]
  rw [← sum_div, nat_sum_cast, Nat.cast_mul]
  apply (div_eq_div_iff (ne_of_gt (mul_pos Dpos Lpos)) (ne_of_gt Rpos)).2
  exact hc.trans (mul_assoc _ _ _)

def reproductiveIsolation (epi : Bool) : ℝ := 1 - 8 * fixationValue epi
theorem genetic_result : reproductiveIsolation false = 937945083 / 2233177303 := by
  norm_num [reproductiveIsolation, fixationValue, resultNum, resultDen]
theorem epigenetic_result : reproductiveIsolation true = 3/7 := by
  norm_num [reproductiveIsolation, fixationValue, resultNum, resultDen]
theorem epigenetic_advantage :
    reproductiveIsolation true - reproductiveIsolation false = 19130904/2233177303 := by
  rw [genetic_result, epigenetic_result]
  norm_num
theorem epigenetic_strictly_greater :
    reproductiveIsolation false < reproductiveIsolation true := by
  rw [genetic_result, epigenetic_result]
  norm_num

theorem fixation_probability_error (epi : Bool) (n : ℕ) :
    |winProbabilityFrom (kernel epi) boundary (pulse epi) n - fixationValue epi| ≤
      (99/100)^n := by
  have h := win_probability_from_error (kernel epi) boundary
    (boundary_absorbing epi) (by norm_num : (1:ℝ)/100 ≤ 1)
    (uniform_terminal epi) (certificate_valid epi) (pulse epi)
    (pulse_nonneg epi) (pulse_total epi) n
  rw [pulse_certificate_value] at h
  convert h using 1 <;> norm_num

theorem fixation_probability_limit (epi : Bool) :
    ∀ δ : ℝ, 0 < δ → ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      |winProbabilityFrom (kernel epi) boundary (pulse epi) n - fixationValue epi| < δ := by
  have h := certificate_identifies_mixture_limit (kernel epi) boundary
    (boundary_absorbing epi) (by norm_num : (0:ℝ) < 1/100)
    (by norm_num : (1:ℝ)/100 ≤ 1) (uniform_terminal epi)
    (certificate_valid epi) (pulse epi) (pulse_nonneg epi) (pulse_total epi)
  simpa only [pulse_certificate_value] using h

#print axioms fixation_probability_error
#print axioms fixation_probability_limit
#print axioms integer_facts
#print axioms certificate_valid
#print axioms boundary_absorbing
#print axioms uniform_terminal
#print axioms pulse_total
#print axioms pulse_certificate_value
#print axioms epigenetic_advantage
#print axioms epigenetic_strictly_greater
end
end FiniteEpigenetic
