import SamuelAlexanderResearch.FullHeight

/-!
Universal digit algebra for the proved matching-height formula. The final
endpoints compose the independent actual-trajectory theorem with the integer
recurrence and its executable evaluator. Sampled transitions are not premises.
-/

namespace DigitRecurrence

open ThueMorseBits
open FullHeight

theorem odd_times_power (m : Nat) (hm : 0 < m) :
    ∃ h r, m = (2 * h + 1) * 2 ^ r := by
  induction m using Nat.strongRecOn with
  | ind m ih =>
    by_cases hodd : m % 2 = 1
    · exact ⟨m / 2, 0, by simp; omega⟩
    · have hhalf : 0 < m / 2 := by omega
      have hsmall : m / 2 < m := by omega
      obtain ⟨h, r, hr⟩ := ih (m / 2) hsmall hhalf
      refine ⟨h, r + 1, ?_⟩
      calc
        m = 2 * (m / 2) := by omega
        _ = (2 * h + 1) * 2 ^ (r + 1) := by
          rw [hr, Nat.pow_succ]
          simp only [Nat.mul_comm, Nat.mul_left_comm]

theorem t_four (n : Nat) : t (4 * n) = t n := by
  have h : 4 * n = 2 * (2 * n) := by omega
  rw [h, t_double, t_double]

theorem t_four_add_one (n : Nat) : t (4 * n + 1) = !(t n) := by
  have h : 4 * n + 1 = 2 * (2 * n) + 1 := by omega
  rw [h, t_double_add_one, t_double]

theorem t_four_add_two (n : Nat) : t (4 * n + 2) = !(t n) := by
  have h : 4 * n + 2 = 2 * (2 * n + 1) := by omega
  rw [h, t_double, t_double_add_one]

theorem t_four_add_three (n : Nat) : t (4 * n + 3) = t n := by
  have h : 4 * n + 3 = 2 * (2 * n + 1) + 1 := by omega
  rw [h, t_double_add_one, t_double_add_one]
  simp

theorem t_scaled_minus_one (h r : Nat) :
    t ((2 * h + 1) * 2 ^ r - 1) =
      if r % 2 = 0 then t h else !(t h) := by
  induction r with
  | zero =>
    have hindex : (2 * h + 1) * 2 ^ 0 - 1 = 2 * h := by omega
    simp only [hindex, t_double, Nat.zero_mod, ↓reduceIte]
  | succ r ih =>
    have hp : 0 < 2 ^ r := by have := index_lt_two_pow r; omega
    have hm : 0 < (2 * h + 1) * 2 ^ r := Nat.mul_pos (by omega) hp
    have hindex : (2 * h + 1) * 2 ^ (r + 1) - 1 =
        2 * ((2 * h + 1) * 2 ^ r - 1) + 1 := by
      rw [Nat.pow_succ, ← Nat.mul_assoc]
      omega
    rw [hindex, t_double_add_one, ih]
    by_cases heven : r % 2 = 0
    · have hodd : (r+1) % 2 ≠ 0 := by omega
      simp [heven, hodd]
    · have hnext : (r+1) % 2 = 0 := by omega
      simp [heven, hnext]

theorem t_scaled (h r : Nat) :
    t ((2 * h + 1) * 2 ^ r) = !(t h) := by
  rw [t_mul_two_pow, t_double_add_one]

def bitInt (b : Bool) : Int := if b then 1 else 0

/-- The ten integer coordinates in the proposed digit recurrence. -/
structure State where
  one : Int
  T : Int
  U : Int
  V : Int
  L : Int
  E : Int
  O : Int
  X : Int
  F : Int
  C : Int
  deriving DecidableEq, Repr

def coordinates (H : Nat → Nat) (n : Nat) : State where
  one := 1
  T := bitInt (t n)
  U := bitInt (t (n+1))
  V := bitInt (t n) * bitInt (t (n+1))
  L := H n
  E := H (2*n)
  O := H (2*n+1)
  X := ((H (4*n+1) : Int) - bitInt (t n)) / 2
  F := H (4*n+2)
  C := H (4*n+3)

def evenStep (z : State) : State where
  one := z.one
  T := z.T
  U := z.one - z.T
  V := 0
  L := z.E
  E := 3*z.one - 2*z.T - 2*z.U + 2*z.V
  O := 2*z.X + z.T
  X := z.T
  F := 7*z.one - 7*z.T - 2*z.U + 2*z.V
  C := 5*z.X + 2*z.T - 3*z.V

def oddStep (z : State) : State where
  one := z.one
  T := z.one - z.T
  U := z.U
  V := z.U - z.V
  L := z.O
  E := z.F
  O := z.C
  X := 3*z.U - 12*z.V - 2*z.E + 2*z.X + z.F
  F := z.T + 3*z.U + 15*z.V + 4*z.E - 4*z.X
  C := 3*z.C - 2*z.O

theorem State.ext {a b : State}
    (hone : a.one = b.one) (hT : a.T = b.T) (hU : a.U = b.U)
    (hV : a.V = b.V) (hL : a.L = b.L) (hE : a.E = b.E)
    (hO : a.O = b.O) (hX : a.X = b.X) (hF : a.F = b.F)
    (hC : a.C = b.C) : a = b := by
  cases a
  cases b
  simp_all

theorem special_even (n : Nat) : special (2*n) = false := by
  have hm : (2*n) % 4 ≠ 1 := by omega
  simp [special, hm]

theorem special_four_add_one (n : Nat) :
    special (4*n+1) = (!(t n) && t (n+1)) := by
  have hm : (4*n+1) % 4 = 1 := by omega
  have hd : (4*n+1) / 4 = n := by omega
  simp [special, hm, hd]

theorem special_four_add_three (n : Nat) : special (4*n+3) = false := by
  have hm : (4*n+3) % 4 = 3 := by omega
  simp [special, hm]

theorem scaled_mod_four (h r : Nat) (hr : 2 ≤ r) :
    ((2*h+1)*2^r-1) % 4 = 3 := by
  obtain ⟨j, rfl⟩ : ∃ j, r = j+2 := ⟨r-2, by omega⟩
  have hp : 0 < 2^j := by have := index_lt_two_pow j; omega
  have hm : 0 < (2*h+1)*2^j := Nat.mul_pos (by omega) hp
  have he : (2*h+1)*2^(j+2) = 4*((2*h+1)*2^j) := by
    simp only [Nat.pow_add, Nat.reducePow]
    simp only [Nat.mul_comm, Nat.mul_assoc]
  rw [he]
  omega

theorem factor_even {H : Nat → Nat} (spec : FormulaSpec H)
    (n h r : Nat) (hn : n+1 = (2*h+1)*2^r) : H (2*n) = evenValue h r := by
  have he : (4*h+2)*2^r-2 = 2*n := by
    have hc : 4*h+2 = 2*(2*h+1) := by omega
    rw [hc, Nat.mul_assoc, ← hn]
    omega
  simpa only [he] using (spec.2 h r).1

theorem factor_odd {H : Nat → Nat} (spec : FormulaSpec H)
    (n h r : Nat) (hn : n+1 = (2*h+1)*2^r) : H (2*n+1) = oddValue h r := by
  have he : (4*h+2)*2^r-1 = 2*n+1 := by
    have hc : 4*h+2 = 2*(2*h+1) := by omega
    rw [hc, Nat.mul_assoc, ← hn]
    omega
  simpa only [he] using (spec.2 h r).2

theorem factor_next (n h r : Nat) (hn : n+1 = (2*h+1)*2^r) :
    (2*n+1)+1 = (2*h+1)*2^(r+1) := by
  rw [Nat.pow_succ, ← Nat.mul_assoc, ← hn]
  omega

def smallX (n : Nat) : Int :=
  if t n then if t (n+1) then if special n then 6 else 4 else 1 else 0

theorem height_four_even {H : Nat → Nat} (spec : FormulaSpec H) (n : Nat) :
    H (4*n) = evenValue n 0 := by
  have h := (spec.2 n 0).1
  have he : (4*n+2)*2^0-2 = 4*n := by omega
  simpa only [he] using h

theorem height_four_odd {H : Nat → Nat} (spec : FormulaSpec H) (n : Nat) :
    H (4*n+1) = oddValue n 0 := by
  have h := (spec.2 n 0).2
  have he : (4*n+2)*2^0-1 = 4*n+1 := by omega
  simpa only [he] using h

theorem coordinate_X {H : Nat → Nat} (spec : FormulaSpec H) (n : Nat) :
    (coordinates H n).X = smallX n := by
  simp only [coordinates, height_four_odd spec]
  cases ht : t n <;> cases hu : t (n+1) <;> cases ha : special n <;>
    simp [oddValue, smallX, bitInt, ht, hu, ha]

theorem X_integral {H : Nat → Nat} (spec : FormulaSpec H) (n : Nat) :
    (H (4*n+1) : Int) = 2 * (coordinates H n).X + bitInt (t n) := by
  rw [height_four_odd spec, coordinate_X spec]
  cases ht : t n <;> cases hu : t (n+1) <;> cases ha : special n <;>
    simp [oddValue, smallX, bitInt, ht, hu, ha]

theorem even_transition {H : Nat → Nat} (spec : FormulaSpec H) (n : Nat) :
    coordinates H (2*n) = evenStep (coordinates H n) := by
  have hF : H (8*n+2) = evenValue n 1 := by
    have h := (spec.2 n 1).1
    have he : (4*n+2)*2^1-2 = 8*n+2 := by omega
    simpa only [he] using h
  have hC : H (8*n+3) = oddValue n 1 := by
    have h := (spec.2 n 1).2
    have he : (4*n+2)*2^1-1 = 8*n+3 := by omega
    simpa only [he] using h
  apply State.ext
  · rfl
  · simp only [coordinates, evenStep, t_double]
  · simp only [coordinates, evenStep, t_double_add_one]
    cases t n <;> rfl
  · simp only [coordinates, evenStep, t_double, t_double_add_one]
    cases t n <;> rfl
  · rfl
  · change (H (2*(2*n)) : Int) = _
    have he : 2*(2*n) = 4*n := by omega
    rw [he, height_four_even spec]
    cases ht : t n <;> cases hu : t (n+1) <;>
      simp [evenValue, evenStep, coordinates, bitInt, bit, ht, hu]
  · change (H (2*(2*n)+1) : Int) = _
    have he : 2*(2*n)+1 = 4*n+1 := by omega
    simpa only [he, evenStep, coordinates] using X_integral spec n
  · rw [coordinate_X spec]
    simp only [smallX, t_double, t_double_add_one, evenStep, coordinates]
    cases t n <;> simp [bitInt]
  · change (H (4*(2*n)+2) : Int) = _
    have he : 4*(2*n)+2 = 8*n+2 := by omega
    rw [he, hF]
    cases ht : t n <;> cases hu : t (n+1) <;>
      simp [evenValue, evenStep, coordinates, bitInt, bit, ht, hu]
  · change (H (4*(2*n)+3) : Int) = _
    have he : 4*(2*n)+3 = 8*n+3 := by omega
    rw [he, hC]
    change (oddValue n 1 : Int) = 5*(coordinates H n).X +
      2*bitInt (t n)-3*(bitInt (t n)*bitInt (t (n+1)))
    rw [coordinate_X spec]
    cases ht : t n <;> cases hu : t (n+1) <;> cases ha : special n <;>
      simp [oddValue, smallX, bitInt, ht, hu, ha]

theorem smallX_odd (n : Nat) :
    smallX (2*n+1) = if t n then 0 else
      if t (n+1) then if special (2*n+1) then 6 else 4 else 1 := by
  have he : 2*n+1+1 = 2*(n+1) := by omega
  simp only [smallX, he, t_double_add_one, t_double]
  cases t n <;> simp

theorem oddValue_scale (h r : Nat) :
    (oddValue h (r+2) : Int) =
      3*(oddValue h (r+1) : Int) - 2*(oddValue h r : Int) := by
  have hp : 0 < 2^r := by have := index_lt_two_pow r; omega
  cases ht : t h <;> cases hu : t (h+1) <;> cases ha : special h <;>
    simp [oddValue, ht, hu, ha, Nat.pow_succ] <;> omega

/-- The only two nontrivial odd-digit rows, proved by the exhaustive
valuation cases zero, one, and at least two. -/
theorem odd_auxiliary (n h r : Nat) (hn : n+1 = (2*h+1)*2^r) :
    smallX (2*n+1) = 3*bitInt (t (n+1)) -
      12*(bitInt (t n)*bitInt (t (n+1))) -
      2*(evenValue h r : Int) + 2*smallX n + (evenValue h (r+1) : Int) ∧
    (evenValue h (r+2) : Int) = bitInt (t n) + 3*bitInt (t (n+1)) +
      15*(bitInt (t n)*bitInt (t (n+1))) + 4*(evenValue h r : Int) - 4*smallX n := by
  rw [smallX_odd]
  by_cases hr0 : r = 0
  · subst r
    have hn' : n = 2*h := by simpa using hn
    subst n
    have he : 2*(2*h)+1 = 4*h+1 := by omega
    cases hb : t h <;> cases hd : t (h+1) <;>
      simp [smallX, evenValue, bitInt, bit, t_double, t_double_add_one,
        he, special_four_add_one, hb, hd]
  · by_cases hr1 : r = 1
    · subst r
      have hn' : n = 4*h+1 := by simp only [Nat.pow_one, Nat.add_mul] at hn; omega
      subst n
      have he' : 4*h+1+1 = 4*h+2 := by omega
      cases hb : t h <;> cases hd : t (h+1) <;>
        simp [smallX, evenValue, bitInt, bit, he', special_four_add_one, hb, hd]
    · have hr : 2 ≤ r := by omega
      have hindex : n = (2*h+1)*2^r-1 := by omega
      have hT : t n = if r%2 = 0 then t h else !(t h) := by
        rw [hindex]
        exact t_scaled_minus_one h r
      have hU : t (n+1) = !(t h) := by rw [hn, t_scaled]
      have hmod : n % 4 = 3 := by rw [hindex]; exact scaled_mod_four h r hr
      have hAn : special n = false := by simp [special, hmod]
      have hmod' : (2*n+1)%4 = 3 := by omega
      have hAodd : special (2*n+1) = false := by simp [special, hmod']
      have hrafter : r+2 ≠ 1 := by omega
      have hp : 0 < 2^r := by have := index_lt_two_pow r; omega
      by_cases heven : r%2 = 0
      · have hnext : (r+1)%2 = 1 := by omega
        have hafter : (r+2)%2 = 0 := by omega
        cases hb : t h <;> cases hd : t (h+1) <;>
          simp [smallX, hT, hU, hAodd, heven, hnext, hafter,
            evenValue, bit, bitInt, hr0, hr1, hrafter, hb, hd, Nat.pow_succ] <;> omega
      · have hmodtwo : r%2 = 1 := by omega
        have hnext : (r+1)%2 = 0 := by omega
        have hafter : (r+2)%2 = 1 := by omega
        cases hb : t h <;> cases hd : t (h+1) <;>
          simp [smallX, hT, hU, hAn, hmodtwo, hnext, hafter,
            evenValue, bit, bitInt, hr0, hr1, hrafter, hb, hd, Nat.pow_succ] <;> omega

theorem odd_transition {H : Nat → Nat} (spec : FormulaSpec H) (n : Nat) :
    coordinates H (2*n+1) = oddStep (coordinates H n) := by
  obtain ⟨h, r, hn⟩ := odd_times_power (n+1) (by omega)
  have hn' := factor_next n h r hn
  have hn'' : (4*n+3)+1 = (2*h+1)*2^(r+2) := by
    have hh := factor_next (2*n+1) h (r+1) hn'
    have he : 2*(2*n+1)+1+1 = (4*n+3)+1 := by omega
    simpa only [he, Nat.add_assoc] using hh
  have hE := factor_even spec n h r hn
  have hO := factor_odd spec n h r hn
  have hF : H (4*n+2) = evenValue h (r+1) := by
    have hh := factor_even spec (2*n+1) h (r+1) hn'
    have he : 2*(2*n+1) = 4*n+2 := by omega
    simpa only [he] using hh
  have hC : H (4*n+3) = oddValue h (r+1) := by
    have hh := factor_odd spec (2*n+1) h (r+1) hn'
    have he : 2*(2*n+1)+1 = 4*n+3 := by omega
    simpa only [he] using hh
  have hF' : H (8*n+6) = evenValue h (r+2) := by
    have hh := factor_even spec (4*n+3) h (r+2) hn''
    have he : 2*(4*n+3) = 8*n+6 := by omega
    simpa only [he] using hh
  have hC' : H (8*n+7) = oddValue h (r+2) := by
    have hh := factor_odd spec (4*n+3) h (r+2) hn''
    have he : 2*(4*n+3)+1 = 8*n+7 := by omega
    simpa only [he] using hh
  have hbits : t (2*n+1+1) = t (n+1) := by
    have he : 2*n+1+1 = 2*(n+1) := by omega
    rw [he, t_double]
  apply State.ext
  · rfl
  · simp only [coordinates, oddStep, t_double_add_one]
    cases t n <;> rfl
  · simp only [coordinates, oddStep, hbits]
  · simp only [coordinates, oddStep, t_double_add_one, hbits]
    cases t n <;> cases t (n+1) <;> rfl
  · rfl
  · change (H (2*(2*n+1)) : Int) = H (4*n+2)
    have he : 2*(2*n+1) = 4*n+2 := by omega
    rw [he]
  · change (H (2*(2*n+1)+1) : Int) = H (4*n+3)
    have he : 2*(2*n+1)+1 = 4*n+3 := by omega
    rw [he]
  · change (coordinates H (2*n+1)).X = 3*bitInt (t (n+1)) -
      12*(bitInt (t n)*bitInt (t (n+1))) - 2*(H (2*n) : Int) +
      2*(coordinates H n).X + (H (4*n+2) : Int)
    rw [coordinate_X spec, coordinate_X spec, hE, hF]
    exact (odd_auxiliary n h r hn).1
  · change (H (4*(2*n+1)+2) : Int) = bitInt (t n) + 3*bitInt (t (n+1)) +
      15*(bitInt (t n)*bitInt (t (n+1))) + 4*(H (2*n) : Int) -
      4*(coordinates H n).X
    have he : 4*(2*n+1)+2 = 8*n+6 := by omega
    rw [he, hF', hE, coordinate_X spec]
    exact (odd_auxiliary n h r hn).2
  · change (H (4*(2*n+1)+3) : Int) = 3*(H (4*n+3) : Int) - 2*(H (2*n+1) : Int)
    have he : 4*(2*n+1)+3 = 8*n+7 := by omega
    rw [he, hC', hC, hO]
    exact oddValue_scale h r

def initial : State := ⟨1, 0, 1, 0, 1, 1, 0, 0, 5, 0⟩

theorem initial_coordinates {H : Nat → Nat} (spec : FormulaSpec H) :
    coordinates H 0 = initial := by
  have h1 : H 1 = 0 := by simpa [oddValue] using (spec.2 0 0).2
  have h2 : H 2 = 5 := by simpa [evenValue, bit] using (spec.2 0 1).1
  have h3 : H 3 = 0 := by simpa [oddValue] using (spec.2 0 1).2
  simp [coordinates, initial, spec.1, h1, h2, h3, bitInt]

theorem X_values {H : Nat → Nat} (spec : FormulaSpec H) (n : Nat) :
    (coordinates H n).X = 0 ∨ (coordinates H n).X = 1 ∨
      (coordinates H n).X = 4 ∨ (coordinates H n).X = 6 := by
  rw [coordinate_X spec]
  cases ht : t n <;> cases hu : t (n+1) <;> cases ha : special n <;>
    simp [smallX, ht, hu, ha]

/-- The complete initial vector and both ten-coordinate transition rules. -/
theorem digit_recurrence_of_formula {H : Nat → Nat} (spec : FormulaSpec H) :
    coordinates H 0 = initial ∧
    ∀ n, coordinates H (2*n) = evenStep (coordinates H n) ∧
      coordinates H (2*n+1) = oddStep (coordinates H n) :=
  ⟨initial_coordinates spec, fun n => ⟨even_transition spec n, odd_transition spec n⟩⟩

/-- A terminating evaluator that recursively removes one binary digit and
applies the corresponding proved integer transition. -/
def evaluate (n : Nat) : State :=
  if n = 0 then initial
  else if n % 2 = 0 then evenStep (evaluate (n/2)) else oddStep (evaluate (n/2))
termination_by n
decreasing_by all_goals omega

theorem evaluate_eq_of_formula {H : Nat → Nat} (spec : FormulaSpec H) (n : Nat) :
    evaluate n = coordinates H n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hz : n = 0
    · subst n
      rw [evaluate, if_pos rfl]
      exact (initial_coordinates spec).symm
    · have hsmall : n/2 < n := by omega
      rw [evaluate, if_neg hz, ih (n/2) hsmall]
      by_cases heven : n%2 = 0
      · rw [if_pos heven]
        have hindex : n = 2*(n/2) := by omega
        exact (even_transition spec (n/2)).symm.trans (congrArg (coordinates H) hindex.symm)
      · rw [if_neg heven]
        have hindex : n = 2*(n/2)+1 := by omega
        exact (odd_transition spec (n/2)).symm.trans (congrArg (coordinates H) hindex.symm)

theorem evaluate_height_of_formula {H : Nat → Nat} (spec : FormulaSpec H) (n : Nat) :
    (evaluate n).L = (H n : Int) := by
  rw [evaluate_eq_of_formula spec]
  rfl

theorem formula_unique {H K : Nat → Nat} (hH : FormulaSpec H) (hK : FormulaSpec K) : H = K := by
  funext n
  have he : (H n : Int) = K n :=
    (evaluate_height_of_formula hH n).symm.trans (evaluate_height_of_formula hK n)
  omega

/-- Unconditional recurrence for the actual attained graph maxima. -/
theorem actual_digit_recurrence :
    coordinates FullHeight.height 0 = initial ∧
    ∀ n, coordinates FullHeight.height (2*n) = evenStep (coordinates FullHeight.height n) ∧
      coordinates FullHeight.height (2*n+1) = oddStep (coordinates FullHeight.height n) :=
  digit_recurrence_of_formula FullHeight.height_formula

theorem evaluate_actual_height (n : Nat) :
    (evaluate n).L = (FullHeight.height n : Int) :=
  evaluate_height_of_formula FullHeight.height_formula n

/-- The computed integer coordinate, converted to Nat, is an attained maximum
of actual own-target matching paths; the endpoint has no formula premise. -/
theorem evaluate_isMaximum (n : Nat) :
    FiniteEditStability.IsMaximumPrefix ThueMorseBits.t n (evaluate n).L.toNat := by
  rw [evaluate_actual_height]
  exact FullHeight.height_isMaximum n

end DigitRecurrence

#print axioms DigitRecurrence.X_integral
#print axioms DigitRecurrence.even_transition
#print axioms DigitRecurrence.odd_transition
#print axioms DigitRecurrence.digit_recurrence_of_formula
#print axioms DigitRecurrence.evaluate_eq_of_formula
#print axioms DigitRecurrence.formula_unique
#print axioms DigitRecurrence.actual_digit_recurrence
#print axioms DigitRecurrence.evaluate_actual_height
#print axioms DigitRecurrence.evaluate_isMaximum
