import Std

/-!
# Actual Boolean Thue-Morse bits

`t` recursively deletes the least significant binary digit. A zero digit
preserves parity and a one digit flips it; the empty binary expansion has
parity false. This defines the actual binary digit parity sequence, not an
abstract sequence postulated to satisfy recurrences.
-/

namespace ThueMorseBits

def t (n : Nat) : Bool :=
  if n = 0 then false
  else if n % 2 = 0 then t (n / 2) else !(t (n / 2))
termination_by n
decreasing_by all_goals omega

@[simp] theorem t_zero : t 0 = false := by
  rw [t]
  decide

theorem t_double (n : Nat) : t (2 * n) = t n := by
  by_cases hn : n = 0
  · simp [hn]
  · rw [t]
    have hz : 2 * n ≠ 0 := by omega
    have hm : (2 * n) % 2 = 0 := by omega
    have hd : (2 * n) / 2 = n := by omega
    simp only [hz, hm, hd, ↓reduceIte]

theorem t_double_add_one (n : Nat) : t (2 * n + 1) = !(t n) := by
  rw [t]
  have hz : 2 * n + 1 ≠ 0 := by omega
  have hm : (2 * n + 1) % 2 ≠ 0 := by omega
  have hd : (2 * n + 1) / 2 = n := by omega
  simp only [hz, hm, hd, ↓reduceIte]

@[simp] theorem t_one : t 1 = true := by
  have h := t_double_add_one 0
  simpa using h

/-- Concatenating binary blocks adds their digit parities by xor. -/
theorem t_dyadic_block (a n b : Nat) (hb : b < 2 ^ n) :
    t (a * 2 ^ n + b) = Bool.xor (t a) (t b) := by
  induction n generalizing b with
  | zero =>
    have hb0 : b = 0 := by simpa using hb
    simp [hb0]
  | succ n ih =>
    have hbound : b / 2 < 2 ^ n := by
      rw [Nat.pow_succ] at hb
      omega
    have hsplit : a * 2 ^ (n + 1) + b =
        2 * (a * 2 ^ n + b / 2) + b % 2 := by
      rw [Nat.pow_succ, ← Nat.mul_assoc]
      omega
    by_cases hparity : b % 2 = 0
    · have hbhalf : b = 2 * (b / 2) := by omega
      have hwhole : a * 2 ^ (n + 1) + b = 2 * (a * 2 ^ n + b / 2) := by omega
      rw [hwhole, t_double, ih (b / 2) hbound]
      have ht : t b = t (b / 2) := by
        calc
          t b = t (2 * (b / 2)) := congrArg t hbhalf
          _ = t (b / 2) := t_double _
      rw [ht]
    · have hbhalf : b = 2 * (b / 2) + 1 := by omega
      have hwhole : a * 2 ^ (n + 1) + b = 2 * (a * 2 ^ n + b / 2) + 1 := by omega
      rw [hwhole, t_double_add_one, ih (b / 2) hbound]
      have ht : t b = !(t (b / 2)) := by
        calc
          t b = t (2 * (b / 2) + 1) := congrArg t hbhalf
          _ = !(t (b / 2)) := t_double_add_one _
      rw [ht]
      cases t a <;> cases t (b / 2) <;> rfl

theorem index_lt_two_pow (n : Nat) : n < 2 ^ n := by
  induction n with
  | zero => decide
  | succ n ih => rw [Nat.pow_succ]; omega

theorem t_mul_two_pow (a n : Nat) : t (a * 2 ^ n) = t a := by
  have h := t_dyadic_block a n 0 (by have := index_lt_two_pow n; omega)
  simpa using h

@[simp] theorem t_two_pow (n : Nat) : t (2 ^ n) = true := by
  have h := t_mul_two_pow 1 n
  simpa using h

/-- Adjacent parity change at the last four entries of a sufficiently large
dyadic block. The trajectory API uses the convenient hypothesis `3 <= n`. -/
theorem t_power_sub_three (n : Nat) (hn : 3 <= n) :
    t (2 ^ n - 3) = !(t (2 ^ n - 4)) := by
  obtain ⟨m, hm⟩ : exists m, n = m + 1 := ⟨n - 1, by omega⟩
  subst n
  have hpow : 2 <= 2 ^ m := by have := index_lt_two_pow m; omega
  have hthree : 2 ^ (m + 1) - 3 = 2 * (2 ^ m - 2) + 1 := by
    rw [Nat.pow_succ]
    omega
  have hfour : 2 ^ (m + 1) - 4 = 2 * (2 ^ m - 2) := by
    rw [Nat.pow_succ]
    omega
  rw [hthree, hfour, t_double_add_one, t_double]

theorem t_power_sub_two (n : Nat) (hn : 3 <= n) :
    t (2 ^ n - 2) = t (2 ^ n - 3) := by
  obtain ⟨m, hm⟩ : exists m, n = m + 2 := ⟨n - 2, by omega⟩
  subst n
  have hpos : 0 < 2 ^ m := by have := index_lt_two_pow m; omega
  have hpow : 2 ^ (m + 2) = 4 * 2 ^ m := by
    simp only [Nat.pow_succ]
    omega
  have htwo : 2 ^ (m + 2) - 2 = 2 * (2 * (2 ^ m - 1) + 1) := by omega
  have hthree : 2 ^ (m + 2) - 3 = 2 * (2 * (2 ^ m - 1)) + 1 := by omega
  rw [htwo, hthree, t_double, t_double_add_one, t_double_add_one, t_double]

theorem t_twice_power_sub_four (n : Nat) (hn : 3 <= n) :
    t (2 * 2 ^ n - 4) = t (2 ^ n - 3) := by
  have hpos : 2 <= 2 ^ n := by have := index_lt_two_pow n; omega
  have heq : 2 * 2 ^ n - 4 = 2 * (2 ^ n - 2) := by omega
  rw [heq, t_double]
  exact t_power_sub_two n hn

@[simp] theorem t_two : t 2 = true := by simpa using t_double 1
@[simp] theorem t_three : t 3 = false := by simpa using t_double_add_one 1
@[simp] theorem t_four : t 4 = true := by simpa using t_double 2
@[simp] theorem t_five : t 5 = false := by simpa using t_double_add_one 2
@[simp] theorem t_six : t 6 = false := by simpa using t_double 3
@[simp] theorem t_seven : t 7 = true := by simpa using t_double_add_one 3
@[simp] theorem t_eight : t 8 = true := by simpa using t_double 4
@[simp] theorem t_nine : t 9 = false := by simpa using t_double_add_one 4
@[simp] theorem t_ten : t 10 = false := by simpa using t_double 5
@[simp] theorem t_eleven : t 11 = true := by simpa using t_double_add_one 5
@[simp] theorem t_twelve : t 12 = false := by simpa using t_double 6
@[simp] theorem t_thirteen : t 13 = true := by simpa using t_double_add_one 6

theorem t_ten_pow_add_one (n : Nat) : t (10 * 2 ^ n + 1) = true := by
  by_cases hn : n = 0
  · simp [hn]
  · have hb : 1 < 2 ^ n := by have := index_lt_two_pow n; omega
    have h := t_dyadic_block 10 n 1 hb
    simpa using h

end ThueMorseBits

#print axioms ThueMorseBits.t_zero
#print axioms ThueMorseBits.t_double
#print axioms ThueMorseBits.t_double_add_one
#print axioms ThueMorseBits.t_dyadic_block
#print axioms ThueMorseBits.t_power_sub_three
#print axioms ThueMorseBits.t_power_sub_two
#print axioms ThueMorseBits.t_twice_power_sub_four
#print axioms ThueMorseBits.t_ten_pow_add_one
