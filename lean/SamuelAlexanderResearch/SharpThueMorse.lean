import SamuelAlexanderResearch.ThueMorseBound
import SamuelAlexanderResearch.ThueMorseBits
import SamuelAlexanderResearch.BinaryAvoidance

/-!
Complete sharp Thue--Morse path bounds from exact dyadic trajectories.
The graph and frontier semantics come from ThueMorseBound; auxiliary boundary
trajectories are not assumed to be actual matching paths. The endpoints prove
the universal 8/3 bound, existence of finite maxima, and the exact equality
family, using the actual recursively defined ThueMorseBits.t.
-/

namespace SharpThueMorse
open SamuelAlexanderResearch.ThueMorseBound

/-- A checked run of advances of one, beginning at an arbitrary time. -/
theorem run_ones (color target : Nat → Bool) (v k x len : Nat)
    (hstart : trajectory color target v k = x)
    (hbits : ∀ i, i < len → color (x + i + 1) = target (k + i)) :
    trajectory color target v (k + len) = x + len := by
  induction len with
  | zero => simpa using hstart
  | succ len ih =>
    have hprev := ih (fun i hi => hbits i (by omega))
    have hbit := hbits len (by omega)
    change boundary color (target (k + len)) (trajectory color target v (k + len)) = x + (len + 1)
    rw [hprev]
    simp only [boundary, if_pos hbit]
    omega

/-- A checked run of advances of two. -/
theorem run_twos (color target : Nat → Bool) (v k x len : Nat)
    (hstart : trajectory color target v k = x)
    (hbits : ∀ i, i < len → color (x + 2 * i + 1) ≠ target (k + i)) :
    trajectory color target v (k + len) = x + 2 * len := by
  induction len with
  | zero => simpa using hstart
  | succ len ih =>
    have hprev := ih (fun i hi => hbits i (by omega))
    have hbit := hbits len (by omega)
    change boundary color (target (k + len)) (trajectory color target v (k + len)) = x + 2 * (len + 1)
    rw [hprev]
    simp [boundary, hbit]
    omega

/-- Dyadic intervals `[3*2^n,6*2^n)` cover all natural numbers at least three. -/
theorem exists_dyadic_interval (v : Nat) (hv : 3 ≤ v) :
    ∃ n, 3 * 2^n ≤ v ∧ v < 6 * 2^n := by
  by_cases hs : v < 6
  · exact ⟨0, by simp; omega, by simp; omega⟩
  · obtain ⟨n, hl, hu⟩ := exists_dyadic_interval (v / 2) (by omega)
    refine ⟨n + 1, ?_, ?_⟩ <;> simp only [Nat.pow_succ] <;> omega
termination_by v
decreasing_by omega

open ThueMorseBits

abbrev X (v k : Nat) : Nat := trajectory t t v k

private theorem xor_ne_right (a b c : Bool) (h : a ≠ b) :
    Bool.xor a c ≠ Bool.xor b c := by
  cases a <;> cases b <;> cases c <;> simp_all

/-- Transfer a finite list of high-block agreements to arbitrary dyadic scale. -/
theorem block_eq (n a b count i : Nat)
    (hhigh : ∀ j, j < count → t (a + j) = t (b + j))
    (hi : i < count * 2^n) : t (a * 2^n + i) = t (b * 2^n + i) := by
  have hp := Nat.two_pow_pos n
  have hj : i / 2^n < count := Nat.lt_of_mul_lt_mul_right
    (Nat.lt_of_le_of_lt (Nat.div_mul_le_self i (2^n)) hi)
  have hr := Nat.mod_lt i hp
  have hd := Nat.mod_add_div i (2^n)
  rw [Nat.mul_comm (2^n) (i / 2^n)] at hd
  have ha : a * 2^n + i = (a + i / 2^n) * 2^n + i % 2^n := by
    rw [Nat.add_mul]; omega
  have hb : b * 2^n + i = (b + i / 2^n) * 2^n + i % 2^n := by
    rw [Nat.add_mul]; omega
  rw [ha, hb, t_dyadic_block _ _ _ hr, t_dyadic_block _ _ _ hr, hhigh _ hj]

/-- Transfer high-block mismatches without replacing the actual bit sequence. -/
theorem block_ne (n a b count i : Nat)
    (hhigh : ∀ j, j < count → t (a + j) ≠ t (b + j))
    (hi : i < count * 2^n) : t (a * 2^n + i) ≠ t (b * 2^n + i) := by
  have hp := Nat.two_pow_pos n
  have hj : i / 2^n < count := Nat.lt_of_mul_lt_mul_right
    (Nat.lt_of_le_of_lt (Nat.div_mul_le_self i (2^n)) hi)
  have hr := Nat.mod_lt i hp
  have hd := Nat.mod_add_div i (2^n)
  rw [Nat.mul_comm (2^n) (i / 2^n)] at hd
  have ha : a * 2^n + i = (a + i / 2^n) * 2^n + i % 2^n := by
    rw [Nat.add_mul]; omega
  have hb : b * 2^n + i = (b + i / 2^n) * 2^n + i % 2^n := by
    rw [Nat.add_mul]; omega
  rw [ha, hb, t_dyadic_block _ _ _ hr, t_dyadic_block _ _ _ hr]
  exact xor_ne_right _ _ _ (hhigh _ hj)

theorem baseline (k : Nat) : X 0 k = 2 * k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change boundary t (t k) (X 0 k) = 2 * (k + 1)
    rw [ih]
    have hn : !(t k) ≠ t k := by cases t k <;> decide
    simp [boundary, t_double_add_one]
    omega

/-- The initial upper trajectory consists of `4q` advances of one. -/
theorem upper_join (n : Nat) : X (6 * 2^n - 1) (4 * 2^n) = 10 * 2^n - 1 := by
  have hp := Nat.two_pow_pos n
  have h := run_ones t t (6 * 2^n - 1) 0 (6 * 2^n - 1) (4 * 2^n) rfl (by
    intro i hi
    have he : (6 * 2^n - 1) + i + 1 = 6 * 2^n + i := by omega
    rw [he]
    have hb := block_eq n 6 0 4 i (by
      intro j hj
      have hcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
      rcases hcases with h | h | h | h <;> subst j <;> decide +kernel) hi
    simpa using hb)
  simpa [show (6 * 2^n - 1) + 4 * 2^n = 10 * 2^n - 1 by omega] using h

/-- One exact dyadic descent block: `r` advances of two, then `r` of one. -/
theorem descent_block (n s v A : Nat) (hA : A = 2^(s+3) * 2^n)
    (hstart : X v (A - 4 * 2^n) = 2 * A - 6 * 2^n - 1) :
    X v (A - 2 * 2^n) = 2 * A - 3 * 2^n - 1 := by
  let r := 2^n
  let M := 2^(s+3)
  have hr : 0 < r := Nat.two_pow_pos n
  have hM : 8 ≤ M := Nat.pow_le_pow_right (n := 2) (by decide) (by omega : 3 ≤ s + 3)
  have hAr : 8 * r ≤ A := by
    have h := Nat.mul_le_mul_right r hM
    simpa [M, r, ← hA] using h
  have h3 : (M - 3) * r = A - 3 * r := by rw [Nat.sub_mul]; change M * r - 3 * r = _; rw [← hA]
  have h4 : (M - 4) * r = A - 4 * r := by rw [Nat.sub_mul]; change M * r - 4 * r = _; rw [← hA]
  have h24 : (2 * M - 4) * r = 2 * A - 4 * r := by
    rw [Nat.sub_mul, Nat.mul_assoc]
    change 2 * (M * r) - 4 * r = _
    rw [← hA]
  have hfirst := run_twos t t v (A - 4 * r) (2 * A - 6 * r - 1) r hstart (by
    intro i hi
    have he : (2 * A - 6 * r - 1) + 2 * i + 1 = 2 * ((M - 3) * r + i) := by omega
    have hk : (A - 4 * r) + i = (M - 4) * r + i := by omega
    rw [he, hk, t_double]
    rw [t_dyadic_block _ n i hi, t_dyadic_block _ n i hi]
    apply xor_ne_right
    have hb := t_power_sub_three (s+3) (by omega)
    change t (M - 3) = !(t (M - 4)) at hb
    rw [hb]
    cases t (M - 4) <;> decide)
  have hmid : X v (A - 3 * r) = 2 * A - 4 * r - 1 := by
    have hk : A - 4 * r + r = A - 3 * r := by omega
    have hx : (2 * A - 6 * r - 1) + 2 * r = 2 * A - 4 * r - 1 := by omega
    simpa [hk, hx] using hfirst
  have hsecond := run_ones t t v (A - 3 * r) (2 * A - 4 * r - 1) r hmid (by
    intro i hi
    have he : (2 * A - 4 * r - 1) + i + 1 = (2 * M - 4) * r + i := by omega
    have hk : (A - 3 * r) + i = (M - 3) * r + i := by omega
    rw [he, hk, t_dyadic_block _ n i hi, t_dyadic_block _ n i hi]
    have hb := t_twice_power_sub_four (s+3) (by omega)
    change t (2 * M - 4) = t (M - 3) at hb
    rw [hb])
  have hk : A - 3 * r + r = A - 2 * r := by omega
  have hx : (2 * A - 4 * r - 1) + r = 2 * A - 3 * r - 1 := by omega
  simpa [hk, hx] using hsecond

/-- Chaining all dyadic descent blocks gives the last separated and first merged states. -/
theorem descent (n s v A : Nat) (hA : A = 2^(s+3) * 2^n)
    (hstart : X v (A - 4 * 2^n) = 2 * A - 6 * 2^n - 1) :
    X v (A - 3) = 2 * (A - 3) + 1 ∧ X v (A - 2) = 2 * (A - 2) := by
  induction n generalizing s with
  | zero =>
    have hAp : A = 2^(s+3) := by simpa using hA
    have hlarge : 8 ≤ A := by
      rw [hAp]
      exact Nat.pow_le_pow_right (n := 2) (by decide) (by omega : 3 ≤ s + 3)
    have hs0 : X v (A - 4) = 2 * A - 7 := by
      have hs := hstart
      simp only [Nat.pow_zero, Nat.mul_one] at hs
      omega
    have hfirst := run_twos t t v (A - 4) (2 * A - 7) 1 hs0 (by
      intro i hi
      have : i = 0 := by omega
      subst i
      have he : (2 * A - 7) + 2 * 0 + 1 = 2 * (A - 3) := by omega
      rw [he, t_double]
      simp only [Nat.add_zero]
      rw [hAp, t_power_sub_three (s+3) (by omega)]
      simp)
    have hlast := descent_block 0 s v A hA hstart
    constructor
    · have ht : A - 4 + 1 = A - 3 := by omega
      have hx : 2 * A - 7 + 2 * 1 = 2 * (A - 3) + 1 := by omega
      simpa [ht, hx] using hfirst
    · have hx : 2 * A - 3 * 2^0 - 1 = 2 * (A - 2) := by omega
      simpa [hx] using hlast
  | succ n ih =>
    have hnext := descent_block (n+1) s v A hA hstart
    have hA' : A = 2^((s+1)+3) * 2^n := by
      calc
        A = 2^(s+3) * (2^n * 2) := by rw [hA, Nat.pow_succ 2 n]
        _ = (2^(s+3) * 2) * 2^n := by rw [Nat.mul_assoc, Nat.mul_comm 2 (2^n)]
        _ = 2^((s+1)+3) * 2^n := by
          rw [show (s+1)+3 = (s+3)+1 by omega, Nat.pow_succ 2 (s+3)]
    have ht : A - 2 * 2^(n+1) = A - 4 * 2^n := by rw [Nat.pow_succ]; omega
    have hx : 2 * A - 3 * 2^(n+1) - 1 = 2 * A - 6 * 2^n - 1 := by rw [Nat.pow_succ]; omega
    exact ih (s+1) hA' (by simpa [ht, hx] using hnext)

/-- A trajectory in the common join state has the exact final descent. -/
theorem common_descent (n v : Nat) (hstart : X v (4 * 2^n) = 10 * 2^n - 1) :
    X v (8 * 2^n - 3) = 2 * (8 * 2^n - 3) + 1 ∧
      X v (8 * 2^n - 2) = 2 * (8 * 2^n - 2) := by
  apply descent n 0 v (8 * 2^n) rfl
  have ht : 8 * 2^n - 4 * 2^n = 4 * 2^n := by omega
  have hx : 2 * (8 * 2^n) - 6 * 2^n - 1 = 10 * 2^n - 1 := by omega
  simpa [ht, hx] using hstart

theorem upper_coalescence (n : Nat) :
    X (6 * 2^n - 1) (8 * 2^n - 2) = 2 * (8 * 2^n - 2) :=
  (common_descent n _ (upper_join n)).2

/-- The five exact runs from `6r`, with `r=2^n`. -/
theorem five_run_join (n : Nat) : X (6 * 2^n) (8 * 2^n) = 20 * 2^n - 1 := by
  let r := 2^n
  have hr : 0 < r := Nat.two_pow_pos n
  have hIraw := run_twos t t (6 * r) 0 (6 * r) (2 * r) rfl (by
    intro i hi
    have he : 6 * r + 2 * i + 1 = 2 * (3 * r + i) + 1 := by omega
    rw [he, t_double_add_one]
    have hb := block_eq n 3 0 2 i (by
      intro j hj
      have hcases : j = 0 ∨ j = 1 := by omega
      rcases hcases with h | h <;> subst j <;> decide +kernel) hi
    have hb' : t (3 * r + i) = t i := by simpa [r] using hb
    rw [hb']
    simp)
  have hI : X (6 * r) (2 * r) = 10 * r := by
    have hx : 6 * r + 2 * (2 * r) = 10 * r := by omega
    simpa [hx] using hIraw
  have hII : X (6 * r) (2 * r + 1) = 10 * r + 1 := by
    change boundary t (t (2 * r)) (X (6 * r) (2 * r)) = 10 * r + 1
    rw [hI]
    simp [boundary, r, t_ten_pow_add_one, t_mul_two_pow]
  have hIIIraw := run_twos t t (6 * r) (2 * r + 1) (10 * r + 1) (r - 1) hII (by
    intro i hi
    have hij : 1 + i < 2^n := by change 1 + i < r; omega
    have he : (10 * r + 1) + 2 * i + 1 = 2 * (5 * r + (1 + i)) := by omega
    have hk : (2 * r + 1) + i = 2 * r + (1 + i) := by omega
    rw [he, hk, t_double, t_dyadic_block _ n _ hij, t_dyadic_block _ n _ hij]
    simp)
  have hIII : X (6 * r) (3 * r) = 12 * r - 1 := by
    have ht : 2 * r + 1 + (r - 1) = 3 * r := by omega
    have hx : 10 * r + 1 + 2 * (r - 1) = 12 * r - 1 := by omega
    simpa [ht, hx] using hIIIraw
  have hIVraw := run_ones t t (6 * r) (3 * r) (12 * r - 1) (2 * r) hIII (by
    intro i hi
    have he : (12 * r - 1) + i + 1 = 12 * r + i := by omega
    rw [he]
    exact block_eq n 12 3 2 i (by
      intro j hj
      have hcases : j = 0 ∨ j = 1 := by omega
      rcases hcases with h | h <;> subst j <;> decide +kernel) hi)
  have hIV : X (6 * r) (5 * r) = 14 * r - 1 := by
    have ht : 3 * r + 2 * r = 5 * r := by omega
    have hx : (12 * r - 1) + 2 * r = 14 * r - 1 := by omega
    simpa [ht, hx] using hIVraw
  have hVraw := run_twos t t (6 * r) (5 * r) (14 * r - 1) (3 * r) hIV (by
    intro i hi
    have he : (14 * r - 1) + 2 * i + 1 = 2 * (7 * r + i) := by omega
    rw [he, t_double]
    exact block_ne n 7 5 3 i (by
      intro j hj
      have hcases : j = 0 ∨ j = 1 ∨ j = 2 := by omega
      rcases hcases with h | h | h <;> subst j <;> decide +kernel) hi)
  have ht : 5 * r + 3 * r = 8 * r := by omega
  have hx : (14 * r - 1) + 2 * (3 * r) = 20 * r - 1 := by omega
  simpa [ht, hx] using hVraw

/-- The lower endpoint of each dyadic start interval joins the same descent. -/
theorem lower_join (n : Nat) : X (3 * 2^n) (4 * 2^n) = 10 * 2^n - 1 := by
  cases n with
  | zero => decide +kernel
  | succ n =>
    have h := five_run_join n
    have ha : 3 * 2^(n+1) = 6 * 2^n := by rw [Nat.pow_succ]; omega
    have hb : 4 * 2^(n+1) = 8 * 2^n := by rw [Nat.pow_succ]; omega
    have hc : 10 * 2^(n+1) - 1 = 20 * 2^n - 1 := by rw [Nat.pow_succ]; omega
    simpa [ha, hb, hc] using h

/-- Coalescence with the baseline is permanent. -/
theorem baseline_later (v k ell : Nat) (hk : X v k = 2 * k) (hle : k ≤ ell) :
    X v ell = 2 * ell := by
  have he : X v k = X 0 k := by rw [baseline]; exact hk
  have hp := coalescence_persists t t v 0 k he (ell - k)
  have hs : k + (ell - k) = ell := by omega
  simpa [hs, baseline] using hp

/-- Monotonicity puts both frontier boundaries on the drained baseline. -/
theorem dyadic_coalesced (n v : Nat) (hv : v + 1 ≤ 6 * 2^n - 1) :
    X v (8 * 2^n - 2) = X (v+1) (8 * 2^n - 2) := by
  have hlo := trajectory_mono t t (Nat.zero_le v) (8 * 2^n - 2)
  have hmid := trajectory_mono t t (Nat.le_succ v) (8 * 2^n - 2)
  have hhi := trajectory_mono t t hv (8 * 2^n - 2)
  have hbase := baseline (8 * 2^n - 2)
  have htop := upper_coalescence n
  change X 0 _ ≤ X v _ at hlo
  change X v _ ≤ X (v+1) _ at hmid
  change X (v+1) _ ≤ X (6 * 2^n - 1) _ at hhi
  omega

/-- Every nonempty matching frontier precedes a known coalescence time. -/
theorem reachable_before_coalescence (color target : Nat → Bool)
    (v k ell : Nat) (hv : 1 ≤ v)
    (hk : trajectory color target v k = trajectory color target (v+1) k)
    (hpath : ∃ w, Reachable color target v ell w) : ell < k := by
  have hs := (nonempty_iff_separated color target v hv ell).1 hpath
  by_cases h : ell < k
  · exact h
  · have hp := coalescence_persists color target v (v+1) k hk (ell-k)
    have he : k + (ell-k) = ell := by omega
    rw [he] at hp
    omega

/-- Universal sharp bound for every matching path, not only a chosen maximum. -/
theorem sharp_path_bound (v ell : Nat) (hv : 1 ≤ v)
    (hpath : ∃ w, Reachable t t v ell w) : 3 * ell ≤ 8 * v - 1 := by
  by_cases hsmall : v = 1
  · subst v
    have hc : X 1 1 = X 2 1 := by decide +kernel
    have he := reachable_before_coalescence t t 1 1 ell (by omega) hc hpath
    omega
  · obtain ⟨n, hl, hu⟩ := exists_dyadic_interval (v+1) (by omega)
    have hq := Nat.two_pow_pos n
    have hfront : v + 1 ≤ 6 * 2^n - 1 := by omega
    have he := reachable_before_coalescence t t v (8 * 2^n - 2) ell hv
      (dyadic_coalesced n v hfront) hpath
    omega

/-- A coalesced finite frontier has a greatest preceding nonempty depth. -/
theorem maximum_exists_of_coalescence (color target : Nat → Bool)
    (v : Nat) (hv : 1 ≤ v) (k : Nat)
    (hk : trajectory color target v k = trajectory color target (v+1) k) :
    ∃ ell, IsMaximumLength color target v ell := by
  induction k with
  | zero => simp [trajectory] at hk
  | succ k ih =>
    by_cases he : trajectory color target v k = trajectory color target (v+1) k
    · exact ih he
    · refine ⟨k, (maximum_length_iff color target v k hv).2 ⟨?_, hk⟩⟩
      have hm := trajectory_mono color target (Nat.le_succ v) k
      change trajectory color target v k ≤ trajectory color target (v+1) k at hm
      omega

/-- Every positive start has a finite maximum, satisfying the conjectured bound. -/
theorem sharp_maximum_exists (v : Nat) (hv : 1 ≤ v) :
    ∃ ell, IsMaximumLength t t v ell ∧ 3 * ell ≤ 8 * v - 1 := by
  obtain ⟨n, _, hu⟩ := exists_dyadic_interval (v+2) (by omega)
  have hc := dyadic_coalesced n v (by omega)
  obtain ⟨ell, hmax⟩ := maximum_exists_of_coalescence t t v hv _ hc
  exact ⟨ell, hmax, sharp_path_bound v ell hv hmax.1⟩

/-- At an equality-family start, the lower boundary has already drained. -/
theorem lower_preterminal (n : Nat) :
    X (3 * 2^n - 1) (8 * 2^n - 3) = 2 * (8 * 2^n - 3) := by
  cases n with
  | zero => decide +kernel
  | succ n =>
    have hp := Nat.two_pow_pos n
    have hs : 3 * 2^(n+1) - 1 = 6 * 2^n - 1 := by rw [Nat.pow_succ]; omega
    rw [hs]
    exact baseline_later _ (8 * 2^n - 2) _ (upper_coalescence n) (by
      rw [Nat.pow_succ]
      omega)

/-- Exact sharp equality for every dyadic scale in the original matching graph. -/
theorem sharp_equality_family (n : Nat) :
    IsMaximumLength t t (3 * 2^n - 1) (8 * 2^n - 3) := by
  have hp := Nat.two_pow_pos n
  have hupper := common_descent n (3 * 2^n) (lower_join n)
  have hlower := lower_preterminal n
  have hfinal := baseline_later (3 * 2^n - 1) (8 * 2^n - 3) (8 * 2^n - 2) hlower (by omega)
  have hv : 1 ≤ 3 * 2^n - 1 := by omega
  have hs : (3 * 2^n - 1) + 1 = 3 * 2^n := by omega
  have ht : (8 * 2^n - 3) + 1 = 8 * 2^n - 2 := by omega
  apply (maximum_length_iff t t _ _ hv).2
  constructor
  · change X (3 * 2^n - 1) (8 * 2^n - 3) < X ((3 * 2^n - 1)+1) (8 * 2^n - 3)
    rw [hs, hlower, hupper.1]
    omega
  · change X (3 * 2^n - 1) ((8 * 2^n - 3)+1) = X ((3 * 2^n - 1)+1) ((8 * 2^n - 3)+1)
    rw [hs, ht, hfinal, hupper.2]

/-- The classification construction's row coloring is the actual Thue--Morse bit. -/
theorem binary_row_eq (w : Nat) : BinaryAvoidance.row t w = t w := by
  by_cases h : w % 2 = 0
  · have hw : w = 2 * (w / 2) := by omega
    rw [hw, BinaryAvoidance.row_even, t_double]
  · have hw : w = 2 * (w / 2) + 1 := by omega
    rw [hw, BinaryAvoidance.row_odd, t_double_add_one]

/-- The sharp-bound graph is exactly the existing binary avoiding construction. -/
theorem binary_edge_iff (u w : Nat) (label : Bool) :
    BinaryAvoidance.Edge t u w label ↔ Edge t label u w := by
  unfold BinaryAvoidance.Edge Edge
  rw [binary_row_eq]
  cases t w <;> cases label <;> simp

/-- Every actual finite edge-path prefix is represented by `Reachable`. -/
theorem binary_prefix_reachable (path : Nat → Nat) (ell : Nat)
    (hpath : ∀ k, k < ell → BinaryAvoidance.Edge t (path k) (path (k+1)) (t k)) :
    Reachable t t (path 0) ell (path ell) := by
  induction ell with
  | zero => rfl
  | succ ell ih =>
    exact ⟨path ell, ih (fun k hk => hpath k (by omega)),
      (binary_edge_iff _ _ _).1 (hpath ell (by omega))⟩

/-- The sharp bound applies directly to finite path prefixes in BinaryAvoidance. -/
theorem binary_path_prefix_bound (path : Nat → Nat) (ell : Nat)
    (hv : 1 ≤ path 0)
    (hpath : ∀ k, k < ell → BinaryAvoidance.Edge t (path k) (path (k+1)) (t k)) :
    3 * ell ≤ 8 * path 0 - 1 :=
  sharp_path_bound (path 0) ell hv ⟨path ell, binary_prefix_reachable path ell hpath⟩

/-- The dyadic family is the entire equality set for positive-start maxima. -/
theorem sharp_equality_indices (v ell : Nat) (hv : 1 ≤ v)
    (hmax : IsMaximumLength t t v ell) :
    (3 * ell = 8 * v - 1) ↔
      ∃ n, v = 3 * 2^n - 1 ∧ ell = 8 * 2^n - 3 := by
  constructor
  · intro heq
    have hv2 : 2 ≤ v := by omega
    obtain ⟨n, hl, hu⟩ := exists_dyadic_interval (v+1) (by omega)
    have hq := Nat.two_pow_pos n
    have hlen := reachable_before_coalescence t t v (8 * 2^n - 2) ell hv
      (dyadic_coalesced n v (by omega)) hmax.1
    exact ⟨n, by omega, by omega⟩
  · rintro ⟨n, hvn, hell⟩
    have hq := Nat.two_pow_pos n
    omega

#print axioms run_ones
#print axioms run_twos
#print axioms block_eq
#print axioms block_ne
#print axioms baseline
#print axioms upper_join
#print axioms descent_block
#print axioms common_descent
#print axioms upper_coalescence
#print axioms five_run_join
#print axioms lower_join
#print axioms sharp_path_bound
#print axioms sharp_maximum_exists
#print axioms sharp_equality_family
#print axioms binary_row_eq
#print axioms binary_edge_iff
#print axioms binary_prefix_reachable
#print axioms binary_path_prefix_bound
#print axioms sharp_equality_indices

end SharpThueMorse
