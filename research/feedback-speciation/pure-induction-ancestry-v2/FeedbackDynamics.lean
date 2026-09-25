import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-! Cultural learning and neutral gene exchange. No species predicate is assumed. -/
namespace FeedbackDynamics
noncomputable def majority (x : ℝ) : ℝ := 3*x^2 - 2*x^3
noncomputable def mix (m x y : ℝ) : ℝ := (1-m)*x + m*y
noncomputable def culture (m : ℝ) (s : ℝ × ℝ) : ℝ × ℝ :=
  (mix m (majority s.1) (majority s.2), mix m (majority s.2) (majority s.1))
noncomputable def polarized (d : ℝ) : ℝ × ℝ := ((1+d)/2, (1-d)/2)
noncomputable def error (s p : ℝ × ℝ) : ℝ := max |s.1-p.1| |s.2-p.2|
theorem majority_probability (x : ℝ) : majority x = x^3 + 3*x^2*(1-x) := by
  unfold majority; ring
theorem majority_complement (x : ℝ) : majority (1-x) = 1-majority x := by
  unfold majority; ring
theorem majority_mem_unit {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    majority x ∈ Set.Icc (0:ℝ) 1 := by
  have h0 : 0 ≤ x^2 * (3-2*x) := mul_nonneg (sq_nonneg x) (by linarith [hx.2])
  have h1 : 0 ≤ (1-x)^2*(1+2*x) := mul_nonneg (sq_nonneg (1-x)) (by linarith [hx.1])
  constructor <;> dsimp [majority] <;> nlinarith
theorem mix_mem_unit {m x y : ℝ} (hm : m ∈ Set.Icc (0:ℝ) 1)
    (hx : x ∈ Set.Icc (0:ℝ) 1) (hy : y ∈ Set.Icc (0:ℝ) 1) :
    mix m x y ∈ Set.Icc (0:ℝ) 1 := by
  have ha := mul_nonneg (show 0 ≤ 1-m by linarith [hm.2]) hx.1
  have hb := mul_nonneg hm.1 hy.1
  have hc := mul_nonneg (show 0 ≤ 1-m by linarith [hm.2]) (show 0 ≤ 1-x by linarith [hx.2])
  have hd := mul_nonneg hm.1 (show 0 ≤ 1-y by linarith [hy.2])
  constructor <;> dsimp [mix] <;> nlinarith
theorem culture_mem_square {m : ℝ} {s : ℝ × ℝ}
    (hm : m ∈ Set.Icc (0:ℝ) 1) (hs : s.1 ∈ Set.Icc (0:ℝ) 1 ∧ s.2 ∈ Set.Icc (0:ℝ) 1) :
    (culture m s).1 ∈ Set.Icc (0:ℝ) 1 ∧ (culture m s).2 ∈ Set.Icc (0:ℝ) 1 :=
  ⟨mix_mem_unit hm (majority_mem_unit hs.1) (majority_mem_unit hs.2),
   mix_mem_unit hm (majority_mem_unit hs.2) (majority_mem_unit hs.1)⟩
theorem polarized_fixed {m d : ℝ} (hd : (1-2*m)*d^2 = 1-6*m) :
    culture m (polarized d) = polarized d := by
  have ha : mix m (majority ((1+d)/2)) (majority ((1-d)/2)) - (1+d)/2 =
      d*((1-6*m)-(1-2*m)*d^2)/4 := by unfold mix majority; ring
  have hb : mix m (majority ((1-d)/2)) (majority ((1+d)/2)) - (1-d)/2 =
      -d*((1-6*m)-(1-2*m)*d^2)/4 := by unfold mix majority; ring
  rw [hd] at ha hb
  apply Prod.ext <;> dsimp [culture, polarized] <;> linarith
theorem polarized_slope {m d : ℝ} (hden : 1-2*m ≠ 0)
    (hd : (1-2*m)*d^2 = 1-6*m) :
    6*((1+d)/2)*(1-(1+d)/2) = 6*m/(1-2*m) ∧
    6*((1-d)/2)*(1-(1-d)/2) = 6*m/(1-2*m) := by
  constructor <;> apply (eq_div_iff hden).2 <;> nlinarith [hd]
/-- Explicit action of the linearized coefficient matrix. -/
noncomputable def linearized (m a : ℝ) (v : ℝ × ℝ) : ℝ × ℝ :=
  (a*mix m v.1 v.2, a*mix m v.2 v.1)
theorem linearized_modes (m a t : ℝ) :
    linearized m a (t,t) = (a*t,a*t) ∧
    linearized m a (t,-t) = (a*(1-2*m)*t, -(a*(1-2*m)*t)) := by
  constructor <;> apply Prod.ext <;> dsimp [linearized, mix] <;> ring
theorem full_stability_range {m : ℝ} (hm0 : 0 < m) (hm8 : m < 1/8) :
    0 < 6*m/(1-2*m) ∧ 6*m/(1-2*m) < 1 ∧ 0 < 6*m ∧ 6*m < 1 := by
  have hden : 0 < 1-2*m := by linarith
  exact ⟨div_pos (by linarith) hden, (div_lt_one hden).2 (by linarith), by linarith, by linarith⟩
theorem restricted_stability_trap {m : ℝ} (hm8 : 1/8 < m) (hm6 : m < 1/6) :
    0 < 6*m ∧ 6*m < 1 ∧ 1 < 6*m/(1-2*m) := by
  have hden : 0 < 1-2*m := by linarith
  exact ⟨by linarith, by linarith, (one_lt_div hden).2 (by linarith)⟩
theorem mix_difference (g u v : ℝ) : mix g u v - mix g v u = (1-2*g)*(u-v) := by
  unfold mix; ring
theorem mix_sum (g u v : ℝ) : mix g u v + mix g v u = u+v := by
  unfold mix; ring
theorem neutral_geometric_bound {u v ρ : ℕ → ℝ} {a : ℝ}
    (_ha : 0 < a) (hρ : ∀ n, a ≤ ρ n ∧ ρ n ≤ 1/2)
    (hu : ∀ n, u (n+1) = mix (ρ n) (u n) (v n))
    (hv : ∀ n, v (n+1) = mix (ρ n) (v n) (u n)) :
    ∀ n, |u n-v n| ≤ (1-2*a)^n * |u 0-v 0| := by
  have ha2 : a ≤ 1/2 := (hρ 0).1.trans (hρ 0).2
  have hq : 0 ≤ 1-2*a := by linarith
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [hu n, hv n, mix_difference, abs_mul, abs_of_nonneg (show 0 ≤ 1-2*ρ n by linarith [(hρ n).2])]
    calc
      (1-2*ρ n)*|u n-v n| ≤ (1-2*a)*((1-2*a)^n*|u 0-v 0|) :=
        mul_le_mul (by linarith [(hρ n).1]) ih (abs_nonneg _) hq
      _ = (1-2*a)^(n+1)*|u 0-v 0| := by rw [pow_succ]; ring
theorem error_nonneg (s p : ℝ × ℝ) : 0 ≤ error s p :=
  (abs_nonneg _).trans (le_max_left _ _)

theorem majority_local_bound {x p A r : ℝ}
    (hp : p ∈ Set.Icc (0:ℝ) 1) (hA : 6*p*(1-p) = A) (hA0 : 0 ≤ A)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hx : |x-p| ≤ r) :
    |majority x-majority p| ≤ (A+5*r)*|x-p| := by
  have hb : |3-6*p| ≤ 3 := abs_le.mpr ⟨by linarith [hp.2], by linarith [hp.1]⟩
  have he : |(x-p)*(3-6*p)| ≤ 3*r := by
    rw [abs_mul]
    nlinarith [mul_le_mul hx hb (abs_nonneg (3-6*p)) hr0]
  have hs : (x-p)^2 ≤ r := by
    have h := mul_le_mul hx (hx.trans hr1) (abs_nonneg (x-p)) hr0
    nlinarith [sq_abs (x-p)]
  have hc : |A+(x-p)*(3-6*p)-2*(x-p)^2| ≤ A+5*r := by
    apply abs_le.mpr
    have he' := abs_le.mp he
    constructor <;> nlinarith [sq_nonneg (x-p)]
  have heq : majority x-majority p =
      (x-p)*(A+(x-p)*(3-6*p)-2*(x-p)^2) := by
    rw [← hA]; unfold majority; ring
  rw [heq, abs_mul]
  nlinarith [mul_le_mul_of_nonneg_left hc (abs_nonneg (x-p))]

theorem mix_absolute {m x y p q B : ℝ} (hm : m ∈ Set.Icc (0:ℝ) 1)
    (hx : |x-p| ≤ B) (hy : |y-q| ≤ B) :
    |mix m x y-mix m p q| ≤ B := by
  have hm' : 0 ≤ 1-m := by linarith [hm.2]
  have heq : mix m x y-mix m p q = (1-m)*(x-p)+m*(y-q) := by unfold mix; ring
  rw [heq]
  calc
    |(1-m)*(x-p)+m*(y-q)| ≤ |(1-m)*(x-p)|+|m*(y-q)| := abs_add_le _ _
    _ = (1-m)*|x-p|+m*|y-q| := by rw [abs_mul, abs_mul, abs_of_nonneg hm', abs_of_nonneg hm.1]
    _ ≤ (1-m)*B+m*B := add_le_add (mul_le_mul_of_nonneg_left hx hm') (mul_le_mul_of_nonneg_left hy hm.1)
    _ = B := by ring

theorem culture_local_bound {m A r : ℝ} {s p : ℝ × ℝ}
    (hm : m ∈ Set.Icc (0:ℝ) 1)
    (hp : p.1 ∈ Set.Icc (0:ℝ) 1 ∧ p.2 ∈ Set.Icc (0:ℝ) 1)
    (hA1 : 6*p.1*(1-p.1) = A) (hA2 : 6*p.2*(1-p.2) = A)
    (hA0 : 0 ≤ A) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hs : error s p ≤ r) :
    error (culture m s) (culture m p) ≤ (A+5*r)*error s p := by
  have hE1 : |s.1-p.1| ≤ error s p := le_max_left _ _
  have hE2 : |s.2-p.2| ≤ error s p := le_max_right _ _
  have hL : 0 ≤ A+5*r := by linarith
  have h1 := (majority_local_bound hp.1 hA1 hA0 hr0 hr1 (hE1.trans hs)).trans
    (mul_le_mul_of_nonneg_left hE1 hL)
  have h2 := (majority_local_bound hp.2 hA2 hA0 hr0 hr1 (hE2.trans hs)).trans
    (mul_le_mul_of_nonneg_left hE2 hL)
  exact max_le (mix_absolute hm h1 h2) (mix_absolute hm h2 h1)

theorem local_geometric_bound {f : (ℝ × ℝ) → (ℝ × ℝ)} {p : ℝ × ℝ}
    {r q : ℝ} (hr : 0 ≤ r) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hloc : ∀ s, error s p ≤ r → error (f s) p ≤ q*error s p)
    (s : ℕ → ℝ × ℝ) (hstep : ∀ n, s (n+1) = f (s n)) (hstart : error (s 0) p ≤ r) :
    ∀ n, error (s n) p ≤ r ∧ error (s n) p ≤ q^n*error (s 0) p := by
  intro n
  induction n with
  | zero => exact ⟨hstart, by simp⟩
  | succ n ih =>
    rw [hstep n]
    have h := hloc (s n) ih.1
    constructor
    · exact h.trans ((mul_le_mul_of_nonneg_left ih.1 hq0).trans (by nlinarith))
    · calc
        error (f (s n)) p ≤ q*error (s n) p := h
        _ ≤ q*(q^n*error (s 0) p) := mul_le_mul_of_nonneg_left ih.2 hq0
        _ = q^(n+1)*error (s 0) p := by rw [pow_succ]; ring

/-- A full two-coordinate neighbourhood with an explicit geometric contraction rate. -/
theorem polarized_local_geometric {m d : ℝ} (hm0 : 0 < m) (hm8 : m < 1/8)
    (hd0 : 0 < d) (hd1 : d < 1) (hd : (1-2*m)*d^2 = 1-6*m) :
    ∃ r q : ℝ, 0 < r ∧ 0 ≤ q ∧ q < 1 ∧
      ∀ s : ℕ → ℝ × ℝ, (∀ n, s (n+1) = culture m (s n)) →
        error (s 0) (polarized d) ≤ r →
        ∀ n, error (s n) (polarized d) ≤ r ∧
          error (s n) (polarized d) ≤ q^n*error (s 0) (polarized d) := by
  let A := 6*m/(1-2*m)
  let r := (1-A)/10
  let q := A+5*r
  have hA := full_stability_range hm0 hm8
  have hr0 : 0 < r := by dsimp [r, A]; linarith [hA.2.1]
  have hr1 : r ≤ 1 := by dsimp [r, A]; linarith [hA.1]
  have hq0 : 0 ≤ q := by dsimp [q]; have : 0 < A := hA.1; linarith
  have hq1 : q < 1 := by dsimp [q, r, A]; linarith [hA.2.1]
  have hp : (polarized d).1 ∈ Set.Icc (0:ℝ) 1 ∧ (polarized d).2 ∈ Set.Icc (0:ℝ) 1 := by
    dsimp [polarized]; constructor <;> constructor <;> linarith
  have hsl := polarized_slope (m := m) (d := d) (by linarith) hd
  have hfix := polarized_fixed hd
  have hloc : ∀ s, error s (polarized d) ≤ r →
      error (culture m s) (polarized d) ≤ q*error s (polarized d) := by
    intro s hs
    have h := culture_local_bound (m := m) (A := A) (by constructor <;> linarith)
      hp hsl.1 hsl.2 hA.1.le hr0.le hr1 hs
    rwa [hfix] at h
  exact ⟨r, q, hr0, hq0, hq1, fun s hstep hstart =>
    local_geometric_bound hr0.le hq0 hq1.le hloc s hstep hstart⟩

theorem geometric_epsilon_limit {q C : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (hC : 0 ≤ C) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n, N ≤ n → q^n*C < ε := by
  intro ε hε
  have hCp : 0 < C+1 := by linarith
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos hε hCp) hq1
  refine ⟨N, fun n hn => ?_⟩
  have hn' : q^n ≤ q^N := pow_le_pow_of_le_one hq0 hq1.le hn
  have hN' : q^N*(C+1) < ε := (lt_div_iff₀ hCp).mp hN
  have hC' := mul_le_mul_of_nonneg_left (show C ≤ C+1 by linarith) (pow_nonneg hq0 N)
  exact (mul_le_mul_of_nonneg_right hn' hC).trans_lt (hC'.trans_lt hN')

/-- The usual epsilon definition of convergence for the real sup-norm. -/
def ConvergesTo (s : ℕ → ℝ × ℝ) (p : ℝ × ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n, N ≤ n → error (s n) p < ε

/-- Fixed point, Lyapunov stability, and attraction of a full neighbourhood. -/
def LocallyAsymptoticallyStable (f : (ℝ × ℝ) → (ℝ × ℝ)) (p : ℝ × ℝ) : Prop :=
  f p = p ∧
  (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ s : ℕ → ℝ × ℝ, (∀ n, s (n+1) = f (s n)) →
      error (s 0) p < δ → ∀ n, error (s n) p < ε) ∧
  (∃ r : ℝ, 0 < r ∧ ∀ s : ℕ → ℝ × ℝ, (∀ n, s (n+1) = f (s n)) →
    error (s 0) p ≤ r → ConvergesTo s p)

theorem polarized_locally_asymptotically_stable {m d : ℝ}
    (hm0 : 0 < m) (hm8 : m < 1/8) (hd0 : 0 < d) (hd1 : d < 1)
    (hd : (1-2*m)*d^2 = 1-6*m) :
    LocallyAsymptoticallyStable (culture m) (polarized d) := by
  obtain ⟨r,q,hr,hq0,hq1,hgeom⟩ := polarized_local_geometric hm0 hm8 hd0 hd1 hd
  refine ⟨polarized_fixed hd, ?_, ?_⟩
  · intro ε hε
    refine ⟨min r ε, lt_min hr hε, ?_⟩
    intro s hs hstart n
    have hstart_r : error (s 0) (polarized d) ≤ r := (hstart.trans_le (min_le_left _ _)).le
    have hstart_ε : error (s 0) (polarized d) < ε := hstart.trans_le (min_le_right _ _)
    have h := (hgeom s hs hstart_r n).2
    have hp := mul_le_mul_of_nonneg_right (pow_le_one₀ (n := n) hq0 hq1.le)
      (error_nonneg (s 0) (polarized d))
    exact h.trans_lt ((by simpa using hp : q^n*error (s 0) (polarized d) ≤ error (s 0) (polarized d)).trans_lt hstart_ε)
  · refine ⟨r, hr, ?_⟩
    intro s hs hstart ε hε
    obtain ⟨N,hN⟩ := geometric_epsilon_limit hq0 hq1 (error_nonneg (s 0) (polarized d)) ε hε
    exact ⟨N, fun n hn => ((hgeom s hs hstart n).2).trans_lt (hN n hn)⟩

/-- A concrete interior polarized equilibrium makes the family nonvacuous without sqrt imports. -/
theorem explicit_stable_counterexample :
    (0 : ℝ) < 7/78 ∧ (7/78 : ℝ) < 1/8 ∧
    polarized (3/4) = ((7/8:ℝ), (1/8:ℝ)) ∧
    LocallyAsymptoticallyStable (culture (7/78)) ((7/8:ℝ), (1/8:ℝ)) := by
  have heq : polarized (3/4) = ((7/8:ℝ), (1/8:ℝ)) := by norm_num [polarized]
  refine ⟨by norm_num, by norm_num, heq, ?_⟩
  rw [← heq]
  apply polarized_locally_asymptotically_stable <;> norm_num

theorem neutral_epsilon_limit {u v ρ : ℕ → ℝ} {a : ℝ}
    (ha : 0 < a) (hρ : ∀ n, a ≤ ρ n ∧ ρ n ≤ 1/2)
    (hu : ∀ n, u (n+1) = mix (ρ n) (u n) (v n))
    (hv : ∀ n, v (n+1) = mix (ρ n) (v n) (u n)) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n, N ≤ n → |u n-v n| < ε := by
  have ha2 : a ≤ 1/2 := (hρ 0).1.trans (hρ 0).2
  intro ε hε
  obtain ⟨N,hN⟩ := geometric_epsilon_limit (show 0 ≤ 1-2*a by linarith)
    (show 1-2*a < 1 by linarith) (abs_nonneg (u 0-v 0)) ε hε
  exact ⟨N, fun n hn => (neutral_geometric_bound ha hρ hu hv n).trans_lt (hN n hn)⟩
theorem majority_expansion (p e : ℝ) :
    majority (p+e) = majority p + 6*p*(1-p)*e + (3-6*p)*e^2 - 2*e^3 := by
  unfold majority; ring

/-- Exact first-order coefficient with a displayed quadratic/cubic remainder. -/
theorem culture_expansion {m A : ℝ} {p e : ℝ × ℝ}
    (hA1 : 6*p.1*(1-p.1) = A) (hA2 : 6*p.2*(1-p.2) = A) :
    culture m (p.1+e.1,p.2+e.2) =
      ((culture m p).1 + (linearized m A e).1 +
        mix m ((3-6*p.1)*e.1^2-2*e.1^3) ((3-6*p.2)*e.2^2-2*e.2^3),
       (culture m p).2 + (linearized m A e).2 +
        mix m ((3-6*p.2)*e.2^2-2*e.2^3) ((3-6*p.1)*e.1^2-2*e.1^3)) := by
  apply Prod.ext <;> dsimp [culture,linearized]
  all_goals rw [majority_expansion,majority_expansion,hA1,hA2]; unfold mix; ring

/-- An algebraic finite-strength response; distinct from the unformalized exp response. -/
noncomputable def rationalFlow (g k d : ℝ) : ℝ := g/(1+k*d^2)
theorem rationalFlow_bounds {g k d : ℝ} (hg : 0 < g) (hk : 0 ≤ k) (hd : |d| ≤ 1) :
    0 < g/(1+k) ∧ g/(1+k) ≤ rationalFlow g k d ∧ rationalFlow g k d ≤ g := by
  have hsq : 0 ≤ d^2 := sq_nonneg d
  have hsq1 : d^2 ≤ 1 := by have := abs_le.mp hd; nlinarith
  have hden : 0 < 1+k*d^2 := by nlinarith
  have hk1 : 0 < 1+k := by linarith
  refine ⟨div_pos hg hk1, ?_, ?_⟩
  · apply (div_le_div_iff₀ hk1 hden).2
    have := mul_le_mul_of_nonneg_left (show 1+k*d^2 ≤ 1+k by nlinarith) hg.le
    nlinarith
  · apply (div_le_iff₀ hden).2
    have := mul_nonneg hg.le (mul_nonneg hk hsq)
    nlinarith

theorem rational_feedback_neutral_convergence {g k : ℝ} {d u v : ℕ → ℝ}
    (hg : 0 < g) (hg2 : g ≤ 1/2) (hk : 0 ≤ k) (hd : ∀ n, |d n| ≤ 1)
    (hu : ∀ n, u (n+1) = mix (rationalFlow g k (d n)) (u n) (v n))
    (hv : ∀ n, v (n+1) = mix (rationalFlow g k (d n)) (v n) (u n)) :
    (∀ n, |u n-v n| ≤ (1-2*(g/(1+k)))^n * |u 0-v 0|) ∧
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n, N ≤ n → |u n-v n| < ε) := by
  have ha := (rationalFlow_bounds hg hk (hd 0)).1
  have hρ : ∀ n, g/(1+k) ≤ rationalFlow g k (d n) ∧ rationalFlow g k (d n) ≤ 1/2 :=
    fun n => ⟨(rationalFlow_bounds hg hk (hd n)).2.1, (rationalFlow_bounds hg hk (hd n)).2.2.trans hg2⟩
  exact ⟨neutral_geometric_bound ha hρ hu hv, neutral_epsilon_limit ha hρ hu hv⟩

theorem culture_trajectory_mem_square {m : ℝ} (hm : m ∈ Set.Icc (0:ℝ) 1)
    (s : ℕ → ℝ × ℝ) (hs : ∀ n, s (n+1) = culture m (s n))
    (h0 : (s 0).1 ∈ Set.Icc (0:ℝ) 1 ∧ (s 0).2 ∈ Set.Icc (0:ℝ) 1) :
    ∀ n, (s n).1 ∈ Set.Icc (0:ℝ) 1 ∧ (s n).2 ∈ Set.Icc (0:ℝ) 1 := by
  intro n
  induction n with
  | zero => exact h0
  | succ n ih => rw [hs n]; exact culture_mem_square hm ih

/-- Coupling is to the actual cultural trajectory, not an assumed bound on another sequence. -/
theorem coupled_neutral_convergence {m g k : ℝ} {u v : ℕ → ℝ}
    (hm : m ∈ Set.Icc (0:ℝ) 1) (hg : 0 < g) (hg2 : g ≤ 1/2) (hk : 0 ≤ k)
    (s : ℕ → ℝ × ℝ) (hs : ∀ n, s (n+1) = culture m (s n))
    (h0 : (s 0).1 ∈ Set.Icc (0:ℝ) 1 ∧ (s 0).2 ∈ Set.Icc (0:ℝ) 1)
    (hu : ∀ n, u (n+1) = mix (rationalFlow g k ((s n).1-(s n).2)) (u n) (v n))
    (hv : ∀ n, v (n+1) = mix (rationalFlow g k ((s n).1-(s n).2)) (v n) (u n)) :
    (∀ n, |u n-v n| ≤ (1-2*(g/(1+k)))^n * |u 0-v 0|) ∧
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n, N ≤ n → |u n-v n| < ε) := by
  apply rational_feedback_neutral_convergence hg hg2 hk _ hu hv
  intro n
  have h := culture_trajectory_mem_square hm s hs h0 n
  exact abs_le.mpr ⟨by linarith [h.1.1,h.2.2], by linarith [h.1.2,h.2.1]⟩
theorem fixed_response_coupled_neutral_convergence {m : ℝ} {u v : ℕ → ℝ}
    (hm : m ∈ Set.Icc (0:ℝ) 1)
    (s : ℕ → ℝ × ℝ) (hs : ∀ n, s (n+1) = culture m (s n))
    (h0 : (s 0).1 ∈ Set.Icc (0:ℝ) 1 ∧ (s 0).2 ∈ Set.Icc (0:ℝ) 1)
    (hu : ∀ n, u (n+1) = mix (rationalFlow (1/2) 1 ((s n).1-(s n).2)) (u n) (v n))
    (hv : ∀ n, v (n+1) = mix (rationalFlow (1/2) 1 ((s n).1-(s n).2)) (v n) (u n)) :
    (∀ n, |u n-v n| ≤ (1/2:ℝ)^n * |u 0-v 0|) ∧
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n, N ≤ n → |u n-v n| < ε) := by
  have h := coupled_neutral_convergence (g := (1/2:ℝ)) (k := (1:ℝ))
    hm (by norm_num) (by norm_num) (by norm_num) s hs h0 hu hv
  norm_num at h
  exact h
/-- A full neighbourhood of a stable, distinct cultural pair is compatible with
actual coupled neutral homogenization under a nonconstant feedback rule. -/
theorem explicit_cultural_genetic_counterexample :
    LocallyAsymptoticallyStable (culture (7/78)) ((7/8:ℝ), (1/8:ℝ)) ∧
    (7/8:ℝ) ≠ 1/8 ∧
    ∃ r : ℝ, 0 < r ∧ ∀ (s : ℕ → ℝ × ℝ) (u v : ℕ → ℝ),
      (∀ n, s (n+1) = culture (7/78) (s n)) →
      ((s 0).1 ∈ Set.Icc (0:ℝ) 1 ∧ (s 0).2 ∈ Set.Icc (0:ℝ) 1) →
      error (s 0) ((7/8:ℝ), (1/8:ℝ)) ≤ r →
      (∀ n, u (n+1) = mix (rationalFlow (1/2) 1 ((s n).1-(s n).2)) (u n) (v n)) →
      (∀ n, v (n+1) = mix (rationalFlow (1/2) 1 ((s n).1-(s n).2)) (v n) (u n)) →
      ConvergesTo s ((7/8:ℝ), (1/8:ℝ)) ∧
      (∀ n, |u n-v n| ≤ (1/2:ℝ)^n * |u 0-v 0|) ∧
      (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n, N ≤ n → |u n-v n| < ε) := by
  have hstable := explicit_stable_counterexample.2.2.2
  obtain ⟨r,hr,hattr⟩ := hstable.2.2
  refine ⟨hstable, by norm_num, r, hr, ?_⟩
  intro s u v hs hunit hnear hu hv
  exact ⟨hattr s hs hnear, fixed_response_coupled_neutral_convergence
    (by constructor <;> norm_num) s hs hunit hu hv⟩
theorem fixed_response_nonconstant :
    rationalFlow (1/2) 1 0 = (1/2:ℝ) ∧ rationalFlow (1/2) 1 1 = (1/4:ℝ) := by
  norm_num [rationalFlow]

theorem neutral_frequency_invariant {u v ρ : ℕ → ℝ}
    (hρ : ∀ n, ρ n ∈ Set.Icc (0:ℝ) 1)
    (hu : ∀ n, u (n+1) = mix (ρ n) (u n) (v n))
    (hv : ∀ n, v (n+1) = mix (ρ n) (v n) (u n))
    (h0 : u 0 ∈ Set.Icc (0:ℝ) 1 ∧ v 0 ∈ Set.Icc (0:ℝ) 1) :
    ∀ n, u n ∈ Set.Icc (0:ℝ) 1 ∧ v n ∈ Set.Icc (0:ℝ) 1 := by
  intro n
  induction n with
  | zero => exact h0
  | succ n ih =>
    rw [hu n,hv n]
    exact ⟨mix_mem_unit (hρ n) ih.1 ih.2, mix_mem_unit (hρ n) ih.2 ih.1⟩

end FeedbackDynamics
#print axioms FeedbackDynamics.culture_mem_square
#print axioms FeedbackDynamics.polarized_fixed
#print axioms FeedbackDynamics.polarized_slope
#print axioms FeedbackDynamics.linearized_modes
#print axioms FeedbackDynamics.full_stability_range
#print axioms FeedbackDynamics.restricted_stability_trap

#print axioms FeedbackDynamics.neutral_geometric_bound


#print axioms FeedbackDynamics.majority_local_bound
#print axioms FeedbackDynamics.polarized_local_geometric



#print axioms FeedbackDynamics.polarized_locally_asymptotically_stable
#print axioms FeedbackDynamics.explicit_stable_counterexample
#print axioms FeedbackDynamics.neutral_epsilon_limit


#print axioms FeedbackDynamics.culture_expansion
#print axioms FeedbackDynamics.rationalFlow_bounds
#print axioms FeedbackDynamics.coupled_neutral_convergence


#print axioms FeedbackDynamics.fixed_response_coupled_neutral_convergence
#print axioms FeedbackDynamics.explicit_cultural_genetic_counterexample


#print axioms FeedbackDynamics.fixed_response_nonconstant
#print axioms FeedbackDynamics.neutral_frequency_invariant

