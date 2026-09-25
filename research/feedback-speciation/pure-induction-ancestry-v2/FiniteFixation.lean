import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
Finite-state harmonic certificates, with an actual forward marginal recursion.
All probabilities below are finite distributions. No infinite product measure
or path-event probability is constructed in this module. Terminal classes may
contain many states and the kernel may move between states of the same class.
-/
namespace FiniteFixation
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

universe u
variable {S : Type u} [Fintype S]

structure Kernel (S : Type u) [Fintype S] where
  transition : S → S → ℝ
  nonneg : ∀ s t, 0 ≤ transition s t
  row_sum : ∀ s, ∑ t, transition s t = 1

structure Boundary (S : Type u) where
  Win : S → Prop
  Loss : S → Prop
  disjoint : ∀ s, Win s → Loss s → False

def Boundary.Terminal (B : Boundary S) (s : S) : Prop := B.Win s ∨ B.Loss s

def indicator (p : S → Prop) (s : S) : ℝ := if p s then 1 else 0

def transientIndicator (B : Boundary S) (s : S) : ℝ :=
  if B.Terminal s then 0 else 1

def expect (μ f : S → ℝ) : ℝ := ∑ s, μ s * f s

/-- Backward action on functions; the certificate is harmonic for this operator. -/
def backward (K : Kernel S) (f : S → ℝ) (s : S) : ℝ :=
  ∑ t, K.transition s t * f t

/-- Forward action on finite distributions. -/
def push (K : Kernel S) (μ : S → ℝ) (t : S) : ℝ :=
  ∑ s, μ s * K.transition s t

/-- The actual n-generation marginal, starting from one specified state. -/
def marginal (K : Kernel S) (start : S) : ℕ → S → ℝ
  | 0 => fun t => if start = t then 1 else 0
  | n+1 => push K (marginal K start n)

structure Absorbing (K : Kernel S) (B : Boundary S) : Prop where
  win : ∀ s t, B.Win s → ¬ B.Win t → K.transition s t = 0
  loss : ∀ s t, B.Loss s → ¬ B.Loss t → K.transition s t = 0

/-- A uniform one-step lower bound on landing anywhere in either terminal class. -/
def UniformTerminal (K : Kernel S) (B : Boundary S) (ε : ℝ) : Prop :=
  ∀ s, ε ≤ backward K (indicator B.Terminal) s

structure Certificate (K : Kernel S) (B : Boundary S) (h : S → ℝ) : Prop where
  bounds : ∀ s, 0 ≤ h s ∧ h s ≤ 1
  win : ∀ s, B.Win s → h s = 1
  loss : ∀ s, B.Loss s → h s = 0
  harmonic : ∀ s, backward K h s = h s

def winProbability (K : Kernel S) (B : Boundary S) (start : S) (n : ℕ) : ℝ :=
  expect (marginal K start n) (indicator B.Win)

def transientMass (K : Kernel S) (B : Boundary S) (start : S) (n : ℕ) : ℝ :=
  expect (marginal K start n) (transientIndicator B)

theorem expect_push (K : Kernel S) (μ f : S → ℝ) :
    expect (push K μ) f = expect μ (backward K f) := by
  unfold expect push backward
  simp_rw [Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

theorem expect_mono {μ f g : S → ℝ}
    (hμ : ∀ s, 0 ≤ μ s) (hfg : ∀ s, f s ≤ g s) : expect μ f ≤ expect μ g := by
  exact Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left (hfg s) (hμ s))

theorem expect_nonneg {μ f : S → ℝ}
    (hμ : ∀ s, 0 ≤ μ s) (hf : ∀ s, 0 ≤ f s) : 0 ≤ expect μ f := by
  exact Finset.sum_nonneg (fun s _ => mul_nonneg (hμ s) (hf s))

theorem expect_sub (μ f g : S → ℝ) :
    expect μ (fun s => f s - g s) = expect μ f - expect μ g := by
  simp only [expect, mul_sub, Finset.sum_sub_distrib]

theorem expect_scale (μ f : S → ℝ) (c : ℝ) :
    expect μ (fun s => c * f s) = c * expect μ f := by
  unfold expect
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  exact mul_left_comm (μ s) c (f s)

theorem apply_one (K : Kernel S) : backward K (fun _ => 1) = fun _ => 1 := by
  funext s
  simpa only [backward, mul_one] using K.row_sum s

theorem marginal_nonneg (K : Kernel S) (start : S) :
    ∀ n t, 0 ≤ marginal K start n t := by
  intro n
  induction n with
  | zero => intro t; dsimp [marginal]; split <;> norm_num
  | succ n ih =>
    intro t
    exact Finset.sum_nonneg (fun s _ => mul_nonneg (ih s) (K.nonneg s t))

theorem expect_marginal_zero (K : Kernel S) (start : S) (f : S → ℝ) :
    expect (marginal K start 0) f = f start := by
  simp [expect, marginal, ite_mul]

theorem marginal_total (K : Kernel S) (start : S) :
    ∀ n, expect (marginal K start n) (fun _ => 1) = 1 := by
  intro n
  induction n with
  | zero => exact expect_marginal_zero K start _
  | succ n ih =>
    change expect (push K (marginal K start n)) (fun _ => 1) = 1
    rw [expect_push, apply_one]
    exact ih

theorem indicator_bounds (p : S → Prop) (s : S) :
    0 ≤ indicator p s ∧ indicator p s ≤ 1 := by
  dsimp [indicator]
  split <;> norm_num

theorem win_probability_bounds (K : Kernel S) (B : Boundary S) (start : S) (n : ℕ) :
    0 ≤ winProbability K B start n ∧ winProbability K B start n ≤ 1 := by
  constructor
  · exact expect_nonneg (marginal_nonneg K start n) (fun s => (indicator_bounds B.Win s).1)
  · calc
      _ ≤ expect (marginal K start n) (fun _ => 1) :=
        expect_mono (marginal_nonneg K start n) (fun s => (indicator_bounds B.Win s).2)
      _ = 1 := marginal_total K start n
theorem harmonic_expectation (K : Kernel S) (start : S) (h : S → ℝ)
    (hh : ∀ s, backward K h s = h s) :
    ∀ n, expect (marginal K start n) h = h start := by
  intro n
  induction n with
  | zero => exact expect_marginal_zero K start h
  | succ n ih =>
    change expect (push K (marginal K start n)) h = h start
    rw [expect_push, funext hh]
    exact ih

theorem terminal_transient_complement (K : Kernel S) (B : Boundary S) (s : S) :
    backward K (indicator B.Terminal) s + backward K (transientIndicator B) s = 1 := by
  rw [← K.row_sum s]
  unfold backward
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  by_cases ht : B.Terminal t <;> simp [indicator, transientIndicator, ht]

theorem terminal_has_zero_transient (K : Kernel S) (B : Boundary S)
    (ha : Absorbing K B) {s : S} (hs : B.Terminal s) :
    backward K (transientIndicator B) s = 0 := by
  apply Finset.sum_eq_zero
  intro t _
  by_cases ht : B.Terminal t
  · simp [transientIndicator, ht]
  · have hP : K.transition s t = 0 := by
      rcases hs with hs | hs
      · exact ha.win s t hs (fun hw => ht (Or.inl hw))
      · exact ha.loss s t hs (fun hl => ht (Or.inr hl))
    simp [hP]

theorem transient_step_bound (K : Kernel S) (B : Boundary S)
    (ha : Absorbing K B) {ε : ℝ} (hu : UniformTerminal K B ε) (s : S) :
    backward K (transientIndicator B) s ≤ (1-ε) * transientIndicator B s := by
  by_cases hs : B.Terminal s
  · rw [terminal_has_zero_transient K B ha hs]
    simp [transientIndicator, hs]
  · have hc := terminal_transient_complement K B s
    have he := hu s
    have hi : transientIndicator B s = 1 := by simp [transientIndicator, hs]
    rw [hi, mul_one]
    linarith

theorem transient_mass_nonneg (K : Kernel S) (B : Boundary S) (start : S) (n : ℕ) :
    0 ≤ transientMass K B start n := by
  apply expect_nonneg (marginal_nonneg K start n)
  intro s
  dsimp [transientIndicator]
  split <;> norm_num

theorem transient_mass_geometric (K : Kernel S) (B : Boundary S)
    (ha : Absorbing K B) {ε : ℝ} (hε1 : ε ≤ 1)
    (hu : UniformTerminal K B ε) (start : S) :
    ∀ n, transientMass K B start n ≤ (1-ε)^n := by
  intro n
  induction n with
  | zero =>
    unfold transientMass
    rw [expect_marginal_zero]
    dsimp [transientIndicator]
    split <;> simp
  | succ n ih =>
    have hc : transientMass K B start (n+1) ≤ (1-ε) * transientMass K B start n := by
      change expect (push K (marginal K start n)) (transientIndicator B) ≤
        (1-ε) * expect (marginal K start n) (transientIndicator B)
      rw [expect_push, ← expect_scale]
      exact expect_mono (marginal_nonneg K start n) (transient_step_bound K B ha hu)
    calc
      _ ≤ (1-ε) * transientMass K B start n := hc
      _ ≤ (1-ε) * (1-ε)^n := mul_le_mul_of_nonneg_left ih (by linarith)
      _ = (1-ε)^(n+1) := by rw [pow_succ, mul_comm]

theorem certificate_pointwise_error (K : Kernel S) (B : Boundary S)
    {h : S → ℝ} (hc : Certificate K B h) (s : S) :
    0 ≤ h s - indicator B.Win s ∧
      h s - indicator B.Win s ≤ transientIndicator B s := by
  by_cases hw : B.Win s
  · have he := hc.win s hw
    simp [he, indicator, hw, transientIndicator, Boundary.Terminal]
  · by_cases hl : B.Loss s
    · have he := hc.loss s hl
      simp [he, indicator, hw, transientIndicator, Boundary.Terminal, hl]
    · simpa [indicator, hw, transientIndicator, Boundary.Terminal, hl] using hc.bounds s

theorem certificate_error_bound (K : Kernel S) (B : Boundary S)
    {h : S → ℝ} (hc : Certificate K B h) (start : S) (n : ℕ) :
    0 ≤ h start - winProbability K B start n ∧
      h start - winProbability K B start n ≤ transientMass K B start n := by
  have he : expect (marginal K start n) (fun s => h s - indicator B.Win s) =
      h start - winProbability K B start n := by
    rw [expect_sub, harmonic_expectation K start h hc.harmonic n]
    rfl
  constructor
  · rw [← he]
    exact expect_nonneg (marginal_nonneg K start n)
      (fun s => (certificate_pointwise_error K B hc s).1)
  · rw [← he]
    exact expect_mono (marginal_nonneg K start n)
      (fun s => (certificate_pointwise_error K B hc s).2)

theorem win_probability_error (K : Kernel S) (B : Boundary S)
    (ha : Absorbing K B) {ε : ℝ} (hε1 : ε ≤ 1) (hu : UniformTerminal K B ε)
    {h : S → ℝ} (hc : Certificate K B h) (start : S) (n : ℕ) :
    |winProbability K B start n - h start| ≤ (1-ε)^n := by
  have hb := certificate_error_bound K B hc start n
  rw [abs_of_nonpos (by linarith [hb.1])]
  have hg := transient_mass_geometric K B ha hε1 hu start n
  linarith [hb.2]

/-- Epsilon convergence of the actual finite-time win probabilities. -/
def WinConverges (K : Kernel S) (B : Boundary S) (h : S → ℝ) : Prop :=
  ∀ start, ∀ δ : ℝ, 0 < δ → ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
    |winProbability K B start n - h start| < δ

theorem certificate_identifies_limit (K : Kernel S) (B : Boundary S)
    (ha : Absorbing K B) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hu : UniformTerminal K B ε) {h : S → ℝ} (hc : Certificate K B h) :
    WinConverges K B h := by
  intro start δ hδ
  have hq0 : 0 ≤ 1-ε := by linarith
  have hq1 : 1-ε < 1 := by linarith
  obtain ⟨n₀, hn₀⟩ := exists_pow_lt_of_lt_one hδ hq1
  refine ⟨n₀, fun n hn => ?_⟩
  have hp : (1-ε)^n ≤ (1-ε)^n₀ := pow_le_pow_of_le_one hq0 hq1.le hn
  exact (win_probability_error K B ha hε1 hu hc start n).trans_lt (hp.trans_lt hn₀)

/-- Finite-time transient mass tends to zero, independently of a certificate. -/
theorem transient_mass_vanishes (K : Kernel S) (B : Boundary S)
    (ha : Absorbing K B) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hu : UniformTerminal K B ε) (start : S) :
    ∀ δ : ℝ, 0 < δ → ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      0 ≤ transientMass K B start n ∧ transientMass K B start n < δ := by
  intro δ hδ
  have hq0 : 0 ≤ 1-ε := by linarith
  have hq1 : 1-ε < 1 := by linarith
  obtain ⟨n₀, hn₀⟩ := exists_pow_lt_of_lt_one hδ hq1
  refine ⟨n₀, fun n hn => ⟨transient_mass_nonneg K B start n, ?_⟩⟩
  have hp : (1-ε)^n ≤ (1-ε)^n₀ := pow_le_pow_of_le_one hq0 hq1.le hn
  exact (transient_mass_geometric K B ha hε1 hu start n).trans_lt (hp.trans_lt hn₀)

/-- Finite conditioning on the state produced by a one-off initial pulse. -/
def winProbabilityFrom (K : Kernel S) (B : Boundary S) (μ : S → ℝ) (n : ℕ) : ℝ :=
  expect μ (fun start => winProbability K B start n)

theorem expect_constant (μ : S → ℝ) (c : ℝ) :
    expect μ (fun _ => c) = (∑ s, μ s) * c := by
  exact (Finset.sum_mul Finset.univ μ c).symm

/-- Averaging the signed pointwise error retains the same geometric rate. -/
theorem certificate_mixture_error (K : Kernel S) (B : Boundary S)
    (ha : Absorbing K B) {ε : ℝ} (hε1 : ε ≤ 1) (hu : UniformTerminal K B ε)
    {h : S → ℝ} (hc : Certificate K B h) (μ : S → ℝ)
    (hμ : ∀ s, 0 ≤ μ s) (hμtotal : ∑ s, μ s = 1) (n : ℕ) :
    0 ≤ expect μ h - winProbabilityFrom K B μ n ∧
      expect μ h - winProbabilityFrom K B μ n ≤ (1-ε)^n := by
  have he : expect μ (fun s => h s - winProbability K B s n) =
      expect μ h - winProbabilityFrom K B μ n := by
    rw [expect_sub]
    rfl
  have hb : ∀ s, h s - winProbability K B s n ≤ (1-ε)^n := by
    intro s
    exact (certificate_error_bound K B hc s n).2.trans
      (transient_mass_geometric K B ha hε1 hu s n)
  constructor
  · rw [← he]
    exact expect_nonneg hμ (fun s => (certificate_error_bound K B hc s n).1)
  · rw [← he]
    calc
      _ ≤ expect μ (fun _ => (1-ε)^n) := expect_mono hμ hb
      _ = (1-ε)^n := by rw [expect_constant, hμtotal, one_mul]

theorem win_probability_from_error (K : Kernel S) (B : Boundary S)
    (ha : Absorbing K B) {ε : ℝ} (hε1 : ε ≤ 1) (hu : UniformTerminal K B ε)
    {h : S → ℝ} (hc : Certificate K B h) (μ : S → ℝ)
    (hμ : ∀ s, 0 ≤ μ s) (hμtotal : ∑ s, μ s = 1) (n : ℕ) :
    |winProbabilityFrom K B μ n - expect μ h| ≤ (1-ε)^n := by
  have hb := certificate_mixture_error K B ha hε1 hu hc μ hμ hμtotal n
  rw [abs_of_nonpos (by linarith [hb.1])]
  linarith [hb.2]

/-- Exact certificate average as the limit of finite-time pulse-start probabilities. -/
theorem certificate_identifies_mixture_limit (K : Kernel S) (B : Boundary S)
    (ha : Absorbing K B) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hu : UniformTerminal K B ε) {h : S → ℝ} (hc : Certificate K B h)
    (μ : S → ℝ) (hμ : ∀ s, 0 ≤ μ s) (hμtotal : ∑ s, μ s = 1) :
    ∀ δ : ℝ, 0 < δ → ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      |winProbabilityFrom K B μ n - expect μ h| < δ := by
  intro δ hδ
  have hq0 : 0 ≤ 1-ε := by linarith
  have hq1 : 1-ε < 1 := by linarith
  obtain ⟨n₀, hn₀⟩ := exists_pow_lt_of_lt_one hδ hq1
  refine ⟨n₀, fun n hn => ?_⟩
  have hp : (1-ε)^n ≤ (1-ε)^n₀ := pow_le_pow_of_le_one hq0 hq1.le hn
  exact (win_probability_from_error K B ha hε1 hu hc μ hμ hμtotal n).trans_lt
    (hp.trans_lt hn₀)
end
end FiniteFixation

#print axioms FiniteFixation.marginal_nonneg
#print axioms FiniteFixation.marginal_total
#print axioms FiniteFixation.harmonic_expectation
#print axioms FiniteFixation.transient_mass_geometric
#print axioms FiniteFixation.certificate_error_bound
#print axioms FiniteFixation.win_probability_error
#print axioms FiniteFixation.certificate_identifies_limit
#print axioms FiniteFixation.transient_mass_vanishes



#print axioms FiniteFixation.certificate_mixture_error
#print axioms FiniteFixation.win_probability_from_error
#print axioms FiniteFixation.certificate_identifies_mixture_limit
