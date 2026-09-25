import FogartyAffinity
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-! A quantitative fixation refinement for the published affinity-bias model.
The trajectory is required to satisfy the four source recursions, not an
assumed odds contraction. An initial odds bound is explicit; beneficial
culture in both genetic backgrounds suffices to obtain such a bound.
-/
namespace FogartyAffinity

def OddsBound (x : Frequencies) (r : ℝ) : Prop :=
  0 ≤ r ∧ x.x2 ≤ r*x.x1 ∧ x.x4 ≤ r*x.x3

theorem transmit_margin_one {x : Frequencies} (hx : Simplex x) (r b₁ b₂ : ℝ) :
    r*(transmit x b₁ b₂).x1-(transmit x b₁ b₂).x2 =
      (1-b₁*(1-p x))*(r*x.x1-x.x2) + b₁*p x*(r*x.x3-x.x4) := by
  have h4 : x.x4 = 1-x.x1-x.x2-x.x3 := by linarith [hx.total]
  dsimp [transmit, association, p]
  rw [h4]
  ring

theorem transmit_margin_two {x : Frequencies} (hx : Simplex x) (r b₁ b₂ : ℝ) :
    r*(transmit x b₁ b₂).x3-(transmit x b₁ b₂).x4 =
      (1-b₂*p x)*(r*x.x3-x.x4) + b₂*(1-p x)*(r*x.x1-x.x2) := by
  have h4 : x.x4 = 1-x.x1-x.x2-x.x3 := by linarith [hx.total]
  dsimp [transmit, association, p]
  rw [h4]
  ring

theorem transmit_preserves_odds {x : Frequencies} {r b₁ b₂ : ℝ}
    (hx : Simplex x) (hb₁ : 0 ≤ b₁ ∧ b₁ ≤ 1) (hb₂ : 0 ≤ b₂ ∧ b₂ ≤ 1)
    (hr : OddsBound x r) : OddsBound (transmit x b₁ b₂) r := by
  have hp := marginal_bounds hx
  have ha : 0 ≤ 1-b₁*(1-p x) := by
    nlinarith [mul_nonneg hb₁.1 hp.1, hb₁.2]
  have hb : 0 ≤ b₁*p x := mul_nonneg hb₁.1 hp.1
  have hc : 0 ≤ 1-b₂*p x := by
    nlinarith [mul_nonneg hb₂.1 (show 0 ≤ 1-p x by linarith [hp.2.1]), hb₂.2]
  have hd : 0 ≤ b₂*(1-p x) :=
    mul_nonneg hb₂.1 (by linarith [hp.2.1])
  have he : 0 ≤ r*x.x1-x.x2 := by linarith [hr.2.1]
  have hf : 0 ≤ r*x.x3-x.x4 := by linarith [hr.2.2]
  have h1 := add_nonneg (mul_nonneg ha he) (mul_nonneg hb hf)
  have h2 := add_nonneg (mul_nonneg hc hf) (mul_nonneg hd he)
  rw [← transmit_margin_one hx r b₁ b₂] at h1
  rw [← transmit_margin_two hx r b₁ b₂] at h2
  exact ⟨hr.1, by linarith, by linarith⟩

theorem source_contracts_odds {x y : Frequencies} {s r b₁ b₂ : ℝ}
    (hx : Simplex x) (hs : 0 ≤ s)
    (hb₁ : 0 ≤ b₁ ∧ b₁ ≤ 1) (hb₂ : 0 ≤ b₂ ∧ b₂ ≤ 1)
    (hr : OddsBound x r) (h : SourceRecursions x y s b₁ b₂) :
    OddsBound y (r/(1+s)) := by
  have hw := normalizer_pos hx hs hb₁ hb₂
  have hs1 : 0 < 1+s := by linarith
  have ht := transmit_preserves_odds hx hb₁ hb₂ hr
  rcases h with ⟨h1, h2, h3, h4⟩
  refine ⟨div_nonneg hr.1 hs1.le, ?_, ?_⟩
  · have hbound : normalizer x s b₁ b₂*((1+s)*y.x2) ≤
        normalizer x s b₁ b₂*(r*y.x1) := by
      calc
        _ = (1+s)*(normalizer x s b₁ b₂*y.x2) := by ring
        _ = (1+s)*(transmit x b₁ b₂).x2 := by rw [h2]
        _ ≤ (1+s)*(r*(transmit x b₁ b₂).x1) :=
          mul_le_mul_of_nonneg_left ht.2.1 hs1.le
        _ = r*(normalizer x s b₁ b₂*y.x1) := by rw [h1]; ring
        _ = normalizer x s b₁ b₂*(r*y.x1) := by ring
    have hc := le_of_mul_le_mul_left hbound hw
    calc
      y.x2 ≤ (r*y.x1)/(1+s) := (le_div_iff₀ hs1).2 (by nlinarith [hc])
      _ = r/(1+s)*y.x1 := by ring
  · have hbound : normalizer x s b₁ b₂*((1+s)*y.x4) ≤
        normalizer x s b₁ b₂*(r*y.x3) := by
      calc
        _ = (1+s)*(normalizer x s b₁ b₂*y.x4) := by ring
        _ = (1+s)*(transmit x b₁ b₂).x4 := by rw [h4]
        _ ≤ (1+s)*(r*(transmit x b₁ b₂).x3) :=
          mul_le_mul_of_nonneg_left ht.2.2 hs1.le
        _ = r*(normalizer x s b₁ b₂*y.x3) := by rw [h3]; ring
        _ = normalizer x s b₁ b₂*(r*y.x3) := by ring
    have hc := le_of_mul_le_mul_left hbound hw
    calc
      y.x4 ≤ (r*y.x3)/(1+s) := (le_div_iff₀ hs1).2 (by nlinarith [hc])
      _ = r/(1+s)*y.x3 := by ring

theorem trajectory_simplex {X : ℕ → Frequencies} {s : ℝ} {b₁ b₂ : ℕ → ℝ}
    (h0 : Simplex (X 0)) (hs : 0 ≤ s)
    (hb₁ : ∀ n, 0 ≤ b₁ n ∧ b₁ n ≤ 1) (hb₂ : ∀ n, 0 ≤ b₂ n ∧ b₂ n ≤ 1)
    (hstep : ∀ n, SourceRecursions (X n) (X (n+1)) s (b₁ n) (b₂ n)) :
    ∀ n, Simplex (X n) := by
  intro n
  induction n with
  | zero => exact h0
  | succ n ih => exact source_preserves_simplex ih hs (hb₁ n) (hb₂ n) (hstep n)

theorem trajectory_odds_bound {X : ℕ → Frequencies} {s r : ℝ} {b₁ b₂ : ℕ → ℝ}
    (h0 : Simplex (X 0)) (hs : 0 ≤ s)
    (hb₁ : ∀ n, 0 ≤ b₁ n ∧ b₁ n ≤ 1) (hb₂ : ∀ n, 0 ≤ b₂ n ∧ b₂ n ≤ 1)
    (hr : OddsBound (X 0) r)
    (hstep : ∀ n, SourceRecursions (X n) (X (n+1)) s (b₁ n) (b₂ n)) :
    ∀ n, OddsBound (X n) (r/(1+s)^n) := by
  intro n
  induction n with
  | zero => simpa using hr
  | succ n ih =>
    have hc := source_contracts_odds
      (trajectory_simplex h0 hs hb₁ hb₂ hstep n) hs (hb₁ n) (hb₂ n) ih (hstep n)
    simpa only [pow_succ, div_div] using hc

theorem odds_deficit_sharp {x : Frequencies} {r : ℝ}
    (hx : Simplex x) (hr : OddsBound x r) :
    1-q x ≤ r/(1+r) := by
  have hsum : 1-q x = x.x2+x.x4 := by dsimp [q]; linarith [hx.total]
  have hbound : 1-q x ≤ r*q x := by
    rw [hsum]
    dsimp [q]
    nlinarith [hr.2.1, hr.2.2]
  apply (le_div_iff₀ (show 0 < 1+r by linarith [hr.1])).2
  nlinarith [hbound]

theorem odds_deficit {x : Frequencies} {r : ℝ}
    (hx : Simplex x) (hr : OddsBound x r) :
    0 ≤ 1-q x ∧ 1-q x ≤ r := by
  have hm := marginal_bounds hx
  have hb := odds_deficit_sharp hx hr
  have hden : 0 < 1+r := by linarith [hr.1]
  have hupper : r/(1+r) ≤ r := by
    apply (div_le_iff₀ hden).2
    nlinarith [sq_nonneg r]
  exact ⟨by linarith [hm.2.2.2], hb.trans hupper⟩

theorem trajectory_deficit {X : ℕ → Frequencies} {s r : ℝ} {b₁ b₂ : ℕ → ℝ}
    (h0 : Simplex (X 0)) (hs : 0 ≤ s)
    (hb₁ : ∀ n, 0 ≤ b₁ n ∧ b₁ n ≤ 1) (hb₂ : ∀ n, 0 ≤ b₂ n ∧ b₂ n ≤ 1)
    (hr : OddsBound (X 0) r)
    (hstep : ∀ n, SourceRecursions (X n) (X (n+1)) s (b₁ n) (b₂ n)) (n : ℕ) :
    0 ≤ 1-q (X n) ∧ 1-q (X n) ≤ r/(1+s)^n :=
  odds_deficit (trajectory_simplex h0 hs hb₁ hb₂ hstep n)
    (trajectory_odds_bound h0 hs hb₁ hb₂ hr hstep n)

/-- A precise epsilon formulation of q_n tending to one. -/
def CultureFixates (X : ℕ → Frequencies) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n, N ≤ n → |q (X n)-1| < ε

theorem trajectory_fixates {X : ℕ → Frequencies} {s r : ℝ} {b₁ b₂ : ℕ → ℝ}
    (h0 : Simplex (X 0)) (hs : 0 < s)
    (hb₁ : ∀ n, 0 ≤ b₁ n ∧ b₁ n ≤ 1) (hb₂ : ∀ n, 0 ≤ b₂ n ∧ b₂ n ≤ 1)
    (hr : OddsBound (X 0) r)
    (hstep : ∀ n, SourceRecursions (X n) (X (n+1)) s (b₁ n) (b₂ n)) :
    CultureFixates X := by
  intro ε hε
  let ρ : ℝ := 1/(1+s)
  have hs1 : 0 < 1+s := by linarith
  have hρ0 : 0 ≤ ρ := div_nonneg (by norm_num) hs1.le
  have hρ1 : ρ < 1 := (div_lt_one hs1).2 (by linarith)
  have hr1 : 0 < r+1 := by linarith [hr.1]
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos hε hr1) hρ1
  refine ⟨N, fun n hn => ?_⟩
  have hpow : ρ^n ≤ ρ^N := pow_le_pow_of_le_one hρ0 hρ1.le hn
  have hN' : ρ^N*(r+1) < ε := (lt_div_iff₀ hr1).mp hN
  have hrN : ρ^N*r ≤ ρ^N*(r+1) :=
    mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg hρ0 N)
  have hsmall : ρ^n*r < ε :=
    (mul_le_mul_of_nonneg_right hpow hr.1).trans_lt (hrN.trans_lt hN')
  have hd := trajectory_deficit h0 hs.le hb₁ hb₂ hr hstep n
  have heq : r/(1+s)^n = ρ^n*r := by
    dsimp [ρ]
    rw [div_pow]
    simp only [one_pow]
    ring
  have habs : |q (X n)-1| = 1-q (X n) := by
    rw [abs_of_nonpos (by linarith [hd.1])]
    ring
  rw [habs]
  exact hd.2.trans_lt (by simpa only [heq] using hsmall)

noncomputable def initialOdds (x : Frequencies) : ℝ :=
  max (x.x2/x.x1) (x.x4/x.x3)

theorem positive_backgrounds_odds {x : Frequencies} (hx : Simplex x)
    (h1 : 0 < x.x1) (h3 : 0 < x.x3) :
    OddsBound x (initialOdds x) := by
  refine ⟨?_, ?_, ?_⟩
  · exact (div_nonneg hx.nonneg2 h1.le).trans (le_max_left _ _)
  · exact (div_le_iff₀ h1).mp (le_max_left _ _)
  · exact (div_le_iff₀ h3).mp (le_max_right _ _)

theorem positive_backgrounds_fixation {X : ℕ → Frequencies} {s : ℝ} {b₁ b₂ : ℕ → ℝ}
    (h0 : Simplex (X 0)) (hs : 0 < s)
    (hb₁ : ∀ n, 0 ≤ b₁ n ∧ b₁ n ≤ 1) (hb₂ : ∀ n, 0 ≤ b₂ n ∧ b₂ n ≤ 1)
    (h1 : 0 < (X 0).x1) (h3 : 0 < (X 0).x3)
    (hstep : ∀ n, SourceRecursions (X n) (X (n+1)) s (b₁ n) (b₂ n)) :
    (∀ n, 0 ≤ 1-q (X n) ∧
      1-q (X n) ≤ initialOdds (X 0)/(1+s)^n) ∧ CultureFixates X :=
  ⟨trajectory_deficit h0 hs.le hb₁ hb₂ (positive_backgrounds_odds h0 h1 h3) hstep,
   trajectory_fixates h0 hs hb₁ hb₂ (positive_backgrounds_odds h0 h1 h3) hstep⟩

noncomputable def evolve (x : Frequencies) (s : ℝ) (b₁ b₂ : ℕ → ℝ) : ℕ → Frequencies
  | 0 => x
  | n+1 => step (evolve x s b₁ b₂ n) s (b₁ n) (b₂ n)

theorem evolve_simplex {x : Frequencies} {s : ℝ} {b₁ b₂ : ℕ → ℝ}
    (hx : Simplex x) (hs : 0 ≤ s)
    (hb₁ : ∀ n, 0 ≤ b₁ n ∧ b₁ n ≤ 1) (hb₂ : ∀ n, 0 ≤ b₂ n ∧ b₂ n ≤ 1) :
    ∀ n, Simplex (evolve x s b₁ b₂ n) := by
  intro n
  induction n with
  | zero => exact hx
  | succ n ih => exact step_preserves_simplex ih hs (hb₁ n) (hb₂ n)

theorem evolve_recursions {x : Frequencies} {s : ℝ} {b₁ b₂ : ℕ → ℝ}
    (hx : Simplex x) (hs : 0 ≤ s)
    (hb₁ : ∀ n, 0 ≤ b₁ n ∧ b₁ n ≤ 1) (hb₂ : ∀ n, 0 ≤ b₂ n ∧ b₂ n ≤ 1) (n : ℕ) :
    SourceRecursions (evolve x s b₁ b₂ n) (evolve x s b₁ b₂ (n+1)) s (b₁ n) (b₂ n) :=
  step_recursions (ne_of_gt (normalizer_pos (evolve_simplex hx hs hb₁ hb₂ n) hs (hb₁ n) (hb₂ n)))

/-- An actual recursively defined model, rather than only a conditional trajectory. -/
theorem model_global_fixation {x : Frequencies} {s : ℝ} {b₁ b₂ : ℕ → ℝ}
    (hx : Simplex x) (hs : 0 < s)
    (hb₁ : ∀ n, 0 ≤ b₁ n ∧ b₁ n ≤ 1) (hb₂ : ∀ n, 0 ≤ b₂ n ∧ b₂ n ≤ 1)
    (h1 : 0 < x.x1) (h3 : 0 < x.x3) :
    (∀ n, 0 ≤ 1-q (evolve x s b₁ b₂ n) ∧
      1-q (evolve x s b₁ b₂ n) ≤ initialOdds x/(1+s)^n) ∧
    CultureFixates (evolve x s b₁ b₂) :=
  positive_backgrounds_fixation hx hs hb₁ hb₂ h1 h3 (evolve_recursions hx hs.le hb₁ hb₂)

end FogartyAffinity

#print axioms FogartyAffinity.transmit_margin_one
#print axioms FogartyAffinity.transmit_margin_two
#print axioms FogartyAffinity.source_contracts_odds
#print axioms FogartyAffinity.trajectory_odds_bound
#print axioms FogartyAffinity.odds_deficit_sharp
#print axioms FogartyAffinity.trajectory_deficit
#print axioms FogartyAffinity.trajectory_fixates
#print axioms FogartyAffinity.positive_backgrounds_fixation
#print axioms FogartyAffinity.model_global_fixation



