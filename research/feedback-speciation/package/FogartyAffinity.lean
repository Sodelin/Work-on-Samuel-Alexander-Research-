import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
The affinity-bias model in Fogarty, Zhang and Feldman (2025),
doi:10.1016/j.tpb.2025.08.003, Table 2 and equations (17)--(23).

The four fields are frequencies of AB, Ab, aB, ab. The results start from
the four source recursions. No convergence, species predicate, empirical
claim, or assumption that the desired drift identity holds is included.
-/
namespace FogartyAffinity

structure Frequencies where
  x1 : ℝ
  x2 : ℝ
  x3 : ℝ
  x4 : ℝ

structure Simplex (x : Frequencies) : Prop where
  nonneg1 : 0 ≤ x.x1
  nonneg2 : 0 ≤ x.x2
  nonneg3 : 0 ≤ x.x3
  nonneg4 : 0 ≤ x.x4
  total : x.x1 + x.x2 + x.x3 + x.x4 = 1

noncomputable def p (x : Frequencies) : ℝ := x.x1 + x.x2
noncomputable def q (x : Frequencies) : ℝ := x.x1 + x.x3
noncomputable def association (x : Frequencies) : ℝ := x.x1*x.x4 - x.x2*x.x3
noncomputable def transmit (x : Frequencies) (b₁ b₂ : ℝ) : Frequencies :=
  ⟨x.x1-b₁*association x, x.x2+b₁*association x,
   x.x3+b₂*association x, x.x4-b₂*association x⟩
noncomputable def z (x : Frequencies) (b₁ b₂ : ℝ) : ℝ :=
  q x + (b₂-b₁)*association x
noncomputable def normalizer (x : Frequencies) (s b₁ b₂ : ℝ) : ℝ :=
  1+s*z x b₁ b₂
noncomputable def k (x : Frequencies) (b₁ b₂ : ℝ) : ℝ :=
  1-b₁*(1-p x)-b₂*p x

/-- Source equations, without dividing by the normalizer. -/
def SourceRecursions (x y : Frequencies) (s b₁ b₂ : ℝ) : Prop :=
  normalizer x s b₁ b₂*y.x1 = (1+s)*(transmit x b₁ b₂).x1 ∧
  normalizer x s b₁ b₂*y.x2 = (transmit x b₁ b₂).x2 ∧
  normalizer x s b₁ b₂*y.x3 = (1+s)*(transmit x b₁ b₂).x3 ∧
  normalizer x s b₁ b₂*y.x4 = (transmit x b₁ b₂).x4

/-- The uniquely normalized update in the admissible parameter range. -/
noncomputable def step (x : Frequencies) (s b₁ b₂ : ℝ) : Frequencies :=
  ⟨(1+s)*(transmit x b₁ b₂).x1 / normalizer x s b₁ b₂,
   (transmit x b₁ b₂).x2 / normalizer x s b₁ b₂,
   (1+s)*(transmit x b₁ b₂).x3 / normalizer x s b₁ b₂,
   (transmit x b₁ b₂).x4 / normalizer x s b₁ b₂⟩

theorem marginal_bounds {x : Frequencies} (hx : Simplex x) :
    0 ≤ p x ∧ p x ≤ 1 ∧ 0 ≤ q x ∧ q x ≤ 1 := by
  dsimp [p, q]
  constructor
  · linarith [hx.nonneg1, hx.nonneg2]
  constructor
  · linarith [hx.total, hx.nonneg3, hx.nonneg4]
  constructor
  · linarith [hx.nonneg1, hx.nonneg3]
  · linarith [hx.total, hx.nonneg2, hx.nonneg4]

theorem association_eq {x : Frequencies} (hx : Simplex x) :
    association x = x.x1-p x*q x := by
  have h := congrArg (fun t : ℝ => x.x1*t) hx.total
  dsimp [association, p, q]
  nlinarith [h]

theorem transmit_q (x : Frequencies) (b₁ b₂ : ℝ) :
    (transmit x b₁ b₂).x1 + (transmit x b₁ b₂).x3 = z x b₁ b₂ := by
  dsimp [transmit, z, q]
  ring

theorem transmit_simplex {x : Frequencies} {b₁ b₂ : ℝ}
    (hx : Simplex x) (hb₁ : 0 ≤ b₁ ∧ b₁ ≤ 1) (hb₂ : 0 ≤ b₂ ∧ b₂ ≤ 1) :
    Simplex (transmit x b₁ b₂) := by
  have hx1 : x.x1 ≤ 1 := by
    linarith [hx.total, hx.nonneg2, hx.nonneg3, hx.nonneg4]
  have hx2 : x.x2 ≤ 1 := by
    linarith [hx.total, hx.nonneg1, hx.nonneg3, hx.nonneg4]
  have hx3 : x.x3 ≤ 1 := by
    linarith [hx.total, hx.nonneg1, hx.nonneg2, hx.nonneg4]
  have hx4 : x.x4 ≤ 1 := by
    linarith [hx.total, hx.nonneg1, hx.nonneg2, hx.nonneg3]
  have hD1 : 0 ≤ x.x1-association x := by
    dsimp [association]
    nlinarith [mul_nonneg hx.nonneg1 (show 0 ≤ 1-x.x4 by linarith),
      mul_nonneg hx.nonneg2 hx.nonneg3]
  have hD4 : 0 ≤ x.x4-association x := by
    dsimp [association]
    nlinarith [mul_nonneg hx.nonneg4 (show 0 ≤ 1-x.x1 by linarith),
      mul_nonneg hx.nonneg2 hx.nonneg3]
  have hD2 : 0 ≤ x.x2+association x := by
    dsimp [association]
    nlinarith [mul_nonneg hx.nonneg2 (show 0 ≤ 1-x.x3 by linarith),
      mul_nonneg hx.nonneg1 hx.nonneg4]
  have hD3 : 0 ≤ x.x3+association x := by
    dsimp [association]
    nlinarith [mul_nonneg hx.nonneg3 (show 0 ≤ 1-x.x2 by linarith),
      mul_nonneg hx.nonneg1 hx.nonneg4]
  have htotal : (transmit x b₁ b₂).x1 + (transmit x b₁ b₂).x2 +
      (transmit x b₁ b₂).x3 + (transmit x b₁ b₂).x4 = 1 := by
    dsimp [transmit]
    linarith [hx.total]
  rcases le_total 0 (association x) with hD | hD
  · refine ⟨?_, ?_, ?_, ?_, htotal⟩
    · dsimp [transmit]
      nlinarith [mul_nonneg (show 0 ≤ 1-b₁ by linarith [hb₁.2]) hD]
    · dsimp [transmit]
      exact add_nonneg hx.nonneg2 (mul_nonneg hb₁.1 hD)
    · dsimp [transmit]
      exact add_nonneg hx.nonneg3 (mul_nonneg hb₂.1 hD)
    · dsimp [transmit]
      nlinarith [mul_nonneg (show 0 ≤ 1-b₂ by linarith [hb₂.2]) hD]
  · refine ⟨?_, ?_, ?_, ?_, htotal⟩
    · dsimp [transmit]
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hb₁.1 hD, hx.nonneg1]
    · dsimp [transmit]
      nlinarith [mul_nonpos_of_nonneg_of_nonpos
        (show 0 ≤ 1-b₁ by linarith [hb₁.2]) hD]
    · dsimp [transmit]
      nlinarith [mul_nonpos_of_nonneg_of_nonpos
        (show 0 ≤ 1-b₂ by linarith [hb₂.2]) hD]
    · dsimp [transmit]
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hb₂.1 hD, hx.nonneg4]

theorem normalizer_pos {x : Frequencies} {s b₁ b₂ : ℝ}
    (hx : Simplex x) (hs : 0 ≤ s)
    (hb₁ : 0 ≤ b₁ ∧ b₁ ≤ 1) (hb₂ : 0 ≤ b₂ ∧ b₂ ≤ 1) :
    0 < normalizer x s b₁ b₂ := by
  have ht := transmit_simplex hx hb₁ hb₂
  have hz : 0 ≤ z x b₁ b₂ := by
    rw [← transmit_q]
    exact add_nonneg ht.nonneg1 ht.nonneg3
  dsimp [normalizer]
  nlinarith [mul_nonneg hs hz]

theorem step_recursions {x : Frequencies} {s b₁ b₂ : ℝ}
    (hw : normalizer x s b₁ b₂ ≠ 0) :
    SourceRecursions x (step x s b₁ b₂) s b₁ b₂ := by
  dsimp [SourceRecursions, step]
  constructor
  · field_simp
  constructor
  · field_simp
  constructor <;> field_simp

theorem q_update_mul {x y : Frequencies} {s b₁ b₂ : ℝ}
    (h : SourceRecursions x y s b₁ b₂) :
    normalizer x s b₁ b₂*q y = (1+s)*z x b₁ b₂ := by
  rcases h with ⟨h1, h2, h3, h4⟩
  calc
    normalizer x s b₁ b₂*q y =
        normalizer x s b₁ b₂*y.x1 + normalizer x s b₁ b₂*y.x3 := by
      dsimp [q]; ring
    _ = (1+s)*((transmit x b₁ b₂).x1+(transmit x b₁ b₂).x3) := by
      rw [h1, h3]; ring
    _ = (1+s)*z x b₁ b₂ := by rw [transmit_q]

theorem source_preserves_simplex {x y : Frequencies} {s b₁ b₂ : ℝ}
    (hx : Simplex x) (hs : 0 ≤ s)
    (hb₁ : 0 ≤ b₁ ∧ b₁ ≤ 1) (hb₂ : 0 ≤ b₂ ∧ b₂ ≤ 1)
    (h : SourceRecursions x y s b₁ b₂) : Simplex y := by
  have hw := normalizer_pos hx hs hb₁ hb₂
  have ht := transmit_simplex hx hb₁ hb₂
  rcases h with ⟨h1, h2, h3, h4⟩
  have hsum : normalizer x s b₁ b₂*(y.x1+y.x2+y.x3+y.x4) =
      normalizer x s b₁ b₂ := by
    calc
      _ = normalizer x s b₁ b₂*y.x1 + normalizer x s b₁ b₂*y.x2 +
          normalizer x s b₁ b₂*y.x3 + normalizer x s b₁ b₂*y.x4 := by ring
      _ = (1+s)*(transmit x b₁ b₂).x1 + (transmit x b₁ b₂).x2 +
          (1+s)*(transmit x b₁ b₂).x3 + (transmit x b₁ b₂).x4 := by
        rw [h1, h2, h3, h4]
      _ = 1+s*((transmit x b₁ b₂).x1+(transmit x b₁ b₂).x3) := by
        nlinarith [ht.total]
      _ = normalizer x s b₁ b₂ := by rw [transmit_q]; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hp := mul_nonneg (show 0 ≤ 1+s by linarith) ht.nonneg1
    rw [← h1] at hp
    exact nonneg_of_mul_nonneg_right hp hw
  · have hp := ht.nonneg2
    rw [← h2] at hp
    exact nonneg_of_mul_nonneg_right hp hw
  · have hp := mul_nonneg (show 0 ≤ 1+s by linarith) ht.nonneg3
    rw [← h3] at hp
    exact nonneg_of_mul_nonneg_right hp hw
  · have hp := ht.nonneg4
    rw [← h4] at hp
    exact nonneg_of_mul_nonneg_right hp hw
  · nlinarith [hsum]

theorem step_preserves_simplex {x : Frequencies} {s b₁ b₂ : ℝ}
    (hx : Simplex x) (hs : 0 ≤ s)
    (hb₁ : 0 ≤ b₁ ∧ b₁ ≤ 1) (hb₂ : 0 ≤ b₂ ∧ b₂ ≤ 1) :
    Simplex (step x s b₁ b₂) :=
  source_preserves_simplex hx hs hb₁ hb₂
    (step_recursions (ne_of_gt (normalizer_pos hx hs hb₁ hb₂)))

theorem p_drift_mul {x y : Frequencies} {s b₁ b₂ : ℝ}
    (hx : Simplex x) (h : SourceRecursions x y s b₁ b₂) :
    normalizer x s b₁ b₂*(p y-p x) = s*association x*k x b₁ b₂ := by
  rcases h with ⟨h1, h2, h3, h4⟩
  have hp : normalizer x s b₁ b₂*p y =
      p x+s*(x.x1-b₁*association x) := by
    dsimp [p, transmit] at h1 h2 ⊢
    nlinarith [h1, h2]
  rw [mul_sub, hp]
  dsimp [normalizer, z, k]
  rw [association_eq hx]
  ring

theorem p_drift {x y : Frequencies} {s b₁ b₂ : ℝ}
    (hx : Simplex x) (hs : 0 ≤ s)
    (hb₁ : 0 ≤ b₁ ∧ b₁ ≤ 1) (hb₂ : 0 ≤ b₂ ∧ b₂ ≤ 1)
    (h : SourceRecursions x y s b₁ b₂) :
    p y-p x = s*association x*k x b₁ b₂ / normalizer x s b₁ b₂ := by
  apply (eq_div_iff (ne_of_gt (normalizer_pos hx hs hb₁ hb₂))).2
  simpa only [mul_comm] using p_drift_mul hx h

/-- Source-faithful theorem: all genetic and cultural copying probabilities
are allowed. Fixedness is the four source equations with y=x. -/
theorem no_polymorphic_fixed_point {x : Frequencies} {s b₁ b₂ : ℝ}
    (hx : Simplex x) (hs : 0 < s)
    (hb₁ : 0 ≤ b₁ ∧ b₁ ≤ 1) (hb₂ : 0 ≤ b₂ ∧ b₂ ≤ 1)
    (hp : 0 < p x ∧ p x < 1) (hq : 0 < q x ∧ q x < 1)
    (h : SourceRecursions x x s b₁ b₂) : False := by
  have hproduct : s*association x*k x b₁ b₂ = 0 := by
    have hd := p_drift_mul hx h
    simpa only [sub_self, mul_zero] using hd.symm
  have hka : 0 ≤ (1-p x)*(1-b₁) :=
    mul_nonneg (by linarith [hp.2]) (by linarith [hb₁.2])
  have hkb : 0 ≤ p x*(1-b₂) :=
    mul_nonneg (le_of_lt hp.1) (by linarith [hb₂.2])
  have hk : k x b₁ b₂ = (1-p x)*(1-b₁)+p x*(1-b₂) := by
    dsimp [k]; ring
  have hdelta : (b₂-b₁)*association x = 0 := by
    by_cases hk0 : k x b₁ b₂ = 0
    · have ha : (1-p x)*(1-b₁) = 0 := by rw [hk] at hk0; linarith
      have hb : p x*(1-b₂) = 0 := by rw [hk] at hk0; linarith
      have h1 : b₁ = 1 := by
        rcases mul_eq_zero.mp ha with ha | ha <;> linarith [hp.2]
      have h2 : b₂ = 1 := by
        rcases mul_eq_zero.mp hb with hb | hb <;> linarith [hp.1]
      rw [h1, h2]; ring
    · have hsd : s*association x = 0 :=
        (mul_eq_zero.mp hproduct).resolve_right hk0
      have hD : association x = 0 :=
        (mul_eq_zero.mp hsd).resolve_left (ne_of_gt hs)
      rw [hD]; ring
  have hz : z x b₁ b₂ = q x := by dsimp [z]; rw [hdelta]; ring
  have hqrec := q_update_mul h
  rw [hz] at hqrec
  have hw : normalizer x s b₁ b₂ = 1+s*q x := by
    dsimp [normalizer]; rw [hz]
  rw [hw] at hqrec
  have hstrict : 0 < s*q x*(1-q x) :=
    mul_pos (mul_pos hs hq.1) (by linarith [hq.2])
  nlinarith [hqrec]

theorem step_not_fixed {x : Frequencies} {s b₁ b₂ : ℝ}
    (hx : Simplex x) (hs : 0 < s)
    (hb₁ : 0 ≤ b₁ ∧ b₁ ≤ 1) (hb₂ : 0 ≤ b₂ ∧ b₂ ≤ 1)
    (hp : 0 < p x ∧ p x < 1) (hq : 0 < q x ∧ q x < 1) :
    step x s b₁ b₂ ≠ x := by
  intro hfixed
  have h := step_recursions
    (ne_of_gt (normalizer_pos hx (le_of_lt hs) hb₁ hb₂))
  rw [hfixed] at h
  exact no_polymorphic_fixed_point hx hs hb₁ hb₂ hp hq h

end FogartyAffinity

#print axioms FogartyAffinity.transmit_simplex
#print axioms FogartyAffinity.normalizer_pos
#print axioms FogartyAffinity.step_recursions
#print axioms FogartyAffinity.source_preserves_simplex
#print axioms FogartyAffinity.step_preserves_simplex
#print axioms FogartyAffinity.p_drift_mul
#print axioms FogartyAffinity.p_drift
#print axioms FogartyAffinity.no_polymorphic_fixed_point
#print axioms FogartyAffinity.step_not_fixed


