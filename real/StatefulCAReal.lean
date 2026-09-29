import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import SamuelAlexanderResearch.StatefulCA

/-! Literal real convex hulls for the synthetic stateful CA certificate. -/
namespace StatefulCAReal
open StatefulCA

/-- The actual predecessor-to-child displacement, embedded in the real plane. -/
def vector (d : Dir) : ℝ × ℝ := ((xStep d : ℝ), (yStep d : ℝ))

def directionSet (D : Dir → Prop) : Set (ℝ × ℝ) := vector '' {d | D d}

def hull (D : Dir → Prop) : Set (ℝ × ℝ) := convexHull ℝ (directionSet D)

theorem direction_mem_hull (D : Dir → Prop) (d : Dir) (hd : D d) : vector d ∈ hull D :=
  subset_convexHull ℝ (directionSet D) ⟨d, hd, rfl⟩

theorem east_mem_hull (D : Dir → Prop) (hn : D 0 ∨ D 1) (hs : D 0 ∨ D 2) :
    (1, 0) ∈ hull D := by
  by_cases hzero : D 0
  · have he := direction_mem_hull D 0 hzero
    simpa [vector, xStep, yStep] using he
  · have hn := direction_mem_hull D 1 (hn.resolve_left hzero)
    have hs := direction_mem_hull D 2 (hs.resolve_left hzero)
    have hc := (convex_convexHull ℝ (directionSet D)) hn hs
      (show (0 : ℝ) ≤ 1/2 by norm_num) (show (0 : ℝ) ≤ 1/2 by norm_num)
      (show (1/2 : ℝ)+1/2=1 by norm_num)
    have hv : (1/2 : ℝ) • vector 1 + (1/2 : ℝ) • vector 2 = (1,0) := by
      ext <;> norm_num [vector, xStep, yStep, Fin.ext_iff]
    simpa only [hull, hv] using hc

/-- Every real convex-hull point, including points with irrational weights,
has horizontal coordinate at most one. -/
theorem hull_east_bound (D : Dir → Prop) (v : ℝ × ℝ) (hv : v ∈ hull D) : v.1 ≤ 1 := by
  have hc : Convex ℝ {p : ℝ × ℝ | p.1 ≤ 1} := by
    intro x hx y hy a b ha hb hab
    change a*x.1+b*y.1 ≤ 1
    nlinarith [mul_nonneg ha (sub_nonneg.mpr hx), mul_nonneg hb (sub_nonneg.mpr hy)]
  apply convexHull_min (t := {p : ℝ × ℝ | p.1 ≤ 1}) ?_ hc hv
  rintro _ ⟨d, _, rfl⟩
  change (xStep d : ℝ) ≤ 1
  unfold xStep
  split <;> norm_num

/-- The exact east support value of every valid fixed two-label certificate. -/
theorem static_east_optimum (a b : Dir → Prop) (cert : FixedCert a b) :
    (1,0) ∈ hull a ∩ hull b ∧ ∀ v ∈ hull a ∩ hull b, v.1 ≤ 1 := by
  obtain ⟨na, sa, nb, sb⟩ := static_east_options a b cert
  exact ⟨⟨east_mem_hull a na sa, east_mem_hull b nb sb⟩,
    fun v hv => hull_east_bound a v hv.1⟩

/-- The horizontal projection of the full real hull intersection has greatest
element exactly one, not merely a supremum or a rational lower witness. -/
theorem static_east_support_one (a b : Dir → Prop) (cert : FixedCert a b) :
    IsGreatest ((fun v : ℝ × ℝ => v.1) '' (hull a ∩ hull b)) 1 := by
  obtain ⟨he, hb⟩ := static_east_optimum a b cert
  refine ⟨⟨(1,0), he, rfl⟩, ?_⟩
  rintro _ ⟨v, hv, rfl⟩
  exact hb v hv

theorem real_horizontal_spaceship_speed_zero (c : Config) (period : Nat) (dx dy : Int)
    (finite : FiniteSupport c) (nonempty : ∃ x y, c x y ≠ dead)
    (recurs : iterate c period = translate c dx dy) :
    (dx : ℝ) / (period : ℝ) = 0 := by
  rw [no_horizontal_spaceship c period dx dy finite nonempty recurs]
  simp

/-- The same actual rule has static real optimum one and excludes every
nonzero horizontal spaceship velocity from finite nonempty support. -/
theorem real_static_gap_and_global_obstruction :
    FixedCert Aligned Diagonal ∧
    (∀ a b, FixedCert a b →
      IsGreatest ((fun v : ℝ × ℝ => v.1) '' (hull a ∩ hull b)) 1) ∧
    (∀ c period dx dy, FiniteSupport c → (∃ x y, c x y ≠ dead) →
      iterate c period = translate c dx dy → (dx : ℝ) / (period : ℝ) = 0) ∧
    FiniteSupport rDomino ∧ evolve rDomino = lDomino ∧ evolve lDomino = rDomino :=
  ⟨aligned_diagonal_certificate, static_east_support_one,
    real_horizontal_spaceship_speed_zero, rDomino_finite, rDomino_step, lDomino_step⟩

#print axioms static_east_optimum
#print axioms static_east_support_one
#print axioms real_static_gap_and_global_obstruction
end StatefulCAReal
