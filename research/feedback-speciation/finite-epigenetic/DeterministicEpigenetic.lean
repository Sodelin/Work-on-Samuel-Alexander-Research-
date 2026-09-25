import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
Exact reduced deterministic Planidin-model recurrence at m=1/4, s=r=1/2.
The marker coordinates are conditional B frequencies in classes d1e,d1E,d2e,d2E.
Index zero below is post-pulse biological generation one: p=6/7, theta=(0,0,0,1).
The row coefficients come from migration, additive viability and free recombination
of the source's randomly paired haplotypes. The independent source audit checks
that reduction; this module directly verifies the displayed reduced recurrence.
Compiler status is recorded in verification/combined-receipt.json.
Common-limit existence is outside the formal scope of this module.
-/
namespace DeterministicEpigenetic
noncomputable section

structure Four where
  d1e : ℝ
  d1E : ℝ
  d2e : ℝ
  d2E : ℝ

def reverse (x : Four) : Four := ⟨x.d2E, x.d2e, x.d1E, x.d1e⟩
def weightSum (w : Four) : ℝ := w.d1e + w.d1E + w.d2e + w.d2E

def blend (w x : Four) : ℝ :=
  (w.d1e*x.d1e + w.d1E*x.d1E + w.d2e*x.d2e + w.d2E*x.d2E) / weightSum w

def Positive (w : Four) : Prop :=
  0 < w.d1e ∧ 0 < w.d1E ∧ 0 < w.d2e ∧ 0 < w.d2E

def Box (M : ℝ) (x : Four) : Prop :=
  (0 ≤ x.d1e ∧ x.d1e ≤ M) ∧ (0 ≤ x.d1E ∧ x.d1E ≤ M) ∧
  (0 ≤ x.d2e ∧ x.d2e ≤ M) ∧ (0 ≤ x.d2E ∧ x.d2E ≤ M)

def BackgroundInterval (p : ℝ) : Prop := 2/3 ≤ p ∧ p ≤ 6/7

def backgroundStep (p : ℝ) : ℝ := (2+2*p+2*p^2)/(5+2*p)

/-- Unnormalized conditional-marker coefficients for deme 1's e class. -/
def rowEsmall (p : ℝ) : Four :=
  ⟨3*(1-p)*(4-p), 9*p*(1-p), p*(3+p), 3*p*(1-p)⟩

/-- Unnormalized conditional-marker coefficients for deme 1's E class. -/
def rowElarge (p : ℝ) : Four :=
  ⟨9*p*(1-p), 3*p*(3+5*p), 3*p*(1-p), (1-p)*(8-5*p)⟩

def markerStep (p : ℝ) (x : Four) : Four :=
  ⟨blend (rowEsmall p) x, blend (rowElarge p) x,
   blend (reverse (rowElarge p)) x, blend (reverse (rowEsmall p)) x⟩

theorem row_sums (p : ℝ) :
    weightSum (rowEsmall p) = 12-8*p^2 ∧
    weightSum (rowElarge p) = 8+8*p+8*p^2 := by
  constructor <;> dsimp [weightSum, rowEsmall, rowElarge] <;> ring

/-- The same selected-gamete masses give the scalar background recursion. -/
theorem background_from_rows {p : ℝ} (hp : BackgroundInterval p) :
    weightSum (rowElarge p) / (weightSum (rowEsmall p)+weightSum (rowElarge p)) =
      backgroundStep p := by
  rw [(row_sums p).1, (row_sums p).2]
  have hd : 5+2*p ≠ 0 := by have := hp.1; linarith
  have hden : 12-8*p^2+(8+8*p+8*p^2) = 4*(5+2*p) := by ring
  rw [hden]
  unfold backgroundStep
  field_simp [hd] <;> ring

theorem background_invariant {p : ℝ} (hp : BackgroundInterval p) :
    BackgroundInterval (backgroundStep p) := by
  have hd : 0 < 5+2*p := by have := hp.1; linarith
  constructor
  · apply (le_div_iff₀ hd).2
    have hm : 0 ≤ (p-2/3)*(p+1) :=
      mul_nonneg (by linarith [hp.1]) (by linarith [hp.1])
    nlinarith
  · apply (div_le_iff₀ hd).2
    have hm : 0 ≤ (6/7-p)*(6/7+p) :=
      mul_nonneg (by linarith [hp.2]) (by linarith [hp.1])
    nlinarith [hp.2]

theorem row_positive {p : ℝ} (hp : BackgroundInterval p) :
    Positive (rowEsmall p) ∧ Positive (rowElarge p) := by
  have hp0 : 0 < p := by linarith [hp.1]
  have hm0 : 0 < 1-p := by linarith [hp.2]
  have h4 : 0 < 4-p := by linarith [hp.2]
  have h8 : 0 < 8-5*p := by linarith [hp.2]
  dsimp [Positive, rowEsmall, rowElarge]
  constructor
  · exact ⟨by positivity, by positivity, by positivity, by positivity⟩
  · exact ⟨by positivity, by positivity, by positivity, by positivity⟩

theorem reverse_positive {w : Four} (hw : Positive w) : Positive (reverse w) :=
  ⟨hw.2.2.2, hw.2.2.1, hw.2.1, hw.1⟩

theorem blend_box {M : ℝ} {w x : Four} (hw : Positive w) (hx : Box M x) :
    0 ≤ blend w x ∧ blend w x ≤ M := by
  have hd : 0 < weightSum w := by unfold weightSum; linarith [hw.1, hw.2.1, hw.2.2.1, hw.2.2.2]
  have ha := mul_nonneg hw.1.le hx.1.1
  have hb := mul_nonneg hw.2.1.le hx.2.1.1
  have hc := mul_nonneg hw.2.2.1.le hx.2.2.1.1
  have he := mul_nonneg hw.2.2.2.le hx.2.2.2.1
  have ha' := mul_le_mul_of_nonneg_left hx.1.2 hw.1.le
  have hb' := mul_le_mul_of_nonneg_left hx.2.1.2 hw.2.1.le
  have hc' := mul_le_mul_of_nonneg_left hx.2.2.1.2 hw.2.2.1.le
  have he' := mul_le_mul_of_nonneg_left hx.2.2.2.2 hw.2.2.2.le
  constructor
  · exact div_nonneg (by linarith) hd.le
  · apply (div_le_iff₀ hd).2
    dsimp [weightSum]
    nlinarith

theorem marker_box_invariant {p M : ℝ} {x : Four}
    (hp : BackgroundInterval p) (hx : Box M x) : Box M (markerStep p x) := by
  have hw := row_positive hp
  exact ⟨blend_box hw.1 hx, blend_box hw.2 hx,
    blend_box (reverse_positive hw.2) hx, blend_box (reverse_positive hw.1) hx⟩

/-- Post-pulse biological generation one is iteration zero. -/
def trajectory : ℕ → ℝ × Four
  | 0 => (6/7, ⟨0,0,0,1⟩)
  | n+1 => (backgroundStep (trajectory n).1, markerStep (trajectory n).1 (trajectory n).2)

theorem trajectory_background : ∀ n, BackgroundInterval (trajectory n).1 := by
  intro n
  induction n with
  | zero => norm_num [trajectory, BackgroundInterval]
  | succ n ih => exact background_invariant ih

/-- Three reduced steps after the pulse give biological generation four. -/
theorem generation_four_exact : (trajectory 3).2 =
    ⟨158042799831/2612298864200, 825778109695/18042773705392,
     1228259142369/18042773705392, 172444392929/2612298864200⟩ := by
  norm_num [trajectory, backgroundStep, markerStep, blend, weightSum,
    rowEsmall, rowElarge, reverse]

theorem generation_four_background_exact :
    (trajectory 3).1 = (2255346713174/3234958787249 : ℝ) := by
  norm_num [trajectory, backgroundStep]
def markerUpper : ℝ := 1228259142369/18042773705392

theorem generation_four_box : Box markerUpper (trajectory 3).2 := by
  rw [generation_four_exact]
  norm_num [Box, markerUpper]

theorem marker_upper_strict : 0 < markerUpper ∧ markerUpper < 1/14 := by
  norm_num [markerUpper]

theorem all_later_marker_box : ∀ n, Box markerUpper (trajectory (n+3)).2 := by
  intro n
  induction n with
  | zero => exact generation_four_box
  | succ n ih =>
    change Box markerUpper (markerStep (trajectory (n+3)).1 (trajectory (n+3)).2)
    exact marker_box_invariant (trajectory_background (n+3)) ih

/-- Equal-deme mean, using selected-allele frequencies p and 1-p. -/
def meanMarker (p : ℝ) (x : Four) : ℝ :=
  ((1-p)*x.d1e+p*x.d1E+p*x.d2e+(1-p)*x.d2E)/2

theorem mean_marker_box {p M : ℝ} {x : Four}
    (hp : BackgroundInterval p) (hx : Box M x) :
    0 ≤ meanMarker p x ∧ meanMarker p x ≤ M := by
  let w : Four := ⟨1-p,p,p,1-p⟩
  have hw : Positive w := by
    dsimp [Positive, w]
    exact ⟨by linarith [hp.2], by linarith [hp.1], by linarith [hp.1], by linarith [hp.2]⟩
  have he : blend w x = meanMarker p x := by
    have hs : weightSum w = 2 := by dsimp [weightSum, w]; ring
    unfold blend
    rw [hs]
    rfl
  rw [← he]
  exact blend_box hw hx

def geneticMean (n : ℕ) : ℝ := meanMarker (trajectory n).1 (trajectory n).2
/-- Global initial marker dose m/2=1/8. -/
def geneticRI (n : ℕ) : ℝ := 1-8*geneticMean n

theorem all_later_mean_bound (n : ℕ) :
    0 ≤ geneticMean (n+3) ∧ geneticMean (n+3) ≤ markerUpper :=
  mean_marker_box (trajectory_background (n+3)) (all_later_marker_box n)

theorem deterministic_genetic_tail_bound (n : ℕ) :
    1027087570805/2255346713174 ≤ geneticRI (n+3) ∧ 3/7 < geneticRI (n+3) := by
  have hmean := (all_later_mean_bound n).2
  have hm := marker_upper_strict.2
  have he : 1-8*markerUpper = (1027087570805/2255346713174 : ℝ) := by
    norm_num [markerUpper]
  unfold geneticRI
  constructor <;> linarith

/-- A supplied limiting mean has the same rigorous bound; existence is not assumed silently. -/
def MeanConverges (L : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → |geneticMean n-L| < δ

theorem limiting_mean_bound {L : ℝ} (hL : MeanConverges L) : L ≤ markerUpper := by
  apply le_of_not_gt
  intro h
  have hgap : 0 < L-markerUpper := by linarith
  obtain ⟨n₀, hn₀⟩ := hL (L-markerUpper) hgap
  have ha := (abs_lt.mp (hn₀ (n₀+3) (by omega))).1
  have hb := (all_later_mean_bound n₀).2
  linarith

theorem limiting_genetic_RI_bound {L : ℝ} (hL : MeanConverges L) :
    1027087570805/2255346713174 ≤ 1-8*L ∧ 3/7 < 1-8*L := by
  have hb := limiting_mean_bound hL
  have hm := marker_upper_strict.2
  have he : 1-8*markerUpper = (1027087570805/2255346713174 : ℝ) := by
    norm_num [markerUpper]
  constructor <;> linarith

/-- Pure induction gives effective neutral exchange a=1/7 at these parameters. -/
def inductionStep (q : ℝ × ℝ) : ℝ × ℝ :=
  (6/7*q.1+1/7*q.2, 1/7*q.1+6/7*q.2)

def inductionTrajectory : ℕ → ℝ × ℝ
  | 0 => (0,1/7)
  | n+1 => inductionStep (inductionTrajectory n)

theorem induction_sum_constant : ∀ n, (inductionTrajectory n).1+(inductionTrajectory n).2 = 1/7 := by
  intro n
  induction n with
  | zero => norm_num [inductionTrajectory]
  | succ n ih =>
    change (inductionStep (inductionTrajectory n)).1+(inductionStep (inductionTrajectory n)).2 = 1/7
    dsimp [inductionStep]
    linarith

theorem pure_induction_RI_exact (n : ℕ) :
    1-8*((inductionTrajectory n).1+(inductionTrajectory n).2)/2 = (3/7 : ℝ) := by
  rw [induction_sum_constant]
  norm_num

/-- Every deterministic genetic RI after generation four exceeds pure induction's RI. -/
theorem deterministic_ranking_strict (n : ℕ) :
    1-8*((inductionTrajectory (n+3)).1+(inductionTrajectory (n+3)).2)/2 < geneticRI (n+3) := by
  rw [pure_induction_RI_exact]
  exact (deterministic_genetic_tail_bound n).2

end
end DeterministicEpigenetic

#print axioms DeterministicEpigenetic.background_from_rows
#print axioms DeterministicEpigenetic.background_invariant
#print axioms DeterministicEpigenetic.row_positive
#print axioms DeterministicEpigenetic.marker_box_invariant
#print axioms DeterministicEpigenetic.generation_four_exact
#print axioms DeterministicEpigenetic.all_later_mean_bound
#print axioms DeterministicEpigenetic.deterministic_genetic_tail_bound
#print axioms DeterministicEpigenetic.limiting_genetic_RI_bound
#print axioms DeterministicEpigenetic.pure_induction_RI_exact
#print axioms DeterministicEpigenetic.deterministic_ranking_strict

