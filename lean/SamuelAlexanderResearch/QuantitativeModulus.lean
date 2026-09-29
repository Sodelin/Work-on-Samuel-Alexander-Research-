import SamuelAlexanderResearch.FiniteEditStability
import SamuelAlexanderResearch.PopulationCounting

/-! Effective upper bounds from a modulus witnessing the failure of local
periods and antiperiods. No matching-length bound is assumed. -/

namespace QuantitativeModulus
open BinaryAvoidance QuantitativeAvoidance FiniteEditStability PopulationCounting

/-- A constant offset d cannot take a two-step edge at a breaking index. -/
def BreaksAt (s : Nat → Bool) (d i : Nat) : Prop :=
  s i ≠ !(row s (2*i+d+2))

/-- Each bounded offset has a period/antiperiod break in every specified window. -/
def IsModulus (s : Nat → Bool) (M : Nat → Nat → Nat) : Prop :=
  ∀ v b d, d ≤ v → ∃ j, b ≤ j ∧ j < M v b ∧ BreaksAt s d j

theorem aperiodic_has_break (s : Nat → Bool) (ha : ¬EventuallyPeriodic s)
    (b d : Nat) : ∃ j, b ≤ j ∧ BreaksAt s d j := by
  classical
  by_cases hex : ∃ j, b ≤ j ∧ BreaksAt s d j
  · exact hex
  · have ht : ∀ j, b ≤ j → s j = !(row s (2*j+d+2)) := by
      intro j hj
      apply Classical.byContradiction
      intro he
      exact hex ⟨j, hj, he⟩
    apply False.elim
    apply ha
    let e := d/2
    by_cases parity : d%2 = 0
    · have hd : d = 2*e := by dsimp [e]; omega
      have opposite : ∀ j, b ≤ j → s j = !(s (j+e+1)) := by
        intro j hj
        have label := ht j hj
        have hw : 2*j+d+2 = 2*(j+e+1) := by omega
        simpa only [hw, row_even] using label
      refine ⟨b, 2*(e+1), by omega, ?_⟩
      intro j hj
      have first := opposite j hj
      have second := opposite (j+e+1) (by omega)
      have hw : j+e+1+e+1 = j+2*(e+1) := by omega
      rw [hw] at second
      rw [second] at first
      simpa using first.symm
    · have hd : d = 2*e+1 := by dsimp [e]; omega
      refine ⟨b, e+1, by omega, ?_⟩
      intro j hj
      have label := ht j hj
      have hw : 2*j+d+2 = 2*(j+e+1)+1 := by omega
      rw [hw, row_odd] at label
      simpa [Nat.add_assoc] using label.symm

/-- Aperiodicity supplies a genuine local-bit modulus, independently of paths. -/
theorem aperiodic_has_modulus (s : Nat → Bool) (ha : ¬EventuallyPeriodic s) :
    ∃ M, IsModulus s M := by
  classical
  let witness := fun b d => Classical.choose (aperiodic_has_break s ha b d)
  have hw : ∀ b d, b ≤ witness b d ∧ BreaksAt s d (witness b d) := by
    intro b d
    exact Classical.choose_spec (aperiodic_has_break s ha b d)
  let M := fun v b => b+1+sumBelow (v+1) (witness b)
  refine ⟨M, ?_⟩
  intro v b d hd
  have ht := term_le_sumBelow (witness b) (show d < v+1 by omega)
  refine ⟨witness b d, (hw b d).1, ?_, (hw b d).2⟩
  change witness b d < b+1+sumBelow (v+1) (witness b)
  omega

def clock (M : Nat → Nat → Nat) (v : Nat) : Nat → Nat
  | 0 => 0
  | i+1 => M v (clock M v i)

theorem modulus_advances {s : Nat → Bool} {M : Nat → Nat → Nat}
    (hm : IsModulus s M) (v b : Nat) : b < M v b := by
  obtain ⟨j, hj, he, _⟩ := hm v b 0 (by omega)
  omega

theorem clock_mono {s : Nat → Bool} {M : Nat → Nat → Nat}
    (hm : IsModulus s M) (v : Nat) {i j : Nat} (hij : i ≤ j) :
    clock M v i ≤ clock M v j := by
  induction j with
  | zero =>
    have : i = 0 := by omega
    subst i
    exact Nat.le_refl _
  | succ j ih =>
    by_cases h : i ≤ j
    · have h1 := ih h
      have h2 := modulus_advances hm v (clock M v j)
      change clock M v i ≤ M v (clock M v j)
      omega
    · have : i = j+1 := by omega
      subst i
      exact Nat.le_refl _

def offset (path : Nat → Nat) (i : Nat) : Nat := path i - 2*i

theorem prefix_offset_mono {s : Nat → Bool} {path : Nat → Nat} {ell : Nat}
    (hp : MatchesPrefix s path ell) {i j : Nat} (hij : i ≤ j) (hj : j ≤ ell) :
    offset path j ≤ offset path i := by
  induction j with
  | zero =>
    have : i = 0 := by omega
    subst i
    exact Nat.le_refl _
  | succ j ih =>
    by_cases h : i ≤ j
    · have ho := ih h (by omega)
      have hb := prefix_lower_bound s path ell hp j (by omega)
      have he := edge_displacement s (path j) (path (j+1)) (s j) (hp j (by omega))
      dsimp [offset] at *
      omega
    · have : i = j+1 := by omega
      subst i
      exact Nat.le_refl _

/-- Each full modulus window consumes at least one unit of actual path offset. -/
theorem window_forces_drop {s : Nat → Bool} {M : Nat → Nat → Nat}
    (hm : IsModulus s M) {path : Nat → Nat} {ell b : Nat}
    (hp : MatchesPrefix s path ell) (hend : M (path 0) b ≤ ell) :
    offset path (M (path 0) b) < offset path b := by
  let v := path 0
  let e := M v b
  have hbe : b < e := modulus_advances hm v b
  have hbell : b ≤ ell := by dsimp [e, v] at hbe; omega
  have hd : offset path b ≤ v := by
    have h := prefix_offset_mono hp (show 0 ≤ b by omega) hbell
    simpa [offset, v] using h
  obtain ⟨j, hbj, hje, hbreak⟩ := hm v b (offset path b) hd
  have hjell : j+1 ≤ ell := by dsimp [e, v] at *; omega
  have hstart := prefix_offset_mono hp hbj (by omega : j ≤ ell)
  have hnext := prefix_offset_mono hp (show j ≤ j+1 by omega) hjell
  have hendmono := prefix_offset_mono hp (show j+1 ≤ e by dsimp [e]; omega)
    (show e ≤ ell from hend)
  have htotal := prefix_offset_mono hp (show b ≤ e by omega) (show e ≤ ell from hend)
  apply Classical.byContradiction
  intro hn
  change ¬offset path e < offset path b at hn
  have heq0 : offset path j = offset path b := by omega
  have heq1 : offset path (j+1) = offset path b := by omega
  have hl0 := prefix_lower_bound s path ell hp j (by omega)
  have hl1 := prefix_lower_bound s path ell hp (j+1) hjell
  have hp0 : path j = 2*j+offset path b := by dsimp [offset] at *; omega
  have hp1 : path (j+1) = 2*j+offset path b+2 := by dsimp [offset] at *; omega
  have he := hp j (by omega)
  apply hbreak
  rcases he.2 with hone | htwo
  · omega
  · simpa only [hp1] using htwo.2

/-- An explicit iterated local-period modulus bounds every finite match. -/
theorem prefix_length_lt_clock {s : Nat → Bool} {M : Nat → Nat → Nat}
    (hm : IsModulus s M) {path : Nat → Nat} {ell : Nat}
    (hp : MatchesPrefix s path ell) : ell < clock M (path 0) (path 0+1) := by
  let v := path 0
  apply Classical.byContradiction
  intro hn
  have hend : clock M v (v+1) ≤ ell := by dsimp [v]; omega
  have hdrop : ∀ i, i ≤ v+1 → offset path (clock M v i)+i ≤ v := by
    intro i
    induction i with
    | zero => intro _; simp [clock, offset, v]
    | succ i ih =>
      intro hi
      have hprevious := ih (by omega)
      have htime := clock_mono hm v hi
      have hstep := window_forces_drop hm hp (b := clock M v i)
        (show M (path 0) (clock M v i) ≤ ell by
          change clock M v (i+1) ≤ ell
          omega)
      change offset path (clock M v (i+1)) < offset path (clock M v i) at hstep
      omega
  have h := hdrop (v+1) (by omega)
  omega

/-- Even offsets test antiperiod e+1. -/
theorem even_break_iff (s : Nat → Bool) (e i : Nat) :
    BreaksAt s (2*e) i ↔ s (i+e+1) = s i := by
  unfold BreaksAt
  have hw : 2*i+2*e+2 = 2*(i+e+1) := by omega
  rw [hw, row_even]
  cases s i <;> cases s (i+e+1) <;> decide

/-- Odd offsets test period e+1. -/
theorem odd_break_iff (s : Nat → Bool) (e i : Nat) :
    BreaksAt s (2*e+1) i ↔ s (i+e+1) ≠ s i := by
  unfold BreaksAt
  have hw : 2*i+(2*e+1)+2 = 2*(i+e+1)+1 := by omega
  rw [hw, row_odd, Bool.not_not]
  exact ne_comm

/-- A uniform window size R at the relevant offsets gives a simple product bound. -/
theorem prefix_length_lt_uniform_windows {s : Nat → Bool} {M : Nat → Nat → Nat}
    (hm : IsModulus s M) {path : Nat → Nat} {ell R : Nat}
    (hp : MatchesPrefix s path ell)
    (hR : ∀ b, M (path 0) b ≤ b+R) : ell < (path 0+1)*R := by
  have hb : ∀ i, clock M (path 0) i ≤ i*R := by
    intro i
    induction i with
    | zero => simp [clock]
    | succ i ih =>
      have hs := hR (clock M (path 0) i)
      change M (path 0) (clock M (path 0) i) ≤ (i+1)*R
      rw [Nat.add_mul, Nat.one_mul]
      omega
  exact Nat.lt_of_lt_of_le (prefix_length_lt_clock hm hp) (hb (path 0+1))

/-- Every aperiodic target admits one bit-defined modulus bounding all starts. -/
theorem aperiodic_explicit_bounds (s : Nat → Bool) (ha : ¬EventuallyPeriodic s) :
    ∃ M, IsModulus s M ∧ ∀ path ell, MatchesPrefix s path ell →
      ell < clock M (path 0) (path 0+1) := by
  obtain ⟨M, hm⟩ := aperiodic_has_modulus s ha
  exact ⟨M, hm, fun _ _ hp => prefix_length_lt_clock hm hp⟩

#print axioms aperiodic_has_modulus
#print axioms prefix_length_lt_clock
#print axioms even_break_iff
#print axioms odd_break_iff
#print axioms prefix_length_lt_uniform_windows
#print axioms aperiodic_explicit_bounds

end QuantitativeModulus
