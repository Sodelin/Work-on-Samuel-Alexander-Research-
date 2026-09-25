import Std

/-!
This file proves an exact interval/coalescence reduction for the population in
the Thue--Morse sharp-bound question.  It does NOT prove the conjectural 8/3
bound.  The reduction holds for every binary vertex coloring and target word.
In particular the edge definition below explicitly omits the edge 0 -> 1.
-/

namespace SamuelAlexanderResearch.ThueMorseBound

def Edge (color : Nat → Bool) (bit : Bool) (x y : Nat) : Prop :=
  2 ≤ y ∧ ((y = x + 1 ∧ color y = bit) ∨
    (y = x + 2 ∧ color y ≠ bit))

def boundary (color : Nat → Bool) (bit : Bool) (x : Nat) : Nat :=
  if color (x + 1) = bit then x + 1 else x + 2

theorem boundary_bounds (color : Nat → Bool) (bit : Bool) (x : Nat) :
    x + 1 ≤ boundary color bit x ∧ boundary color bit x ≤ x + 2 := by
  unfold boundary
  split <;> omega

theorem boundary_mono (color : Nat → Bool) (bit : Bool) {x y : Nat}
    (h : x ≤ y) : boundary color bit x ≤ boundary color bit y := by
  have hx := boundary_bounds color bit x
  have hy := boundary_bounds color bit y
  by_cases hxy : x = y
  · subst y
    exact Nat.le_refl _
  · omega

theorem interval_step (color : Nat → Bool) (bit : Bool) (a c w : Nat)
    (ha : 1 ≤ a) (_hac : a ≤ c) :
    (∃ x, a ≤ x ∧ x < c ∧ Edge color bit x w) ↔
      boundary color bit a ≤ w ∧ w < boundary color bit c := by
  have hlo := boundary_bounds color bit a
  have hhi := boundary_bounds color bit c
  constructor
  · rintro ⟨x, hax, hxc, _, (⟨hw, hcol⟩ | ⟨hw, hcol⟩)⟩
    · subst w
      constructor
      · by_cases hxa : x = a
        · subst x
          simp [boundary, hcol]
        · omega
      · omega
    · subst w
      constructor
      · omega
      · by_cases hxc' : x + 1 = c
        · have hc : color (c + 1) ≠ bit := by
            have heq : c + 1 = x + 2 := by omega
            simpa [heq] using hcol
          simp only [boundary, if_neg hc]
          omega
        · omega
  · rintro ⟨haw, hwc⟩
    have hw : 2 ≤ w := by omega
    by_cases hcol : color w = bit
    · have htop : w < c + 1 := by
        by_cases hn : w < c + 1
        · exact hn
        · have heq : w = c + 1 := by omega
          subst w
          simp [boundary, hcol] at hwc
      refine ⟨w - 1, by omega, by omega, hw, Or.inl ?_⟩
      exact ⟨by omega, hcol⟩
    · have hbottom : a + 2 ≤ w := by
        by_cases hn : a + 2 ≤ w
        · exact hn
        · have heq : w = a + 1 := by omega
          subst w
          simp [boundary, hcol] at haw
      refine ⟨w - 2, by omega, by omega, hw, Or.inr ?_⟩
      exact ⟨by omega, hcol⟩

def trajectory (color target : Nat → Bool) (start : Nat) : Nat → Nat
  | 0 => start
  | k + 1 => boundary color (target k) (trajectory color target start k)

theorem trajectory_ge_start (color target : Nat → Bool) (start k : Nat) :
    start ≤ trajectory color target start k := by
  induction k with
  | zero => simp [trajectory]
  | succ k ih =>
    have h := boundary_bounds color (target k) (trajectory color target start k)
    simp only [trajectory]
    omega

theorem trajectory_mono (color target : Nat → Bool) {a c : Nat}
    (h : a ≤ c) (k : Nat) :
    trajectory color target a k ≤ trajectory color target c k := by
  induction k with
  | zero => exact h
  | succ k ih => exact boundary_mono color (target k) ih

theorem coalescence_persists (color target : Nat → Bool) (a c k : Nat)
    (h : trajectory color target a k = trajectory color target c k) (n : Nat) :
    trajectory color target a (k + n) = trajectory color target c (k + n) := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    exact congrArg (boundary color (target (k + n))) ih

def Reachable (color target : Nat → Bool) (start : Nat) : Nat → Nat → Prop
  | 0, w => w = start
  | k + 1, w => ∃ x, Reachable color target start k x ∧ Edge color (target k) x w

theorem reachable_iff_interval (color target : Nat → Bool) (v : Nat)
    (hv : 1 ≤ v) (k w : Nat) :
    Reachable color target v k w ↔
      trajectory color target v k ≤ w ∧
        w < trajectory color target (v + 1) k := by
  induction k generalizing w with
  | zero => simp only [Reachable, trajectory]; omega
  | succ k ih =>
    simp only [Reachable, trajectory, ih]
    have ha := trajectory_ge_start color target v k
    have hac := trajectory_mono color target (Nat.le_succ v) k
    have hs := interval_step color (target k)
      (trajectory color target v k) (trajectory color target (v + 1) k) w
      (by omega) hac
    simpa only [and_assoc] using hs

theorem nonempty_iff_separated (color target : Nat → Bool) (v : Nat)
    (hv : 1 ≤ v) (k : Nat) :
    (∃ w, Reachable color target v k w) ↔
      trajectory color target v k < trajectory color target (v + 1) k := by
  simp only [reachable_iff_interval color target v hv]
  constructor
  · rintro ⟨w, hl, hr⟩
    omega
  · intro h
    exact ⟨trajectory color target v k, Nat.le_refl _, h⟩

theorem extinct_iff_coalesced (color target : Nat → Bool) (v : Nat)
    (hv : 1 ≤ v) (k : Nat) :
    (¬ ∃ w, Reachable color target v k w) ↔
      trajectory color target v k = trajectory color target (v + 1) k := by
  rw [nonempty_iff_separated color target v hv]
  have hm : trajectory color target v k ≤ trajectory color target (v + 1) k :=
    trajectory_mono color target (by omega) k
  omega

def IsMaximumLength (color target : Nat → Bool) (v ell : Nat) : Prop :=
  (∃ w, Reachable color target v ell w) ∧
    ¬ ∃ w, Reachable color target v (ell + 1) w

theorem maximum_length_iff (color target : Nat → Bool) (v ell : Nat)
    (hv : 1 ≤ v) :
    IsMaximumLength color target v ell ↔
      trajectory color target v ell < trajectory color target (v + 1) ell ∧
      trajectory color target v (ell + 1) =
        trajectory color target (v + 1) (ell + 1) := by
  unfold IsMaximumLength
  rw [nonempty_iff_separated color target v hv,
    extinct_iff_coalesced color target v hv]

#print axioms interval_step
#print axioms reachable_iff_interval
#print axioms coalescence_persists
#print axioms maximum_length_iff

end SamuelAlexanderResearch.ThueMorseBound
