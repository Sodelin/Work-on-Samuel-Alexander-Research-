import Std

/-!
The binary avoiding construction of the September 2026 classification paper.
This is a fresh Std-only formalization of the offset argument. It attributes
the construction to that manuscript and makes no novelty claim.
-/

namespace BinaryAvoidance

def row (s : Nat → Bool) (w : Nat) : Bool :=
  if w % 2 = 0 then s (w / 2) else !(s (w / 2))

def Edge (s : Nat → Bool) (u w : Nat) (label : Bool) : Prop :=
  2 ≤ w ∧ ((w = u + 1 ∧ label = row s w) ∨
    (w = u + 2 ∧ label = !(row s w)))

def Matches (s : Nat → Bool) (path : Nat → Nat) : Prop :=
  ∀ k, Edge s (path k) (path (k + 1)) (s k)

def EventuallyPeriodic (s : Nat → Bool) : Prop :=
  ∃ start period : Nat, 0 < period ∧ ∀ k, start ≤ k → s (k + period) = s k

theorem row_even (s : Nat → Bool) (n : Nat) : row s (2 * n) = s n := by
  have hm : (2 * n) % 2 = 0 := by omega
  have hd : (2 * n) / 2 = n := by omega
  simp [row, hm, hd]

theorem row_odd (s : Nat → Bool) (n : Nat) : row s (2 * n + 1) = !(s n) := by
  have hm : (2 * n + 1) % 2 = 1 := by omega
  have hd : (2 * n + 1) / 2 = n := by omega
  simp [row, hm, hd]

theorem path_lower_bound (s : Nat → Bool) (path : Nat → Nat)
    (matching : Matches s path) : ∀ k, 2 * k ≤ path k := by
  intro k
  induction k with
  | zero => omega
  | succ k ih =>
      obtain ⟨_, ⟨step, label⟩ | ⟨step, _⟩⟩ := matching k
      · by_cases h : path k = 2 * k
        · have hw : path (k + 1) = 2 * k + 1 := by omega
          rw [hw, row_odd] at label
          cases hs : s k <;> simp [hs] at label
        · omega
      · omega

theorem decreasing_nat_stabilizes (d : Nat → Nat)
    (decreasing : ∀ k, d (k + 1) ≤ d k) :
    ∃ start, ∀ k, start ≤ k → d k = d start := by
  classical
  have hasMinimum : ∀ value, (∃ k, d k = value) → ∃ m, ∀ k, d m ≤ d k := by
    intro value
    induction value using Nat.strongRecOn with
    | ind value ih =>
        intro occurs
        by_cases smaller : ∃ k, d k < value
        · obtain ⟨k, hk⟩ := smaller
          exact ih (d k) hk ⟨k, rfl⟩
        · obtain ⟨m, hm⟩ := occurs
          refine ⟨m, ?_⟩
          intro k
          have hk : ¬ d k < value := fun h => smaller ⟨k, h⟩
          omega
  have monotone : ∀ j i, i ≤ j → d j ≤ d i := by
    intro j
    induction j with
    | zero =>
        intro i hi
        have : i = 0 := by omega
        subst i
        exact Nat.le_refl _
    | succ j ih =>
        intro i hi
        by_cases h : i ≤ j
        · exact Nat.le_trans (decreasing j) (ih i h)
        · have : i = j + 1 := by omega
          subst i
          exact Nat.le_refl _
  obtain ⟨start, minimal⟩ := hasMinimum (d 0) ⟨0, rfl⟩
  exact ⟨start, fun k hk => Nat.le_antisymm (monotone k start hk) (minimal k)⟩

/-- An infinite path spelling its own target forces that target eventually periodic. -/
theorem matching_implies_eventuallyPeriodic (s : Nat → Bool) (path : Nat → Nat)
    (matching : Matches s path) : EventuallyPeriodic s := by
  let offset := fun k => path k - 2 * k
  have lower := path_lower_bound s path matching
  have decr : ∀ k, offset (k + 1) ≤ offset k := by
    intro k
    obtain ⟨_, ⟨step, _⟩ | ⟨step, _⟩⟩ := matching k <;>
      dsimp [offset] <;> have := lower k <;> omega
  obtain ⟨start, stable⟩ := decreasing_nat_stabilizes offset decr
  let d := offset start
  have linear : ∀ k, start ≤ k → path k = 2 * k + d := by
    intro k hk
    have := stable k hk
    have := lower k
    dsimp [offset, d] at *
    omega
  have tailLabel : ∀ k, start ≤ k → s k = !(row s (2 * k + d + 2)) := by
    intro k hk
    have hnow := linear k hk
    have hnext := linear (k + 1) (by omega)
    obtain ⟨_, ⟨step, _⟩ | ⟨_, label⟩⟩ := matching k
    · omega
    · have hw : path (k + 1) = 2 * k + d + 2 := by omega
      simpa only [hw] using label
  let e := d / 2
  by_cases parity : d % 2 = 0
  · have hd : d = 2 * e := by dsimp [e]; omega
    have opposite : ∀ k, start ≤ k → s k = !(s (k + e + 1)) := by
      intro k hk
      have label := tailLabel k hk
      have hw : 2 * k + d + 2 = 2 * (k + e + 1) := by omega
      simpa only [hw, row_even] using label
    refine ⟨start, 2 * (e + 1), by omega, ?_⟩
    intro k hk
    have first := opposite k hk
    have second := opposite (k + e + 1) (by omega)
    have hw : k + e + 1 + e + 1 = k + 2 * (e + 1) := by omega
    rw [hw] at second
    rw [second] at first
    simpa using first.symm
  · have hd : d = 2 * e + 1 := by dsimp [e]; omega
    refine ⟨start, e + 1, by omega, ?_⟩
    intro k hk
    have label := tailLabel k hk
    have hw : 2 * k + d + 2 = 2 * (k + e + 1) + 1 := by omega
    rw [hw, row_odd] at label
    simpa [Nat.add_assoc] using label.symm

theorem aperiodic_target_avoided (s : Nat → Bool)
    (aperiodic : ¬ EventuallyPeriodic s) : ¬ ∃ path, Matches s path := by
  intro h
  obtain ⟨path, matching⟩ := h
  exact aperiodic (matching_implies_eventuallyPeriodic s path matching)

end BinaryAvoidance
