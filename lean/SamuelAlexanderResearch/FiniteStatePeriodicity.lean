import Std

/-!
# Eventual periodicity of deterministic finite-state orbits

Every orbit in `Fin q` following a single deterministic transition eventually
repeats with a positive period. Repetition is derived from finiteness; it is
not assumed. This is a standard finite-state lemma, not a priority claim.

The conclusion concerns state equality. Applying an observation function gives
the corresponding periodicity of labels or actions derived from those states.
-/

namespace FiniteStatePeriodicity

private theorem finite_nat_bound (P : Nat → Nat → Prop) (q : Nat)
    (bounded : ∀ i, i < q → ∃ b, ∀ n, P i n → n < b) :
    ∃ b, ∀ i, i < q → ∀ n, P i n → n < b := by
  induction q with
  | zero => exact ⟨0, fun _ hi => False.elim (by omega)⟩
  | succ q ih =>
    obtain ⟨a, ha⟩ := ih (fun i hi => bounded i (by omega))
    obtain ⟨b, hb⟩ := bounded q (by omega)
    refine ⟨a + b, ?_⟩
    intro i hi n hn
    by_cases hiq : i < q
    · have := ha i hiq n hn
      omega
    · have : i = q := by omega
      subst i
      have := hb n hn
      omega

private theorem finite_bound {q : Nat} (P : Fin q → Nat → Prop)
    (bounded : ∀ v, ∃ b, ∀ n, P v n → n < b) :
    ∃ b, ∀ v n, P v n → n < b := by
  let Q : Nat → Nat → Prop := fun i n => ∃ hi : i < q, P ⟨i, hi⟩ n
  obtain ⟨b, hb⟩ := finite_nat_bound Q q (by
    intro i hi
    obtain ⟨b, hb⟩ := bounded ⟨i, hi⟩
    refine ⟨b, ?_⟩
    intro n hn
    obtain ⟨hi', hn⟩ := hn
    exact hb n hn)
  refine ⟨b, ?_⟩
  intro v n hn
  exact hb v.val v.isLt n ⟨v.isLt, hn⟩

/-- Any infinite sequence of finitely many states repeats at two distinct times. -/
theorem repeated_state {q : Nat} (f : Nat → Fin q) :
    ∃ i j, i < j ∧ f i = f j := by
  classical
  apply Classical.byContradiction
  intro hnone
  have bounded : ∀ v : Fin q, ∃ b, ∀ n, f n = v → n < b := by
    intro v
    by_cases hex : ∃ n, f n = v
    · obtain ⟨n, hn⟩ := hex
      refine ⟨n + 1, ?_⟩
      intro m hm
      by_cases hmn : m ≤ n
      · omega
      · exact False.elim (hnone ⟨n, m, by omega, hn.trans hm.symm⟩)
    · exact ⟨0, fun n hn => False.elim (hex ⟨n, hn⟩)⟩
  obtain ⟨b, hb⟩ := finite_bound (fun v n => f n = v) bounded
  have impossible := hb (f b) b rfl
  omega

/-- Equal states remain equal at every common future offset under determinism. -/
theorem equal_at_offset {q : Nat} (step : Fin q → Fin q)
    (f : Nat → Fin q) (orbit : ∀ n, f (n + 1) = step (f n))
    {i j : Nat} (same : f i = f j) (k : Nat) :
    f (i + k) = f (j + k) := by
  induction k with
  | zero => simpa using same
  | succ k ih =>
    rw [Nat.add_succ, Nat.add_succ, orbit, orbit, ih]

/-- A deterministic finite-state orbit is eventually periodic with positive period. -/
theorem eventually_periodic {q : Nat} (step : Fin q → Fin q)
    (f : Nat → Fin q) (orbit : ∀ n, f (n + 1) = step (f n)) :
    ∃ N p, 0 < p ∧ ∀ n, N ≤ n → f (n + p) = f n := by
  obtain ⟨i, j, hij, same⟩ := repeated_state f
  refine ⟨i, j - i, by omega, ?_⟩
  intro n hin
  have repeated := equal_at_offset step f orbit same (n - i)
  have left_index : i + (n - i) = n := by omega
  have right_index : j + (n - i) = n + (j - i) := by omega
  rw [left_index, right_index] at repeated
  exact repeated.symm

/-- Any observation determined only by the current state has the same tail period. -/
theorem observed_eventually_periodic {q : Nat} {A : Type}
    (step : Fin q → Fin q) (f : Nat → Fin q)
    (orbit : ∀ n, f (n + 1) = step (f n)) (observe : Fin q → A) :
    ∃ N p, 0 < p ∧ ∀ n, N ≤ n → observe (f (n + p)) = observe (f n) := by
  obtain ⟨N, p, hp, periodic⟩ := eventually_periodic step f orbit
  exact ⟨N, p, hp, fun n hn => congrArg observe (periodic n hn)⟩

#print axioms repeated_state
#print axioms equal_at_offset
#print axioms eventually_periodic
#print axioms observed_eventually_periodic

end FiniteStatePeriodicity
