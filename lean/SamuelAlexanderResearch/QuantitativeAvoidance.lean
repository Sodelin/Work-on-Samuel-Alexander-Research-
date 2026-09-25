import SamuelAlexanderResearch.BinaryAvoidance

/-! A finite periodic prefix supplies an explicit long match in its own
target-dependent avoiding graph. This is a lower-bound tool, not a claim
that an arbitrary aperiodic word has a prescribed growth rate. -/

namespace QuantitativeAvoidance
open BinaryAvoidance

def MatchesPrefix (s : Nat → Bool) (path : Nat → Nat) (len : Nat) : Prop :=
  ∀ k, k < len → Edge s (path k) (path (k + 1)) (s k)

/-- An initial period p lasting len comparisons gives a len-edge path
starting at 2p-1, by always taking the two-step edge. -/
theorem periodic_prefix_gives_match (s : Nat → Bool) (p len : Nat)
    (hp : 0 < p) (period : ∀ k, k < len → s (k + p) = s k) :
    ∃ path : Nat → Nat, path 0 = 2 * p - 1 ∧ MatchesPrefix s path len := by
  let path := fun k => 2 * k + (2 * p - 1)
  refine ⟨path, by simp [path], ?_⟩
  intro k hk
  have hw : path (k + 1) = 2 * (k + p) + 1 := by dsimp [path]; omega
  refine ⟨by dsimp [path]; omega, Or.inr ⟨by dsimp [path]; omega, ?_⟩⟩
  rw [hw, row_odd, Bool.not_not, period k hk]

/-- The same formula supplies an infinite realization for a fully periodic
target; no finite evidence is used to infer periodicity. -/
theorem periodic_target_two_step_path (s : Nat → Bool) (p : Nat)
    (hp : 0 < p) (period : ∀ k, s (k + p) = s k) :
    Matches s (fun k => 2 * k + (2 * p - 1)) := by
  intro k
  change Edge s (2 * k + (2 * p - 1)) (2 * (k + 1) + (2 * p - 1)) (s k)
  have hw : 2 * (k + 1) + (2 * p - 1) = 2 * (k + p) + 1 := by omega
  refine ⟨by omega, Or.inr ⟨by omega, ?_⟩⟩
  rw [hw, row_odd, Bool.not_not, period k]

end QuantitativeAvoidance
