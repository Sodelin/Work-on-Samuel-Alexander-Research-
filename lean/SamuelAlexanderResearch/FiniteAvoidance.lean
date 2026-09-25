import SamuelAlexanderResearch.PositiveUnavoidability
import SamuelAlexanderResearch.FiniteEditStability
import SamuelAlexanderResearch.SlowAvoidance

/-!
Aperiodic own-target avoidance has an attained finite maximum at every start.
The endpoint bound is derived from actual finite branching and absence of an
infinite match; no finite bound or compactness statement is an endpoint premise.
-/

namespace FiniteAvoidance
open BinaryAvoidance QuantitativeAvoidance FiniteEditStability
open SpeciesBridge PositiveUnavoidability

/-- Actual function-path prefixes give the inductive finite paths used by the
already checked finite-branching argument, with the same start and endpoint. -/
theorem prefix_to_finitePath (s : Nat → Bool) (path : Nat → Nat) (ell : Nat)
    (hm : MatchesPrefix s path ell) :
    FinitePath (Edge s) s 0 ell (path 0) (path ell) := by
  induction ell with
  | zero => exact .nil _ _
  | succ ell ih =>
    have hfront := ih (fun k hk => hm k (by omega))
    exact hfront.snoc (by simpa using hm ell (by omega))

/-- Aperiodicity and the actual finite child sets force bounded reachable
endpoints from each specified start, including zero. -/
theorem aperiodic_endpoints_bounded (s : Nat → Bool)
    (ha : ¬EventuallyPeriodic s) (v : Nat) :
    BoundedSupport (Endpoint (Edge s) s 0 v) := by
  classical
  apply Classical.byContradiction
  intro hgood
  obtain ⟨path, _, hm⟩ := infinite_path_from_good (Edge s) s
    (BinaryPopulation.children_finite s) 0 v hgood
  apply aperiodic_target_avoided s ha
  exact ⟨path, by simpa [Matches] using hm⟩

/-- This finite length bound is obtained as a conclusion, not supplied as data. -/
theorem aperiodic_prefix_lengths_bounded (s : Nat → Bool)
    (ha : ¬EventuallyPeriodic s) (v : Nat) :
    ∃ bound, ∀ ell, HasPrefix s v ell → ell ≤ bound := by
  obtain ⟨bound, hb⟩ := aperiodic_endpoints_bounded s ha v
  refine ⟨bound, ?_⟩
  intro ell hp
  obtain ⟨path, hzero, hm⟩ := hp
  have hfinite := prefix_to_finitePath s path ell hm
  rw [hzero] at hfinite
  have hend := hb (path ell) ⟨ell, hfinite⟩
  have hlen := prefix_displacement s path ell hm ell (Nat.le_refl _)
  omega

/-- Every starting vertex in P_s has a genuine attained finite maximum whenever
s is not eventually periodic. No positivity restriction on the start is needed. -/
theorem aperiodic_maximum_exists (s : Nat → Bool)
    (ha : ¬EventuallyPeriodic s) (v : Nat) :
    ∃ ell, IsMaximumPrefix s v ell := by
  obtain ⟨bound, hb⟩ := aperiodic_prefix_lengths_bounded s ha v
  exact bounded_prefix_maximum s v bound hb

/-- An explicit extinction formulation: the maximum is attained and no longer
actual matching prefix exists, for all starts including zero. -/
theorem aperiodic_finite_extinction (s : Nat → Bool)
    (ha : ¬EventuallyPeriodic s) (v : Nat) :
    ∃ ell, HasPrefix s v ell ∧ ∀ len, ell < len → ¬HasPrefix s v len := by
  obtain ⟨ell, hm⟩ := aperiodic_maximum_exists s ha v
  refine ⟨ell, hm.1, ?_⟩
  intro len hlong hp
  have hle := hm.2 len hp
  omega

/-- The slow-avoidance construction has finite maxima at every start, and its
actual maxima exceed any prescribed f along strictly increasing starts. -/
theorem arbitrarily_slow_finite_maxima (f : Nat → Nat) :
    ∃ (s : Nat → Bool) (starts : Nat → Nat), ¬EventuallyPeriodic s ∧
      (¬∃ path, Matches s path) ∧
      (∀ v, ∃ ell, IsMaximumPrefix s v ell) ∧
      (∀ i j, i < j → starts i < starts j) ∧
      ∀ j, ∃ ell, IsMaximumPrefix s (starts j) ell ∧ f (starts j) < ell := by
  obtain ⟨s, ha, hno, starts, hstrict, hlong⟩ := SlowAvoidance.arbitrarily_slow_avoidance f
  refine ⟨s, starts, ha, hno, aperiodic_maximum_exists s ha, hstrict, ?_⟩
  intro j
  obtain ⟨len, hbig, path, hzero, hm⟩ := hlong j
  obtain ⟨ell, hmax⟩ := aperiodic_maximum_exists s ha (starts j)
  have hle := hmax.2 len ⟨path, hzero, hm⟩
  exact ⟨ell, hmax, by omega⟩

#print axioms prefix_to_finitePath
#print axioms aperiodic_endpoints_bounded
#print axioms aperiodic_prefix_lengths_bounded
#print axioms aperiodic_maximum_exists
#print axioms aperiodic_finite_extinction
#print axioms arbitrarily_slow_finite_maxima

end FiniteAvoidance
