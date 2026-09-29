import FiniteEpigenetic
import DeterministicEpigenetic

/-!
A matched comparison of the explicit finite and deterministic recurrences.
The finite value is the limit identified by FiniteEpigenetic.fixation_probability_limit.
The deterministic inequality holds at every biological generation >= 4 and does
not require a supplied convergence hypothesis.
-/
namespace RankingReversal

theorem matched_reversal (n : ℕ) :
    FiniteEpigenetic.reproductiveIsolation false <
      FiniteEpigenetic.reproductiveIsolation true ∧
    (1-8*((DeterministicEpigenetic.inductionTrajectory (n+3)).1+
      (DeterministicEpigenetic.inductionTrajectory (n+3)).2)/2) <
      DeterministicEpigenetic.geneticRI (n+3) :=
  ⟨FiniteEpigenetic.epigenetic_strictly_greater,
   DeterministicEpigenetic.deterministic_ranking_strict n⟩

theorem genetic_barrier_changes_sides (n : ℕ) :
    FiniteEpigenetic.reproductiveIsolation false < (3/7 : ℝ) ∧
    (3/7 : ℝ) < DeterministicEpigenetic.geneticRI (n+3) := by
  constructor
  · have h := FiniteEpigenetic.epigenetic_strictly_greater
    simpa only [FiniteEpigenetic.epigenetic_result] using h
  · exact (DeterministicEpigenetic.deterministic_genetic_tail_bound n).2

theorem certified_gap_between_models (n : ℕ) :
    (1027087570805/2255346713174 : ℝ) - (937945083/2233177303 : ℝ) ≤
      DeterministicEpigenetic.geneticRI (n+3) -
        FiniteEpigenetic.reproductiveIsolation false := by
  rw [FiniteEpigenetic.genetic_result]
  exact sub_le_sub_right (DeterministicEpigenetic.deterministic_genetic_tail_bound n).1 _

#print axioms matched_reversal
#print axioms genetic_barrier_changes_sides
#print axioms certified_gap_between_models
end RankingReversal
