import PureInductionPaths

/-! The exact finite marker kernel and the almost-sure ancestry theorem
belong to the same explicitly constructed random process.
The verification receipt records the checked state of this source. -/

open MeasureTheory Set
open scoped ENNReal BigOperators
open PureInductionJoint PureInductionR1R2 PureInductionNoise PureInductionPaths

namespace PureInductionAncestry
noncomputable section

theorem raw_card : Fintype.card RawNoise = 38416 := by
  norm_num [RawNoise, Fintype.card_pi, Fintype.card_fin]

theorem raw_measure_card (E : RawNoise → Prop) [DecidablePred E] :
    stepLaw {u | E u} =
      (((Finset.univ : Finset RawNoise).filter E).card : ℝ≥0∞) / 38416 := by
  classical
  unfold stepLaw UniformParentProcess.oneStep
  rw [PMF.toMeasure_uniformOfFintype_apply _ (Set.toFinite _).measurableSet]
  rw [Fintype.card_subtype, raw_card]
  simp only [Set.mem_setOf_eq, Nat.cast_ofNat]

theorem raw_measure_ofReal (E : RawNoise → Prop) [DecidablePred E] :
    stepLaw {u | E u} =
      ENNReal.ofReal ((((Finset.univ : Finset RawNoise).filter E).card : ℝ) / 38416) := by
  rw [raw_measure_card, ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 38416)]
  simp only [ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat]

theorem raw_record_mass (p : Table) (h : Homologues) :
    stepLaw {u | rawParent u = p ∧ rawHomologue u = h} =
      (tableWeight p : ℝ≥0∞) / 38416 := by
  rw [raw_measure_card, raw_fibre_filter_card]

theorem ordinary_mass (b c : BState) :
    stepLaw {u | ordinaryState b u = c} =
      ENNReal.ofReal ((FiniteEpigenetic.kernel true).transition (embed b) (embed c)) := by
  rw [raw_measure_ofReal]
  exact congrArg ENNReal.ofReal (ordinary_all_real b c)

theorem pulse_mass (c : BState) :
    stepLaw {u | pulseState u = c} =
      ENNReal.ofReal (FiniteEpigenetic.pulse true (embed c)) := by
  rw [raw_measure_ofReal]
  exact congrArg ENNReal.ofReal (pulse_all_real c)

/-- Transition zero is the pulse; all subsequent transitions are ordinary. -/
def frozenMass (n : Nat) (b c : BState) : ℝ≥0∞ :=
  ENNReal.ofReal (if n = 0 then FiniteEpigenetic.pulse true (embed c)
    else (FiniteEpigenetic.kernel true).transition (embed b) (embed c))

theorem stepMass_eq_frozen (n : Nat) (b c : BState) :
    stepMass n b c = frozenMass n b c := by
  by_cases hn : n = 0
  · simpa [stepMass, update, frozenMass, hn] using pulse_mass c
  · simpa [stepMass, update, frozenMass, hn] using ordinary_mass b c

/-- All finite count paths of the actual iid-driven process have the frozen
pulse/kernel product probabilities, including the empty transition window. -/
theorem finite_path_frozen (n : Nat) (z : Nat → BState) (hz : z 0 = (0, 0)) :
    law (pathEvent n z) = ∏ t ∈ Finset.range n, frozenMass t (z t) (z (t+1)) := by
  rw [path_probability_product n z hz]
  apply Finset.prod_congr rfl
  intro t _
  exact stepMass_eq_frozen t (z t) (z (t+1))

theorem shared_mass :
    stepLaw Shared = ENNReal.ofReal ((36 : ℝ) / 2401) := by
  unfold Shared
  rw [raw_measure_ofReal, raw_designated_numerator]
  congr 1
  norm_num

theorem shared_complement_mass :
    stepLaw Sharedᶜ = ENNReal.ofReal ((2365 : ℝ) / 2401) := by
  rw [prob_compl_eq_one_sub (Set.toFinite Shared).measurableSet, shared_mass]
  have h : (2365 : ℝ) / 2401 = 1 - 36 / 2401 := by norm_num
  rw [h, ENNReal.ofReal_sub 1 (by norm_num : (0 : ℝ) ≤ 36 / 2401)]
  norm_num

theorem shared_avoidance_exact (a k : Nat) :
    law (Avoid Shared a k) = ENNReal.ofReal (((2365 : ℝ) / 2401)^k) := by
  rw [avoidance_exact, shared_complement_mass, ENNReal.ofReal_pow (by norm_num)]

theorem shared_history_exact (a k : Nat) (H : Set (History a)) :
    law (pastEvent a H ∩ Avoid Shared a k) =
      law (pastEvent a H) * ENNReal.ofReal (((2365 : ℝ) / 2401)^k) := by
  rw [history_avoid_inter, shared_complement_mass, ENNReal.ofReal_pow (by norm_num)]

theorem shared_conditional_exact (a k : Nat) (H : Set (History a))
    (hH : law (pastEvent a H) ≠ 0) :
    law (pastEvent a H ∩ Avoid Shared a k) / law (pastEvent a H) =
      ENNReal.ofReal (((2365 : ℝ) / 2401)^k) := by
  rw [history_avoid_conditional Shared a k H hH, shared_complement_mass,
    ENNReal.ofReal_pow (by norm_num)]

theorem resolution_bound (u a k : Nat) (hu : u/2 < a) :
    law {ω | ¬ (pedigree ω).ResolvedFrom u (a+k)} ≤
      ENNReal.ofReal (((2365 : ℝ) / 2401)^k) := by
  simpa only [shared_complement_mass, ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2365/2401)]
    using unresolved_probability_bound u a k hu

theorem resolution_conditional_bound (u a k : Nat) (hu : u/2 < a)
    (H : Set (History a)) (hH : law (pastEvent a H) ≠ 0) :
    law (pastEvent a H ∩ {ω | ¬ (pedigree ω).ResolvedFrom u (a+k)}) /
      law (pastEvent a H) ≤ ENNReal.ofReal (((2365 : ℝ) / 2401)^k) := by
  simpa only [shared_complement_mass, ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2365/2401)]
    using unresolved_conditional_bound u a k hu H hH

/-- The frozen kernel statistic equals 3/7, its finite count paths are realized
by this actual law, and its parent graph satisfies whole-history IAP.
No separate raw-path eventual-fixation event is identified by this theorem. -/
theorem marker_barrier_and_iap :
    FiniteEpigenetic.reproductiveIsolation true = 3/7 ∧
    (∀ n z, z 0 = (0, 0) →
      law (pathEvent n z) = ∏ t ∈ Finset.range n, frozenMass t (z t) (z (t+1))) ∧
    (∀ᵐ ω ∂law, SpeciesBridge.IAP (pedigree ω).edge SpeciesBridge.Whole) := by
  exact ⟨FiniteEpigenetic.epigenetic_result, finite_path_frozen, actual_parent_ae_iap⟩

theorem marker_barrier_positive :
    0 < FiniteEpigenetic.reproductiveIsolation true := by
  rw [FiniteEpigenetic.epigenetic_result]
  norm_num

end
end PureInductionAncestry

#print axioms PureInductionAncestry.raw_record_mass
#print axioms PureInductionAncestry.ordinary_mass
#print axioms PureInductionAncestry.pulse_mass
#print axioms PureInductionAncestry.finite_path_frozen
#print axioms PureInductionAncestry.shared_mass
#print axioms PureInductionAncestry.shared_avoidance_exact
#print axioms PureInductionAncestry.shared_history_exact
#print axioms PureInductionAncestry.shared_conditional_exact
#print axioms PureInductionAncestry.resolution_bound
#print axioms PureInductionAncestry.resolution_conditional_bound
#print axioms PureInductionAncestry.marker_barrier_and_iap
