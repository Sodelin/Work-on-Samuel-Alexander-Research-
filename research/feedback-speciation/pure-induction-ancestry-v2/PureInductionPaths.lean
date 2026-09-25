import PureInductionR1R2
import PureInductionNoise

/-! Recursive marker paths, with the one-time pulse at generation zero.
The parents and markers use the same four raw draws at every generation.
Working continuation; compilation pending. -/

open MeasureTheory Set
open scoped ENNReal BigOperators
open PureInductionJoint PureInductionR1R2 PureInductionNoise

namespace PureInductionPaths
noncomputable section

/-- Explicit nonempty paths expose ancestry as a countable union of events. -/
def finiteWalk (E : SpeciesBridge.Graph) : Nat → Nat → Nat → Prop
  | 0, u, v => E u v
  | n+1, u, v => ∃ w, finiteWalk E n u w ∧ E w v

theorem descendant_iff_finiteWalk (E : SpeciesBridge.Graph) (u v : Nat) :
    SpeciesBridge.Descendant E u v ↔ ∃ n, finiteWalk E n u v := by
  constructor
  · intro h
    induction h with
    | edge he => exact ⟨0, he⟩
    | snoc hp he ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n+1, _, hn, he⟩
  · rintro ⟨n, hn⟩
    induction n generalizing u v with
    | zero => exact .edge hn
    | succ n ih =>
      obtain ⟨w, hw, he⟩ := hn
      exact .snoc (ih _ _ hw) he

theorem edge_measurable (u v : Nat) :
    MeasurableSet {ω : Space | (pedigree ω).edge u v} := by
  change MeasurableSet ((fun ω : Space => parents ω (u/2)) ⁻¹'
    {p : Table | v/2 = u/2+1 ∧
      ∃ s : Fin 2, (p (ParentSchedules.childIndex 2 (by decide) v) s).val = u%2})
  exact (Set.toFinite _).measurableSet.preimage
    ((measurable_pi_apply (u/2)).comp parents_measurable)

theorem finiteWalk_measurable (n u v : Nat) :
    MeasurableSet {ω : Space | finiteWalk (pedigree ω).edge n u v} := by
  induction n generalizing u v with
  | zero => exact edge_measurable u v
  | succ n ih =>
    change MeasurableSet {ω : Space |
      ∃ w, finiteWalk (pedigree ω).edge n u w ∧ (pedigree ω).edge w v}
    simp only [ofPred_exists]
    exact MeasurableSet.iUnion (fun w => (ih u w).inter (edge_measurable w v))

theorem descendant_measurable (u v : Nat) :
    MeasurableSet {ω : Space | SpeciesBridge.Descendant (pedigree ω).edge u v} := by
  simp only [descendant_iff_finiteWalk, ofPred_exists]
  exact MeasurableSet.iUnion (fun n => finiteWalk_measurable n u v)

theorem resolved_measurable (u T : Nat) :
    MeasurableSet {ω : Space | (pedigree ω).ResolvedFrom u T} := by
  have hAll : MeasurableSet {ω : Space |
      ∀ v, T ≤ v/2 → SpeciesBridge.Descendant (pedigree ω).edge u v} := by
    simp only [ofPred_forall]
    exact MeasurableSet.iInter (fun v =>
      MeasurableSet.iInter (fun _ => descendant_measurable u v))
  have hNone : MeasurableSet {ω : Space |
      ∀ v, T ≤ v/2 → ¬ SpeciesBridge.Descendant (pedigree ω).edge u v} := by
    simp only [ofPred_forall]
    exact MeasurableSet.iInter (fun v =>
      MeasurableSet.iInter (fun _ => (descendant_measurable u v).compl))
  exact hNone.union hAll

theorem unresolved_measurable (u T : Nat) :
    MeasurableSet {ω : Space | ¬ (pedigree ω).ResolvedFrom u T} :=
  (resolved_measurable u T).compl

def update (n : Nat) (b : BState) (u : RawNoise) : BState :=
  if n = 0 then pulseState u else ordinaryState b u

def countPath (ω : Space) : Nat → BState
  | 0 => (0, 0)
  | n+1 => update n (countPath ω n) (ω n)

theorem countPath_initial (ω : Space) : countPath ω 0 = (0, 0) := rfl

theorem countPath_pulse (ω : Space) : countPath ω 1 = pulseState (ω 0) := by
  simp [countPath, update]

theorem countPath_ordinary (ω : Space) (n : Nat) (hn : 0 < n) :
    countPath ω (n+1) = ordinaryState (countPath ω n) (ω n) := by
  simp only [countPath, update, if_neg (Nat.ne_of_gt hn)]

theorem countPath_measurable (n : Nat) : Measurable (fun ω => countPath ω n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have hm : Measurable (fun q : BState × RawNoise => update n q.1 q.2) :=
      measurable_of_finite _
    exact hm.comp (ih.prodMk (measurable_pi_apply n))

theorem countPath_depends_prefix :
    ∀ n ω ω', (∀ i < n, ω i = ω' i) → countPath ω n = countPath ω' n := by
  intro n
  induction n with
  | zero => intro ω ω' h; rfl
  | succ n ih =>
    intro ω ω' h
    have hp := ih ω ω' (fun i hi => h i (by omega))
    have hc := h n (Nat.lt_succ_self n)
    simp only [countPath, hp, hc]

def pathEvent (n : Nat) (z : Nat → BState) : Set Space :=
  {ω | ∀ t ≤ n, countPath ω t = z t}

def stepMass (n : Nat) (b c : BState) : ℝ≥0∞ :=
  stepLaw {u | update n b u = c}

theorem pathEvent_eq_noise_box (n : Nat) (z : Nat → BState) (hz : z 0 = (0, 0)) :
    pathEvent n z = Set.pi (Finset.range n)
      (fun t => {u | update t (z t) u = z (t+1)}) := by
  ext ω
  change (∀ t ≤ n, countPath ω t = z t) ↔
    ∀ t ∈ Finset.range n, update t (z t) (ω t) = z (t+1)
  constructor
  · intro h t ht
    have htn := Finset.mem_range.mp ht
    have hp := h t (by omega)
    have hc := h (t+1) (by omega)
    simpa only [countPath, hp] using hc
  · intro h
    have hh : ∀ t, t ≤ n → countPath ω t = z t := by
      intro t
      induction t with
      | zero => intro _; simpa only [countPath] using hz.symm
      | succ t ih =>
        intro ht
        have hp := ih (by omega)
        have hc := h t (Finset.mem_range.mpr (by omega))
        simpa only [countPath, hp] using hc
    exact hh

theorem pathEvent_measurable (n : Nat) (z : Nat → BState) (hz : z 0 = (0, 0)) :
    MeasurableSet (pathEvent n z) := by
  rw [pathEvent_eq_noise_box n z hz]
  exact MeasurableSet.pi (Finset.countable_toSet _)
    (fun _ _ => (Set.toFinite _).measurableSet)

theorem path_probability_product (n : Nat) (z : Nat → BState) (hz : z 0 = (0, 0)) :
    law (pathEvent n z) =
      ∏ t ∈ Finset.range n, stepMass t (z t) (z (t+1)) := by
  rw [pathEvent_eq_noise_box n z hz]
  change Measure.infinitePi (fun _ : Nat => stepLaw)
    (Set.pi (Finset.range n) (fun t => {u | update t (z t) u = z (t+1)})) = _
  rw [Measure.infinitePi_pi _ (fun _ _ => (Set.toFinite _).measurableSet)]
  rfl

def coupled (ω : Space) : (Nat → BState) × ParentSchedules.Schedule 2 :=
  (countPath ω, parents ω)

theorem coupled_measurable : Measurable coupled := by
  exact (measurable_pi_iff.mpr countPath_measurable).prodMk parents_measurable

def jointLaw : Measure ((Nat → BState) × ParentSchedules.Schedule 2) :=
  law.map coupled

instance jointLaw_probability : IsProbabilityMeasure jointLaw :=
  Measure.isProbabilityMeasure_map coupled_measurable.aemeasurable

theorem joint_parent_projection :
    jointLaw.map Prod.snd = Measure.infinitePi (fun _ : Nat => stepLaw.map rawParent) := by
  unfold jointLaw
  rw [Measure.map_map measurable_snd coupled_measurable]
  exact parent_schedule_law

end
end PureInductionPaths

#print axioms PureInductionPaths.countPath_measurable
#print axioms PureInductionPaths.countPath_depends_prefix
#print axioms PureInductionPaths.pathEvent_eq_noise_box
#print axioms PureInductionPaths.path_probability_product
#print axioms PureInductionPaths.coupled_measurable
#print axioms PureInductionPaths.joint_parent_projection

#print axioms PureInductionPaths.unresolved_measurable
