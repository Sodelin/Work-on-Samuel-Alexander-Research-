import PureInductionJoint
import UniformParentProcess
import Mathlib.Probability.Independence.InfinitePi

/-! Actual iid raw noise and its nonuniform parent projection.
Working continuation of the frozen finite checkpoint. Compilation is pending.
No count-path marginal is asserted in this module. -/

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal BigOperators
open PureInductionJoint

namespace PureInductionNoise
noncomputable section

abbrev Space := Nat → RawNoise

def stepLaw : Measure RawNoise := UniformParentProcess.oneStep RawNoise

instance stepLaw_probability : IsProbabilityMeasure stepLaw := by
  unfold stepLaw
  infer_instance

def law : Measure Space := UniformParentProcess.streamLaw RawNoise

instance law_probability : IsProbabilityMeasure law := by
  unfold law
  infer_instance

def parents (ω : Space) : ParentSchedules.Schedule 2 :=
  fun n => rawParent (ω n)

def pedigree (ω : Space) : ExtinctionPedigree.Model :=
  ParentSchedules.model 2 (by decide) (parents ω)

theorem parents_measurable : Measurable parents := by
  apply measurable_pi_iff.mpr
  intro n
  exact (measurable_of_finite rawParent).comp (measurable_pi_apply n)

theorem parent_schedule_law :
    law.map parents = Measure.infinitePi (fun _ : Nat => stepLaw.map rawParent) := by
  change (Measure.infinitePi (fun _ : Nat => stepLaw)).map
    (fun ω n => rawParent (ω n)) = _
  exact Measure.infinitePi_map_pi _ (fun _ => measurable_of_finite rawParent)

def sharedNoise : RawNoise := fun d s => if d = s then 0 else 6

theorem shared_noise_parent :
    rawParent sharedNoise = ParentSchedules.constantTable (fun s : Fin 2 => s) := by
  funext d s
  fin_cases d <;> fin_cases s <;> rfl

theorem designated_iff_constant (p : Table) :
    designated p = true ↔ p = ParentSchedules.constantTable (fun s : Fin 2 => s) := by
  revert p
  decide +kernel

def Shared : Set RawNoise := {u | designated (rawParent u) = true}

theorem actual_parent_ae_iap :
    ∀ᵐ ω ∂law, SpeciesBridge.IAP (pedigree ω).edge SpeciesBridge.Whole := by
  have hr := UniformParentProcess.ae_recurrent sharedNoise
  filter_upwards [hr] with ω hω
  apply ParentSchedules.recurrent_constant_table_iap 2 (by decide) (parents ω)
    (fun s : Fin 2 => s)
  intro a
  obtain ⟨n, hn, he⟩ := hω a
  refine ⟨n, hn, ?_⟩
  simpa only [parents, he] using shared_noise_parent

def Avoid (E : Set RawNoise) (a k : Nat) : Set Space :=
  Set.pi (Finset.Ico a (a+k)) (fun _ => Eᶜ)

theorem avoidance_exact (E : Set RawNoise) (a k : Nat) :
    law (Avoid E a k) = (stepLaw Eᶜ)^k := by
  unfold law UniformParentProcess.streamLaw Avoid stepLaw
  rw [Measure.infinitePi_pi _ (fun _ _ => (Set.toFinite E).measurableSet.compl)]
  simp only [Finset.prod_const, Nat.card_Ico, Nat.add_sub_cancel_left]

abbrev History (a : Nat) := (i : Finset.range a) → RawNoise

def pastEvent (a : Nat) (H : Set (History a)) : Set Space :=
  {ω | (fun i : Finset.range a => ω i.val) ∈ H}

theorem pastEvent_measurable (a : Nat) (H : Set (History a)) :
    MeasurableSet (pastEvent a H) := by
  exact (Set.toFinite H).measurableSet.preimage (by fun_prop)

theorem history_avoid_inter (E : Set RawNoise) (a k : Nat) (H : Set (History a)) :
    law (pastEvent a H ∩ Avoid E a k) =
      law (pastEvent a H) * (stepLaw Eᶜ)^k := by
  have hd : Disjoint (Finset.range a) (Finset.Ico a (a+k)) := by
    apply Finset.disjoint_left.mpr
    intro n hn hm
    have h0 := Finset.mem_range.mp hn
    have h1 := (Finset.mem_Ico.mp hm).1
    omega
  have hi : iIndepFun (fun (n : Nat) (ω : Space) => ω n) law := by
    change iIndepFun (fun (n : Nat) (ω : Space) => ω n)
      (Measure.infinitePi (fun _ : Nat => stepLaw))
    exact iIndepFun_infinitePi
      (X := fun (_ : Nat) (u : RawNoise) => u) (fun _ => measurable_id)
  have hij := iIndepFun.indepFun_finset (Finset.range a) (Finset.Ico a (a+k))
    hd hi (fun n => measurable_pi_apply n)
  let W : Set ((i : Finset.Ico a (a+k)) → RawNoise) := {x | ∀ i, x i ∉ E}
  have hW : MeasurableSet W := (Set.toFinite W).measurableSet
  have he : (fun (ω : Space) (i : Finset.Ico a (a+k)) => ω i.val) ⁻¹' W =
      Avoid E a k := by
    ext ω
    change (∀ i : Finset.Ico a (a+k), ω i.val ∉ E) ↔
      ∀ n ∈ Finset.Ico a (a+k), ω n ∉ E
    constructor
    · intro h n hn
      exact h ⟨n, hn⟩
    · intro h i
      exact h i.val i.property
  have h := hij.measure_inter_preimage_eq_mul H W
    (Set.toFinite H).measurableSet hW
  rw [he, avoidance_exact] at h
  exact h

theorem history_avoid_conditional (E : Set RawNoise) (a k : Nat)
    (H : Set (History a)) (hH : law (pastEvent a H) ≠ 0) :
    law (pastEvent a H ∩ Avoid E a k) / law (pastEvent a H) = (stepLaw Eᶜ)^k := by
  rw [history_avoid_inter, mul_comm]
  exact ENNReal.mul_div_cancel_right hH (measure_ne_top law _)

theorem unresolved_subset_avoid (u a k : Nat) (hu : u/2 < a) :
    {ω | ¬ (pedigree ω).ResolvedFrom u (a+k)} ⊆ Avoid Shared a k := by
  intro ω hω
  change ∀ n ∈ Finset.Ico a (a+k), ω n ∉ Shared
  intro n hn hs
  have hnt := Finset.mem_Ico.mp hn
  have hp : parents ω n = ParentSchedules.constantTable (fun s : Fin 2 => s) :=
    (designated_iff_constant _).mp hs
  have hr := ParentSchedules.constant_table_resolves_older 2 (by decide)
    (parents ω) n u (fun s : Fin 2 => s) hp (by omega)
  apply hω
  rcases hr with hnone | hall
  · exact Or.inl (fun v hv => hnone v (Nat.le_trans (by omega) hv))
  · exact Or.inr (fun v hv => hall v (Nat.le_trans (by omega) hv))

theorem unresolved_probability_bound (u a k : Nat) (hu : u/2 < a) :
    law {ω | ¬ (pedigree ω).ResolvedFrom u (a+k)} ≤ (stepLaw Sharedᶜ)^k := by
  rw [← avoidance_exact Shared a k]
  exact measure_mono (unresolved_subset_avoid u a k hu)

theorem unresolved_history_bound (u a k : Nat) (hu : u/2 < a)
    (H : Set (History a)) :
    law (pastEvent a H ∩ {ω | ¬ (pedigree ω).ResolvedFrom u (a+k)}) ≤
      law (pastEvent a H) * (stepLaw Sharedᶜ)^k := by
  rw [← history_avoid_inter Shared a k H]
  apply measure_mono
  intro ω hω
  exact ⟨hω.1, unresolved_subset_avoid u a k hu hω.2⟩

theorem unresolved_conditional_bound (u a k : Nat) (hu : u/2 < a)
    (H : Set (History a)) (hH : law (pastEvent a H) ≠ 0) :
    law (pastEvent a H ∩ {ω | ¬ (pedigree ω).ResolvedFrom u (a+k)}) /
      law (pastEvent a H) ≤ (stepLaw Sharedᶜ)^k := by
  apply (ENNReal.div_le_iff' hH (measure_ne_top law _)).mpr
  exact unresolved_history_bound u a k hu H

end
end PureInductionNoise

#print axioms PureInductionNoise.parent_schedule_law
#print axioms PureInductionNoise.actual_parent_ae_iap
#print axioms PureInductionNoise.avoidance_exact
#print axioms PureInductionNoise.history_avoid_inter
#print axioms PureInductionNoise.history_avoid_conditional
#print axioms PureInductionNoise.unresolved_probability_bound
#print axioms PureInductionNoise.unresolved_history_bound
#print axioms PureInductionNoise.unresolved_conditional_bound
