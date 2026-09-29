import PedigreeBlockGraph
import PedigreeBlockProbability
import PedigreeBlockObservation

set_option autoImplicit false

/-!
Exact recovery probability for a one-generation sampled-family partition
from the actual graph of observed symbol matches. The symbol assignment must
be injective in (family, parental choice) at each block. This requirement is
not inferred from real genomic sequences or the Wong ARG law.
-/

noncomputable section

namespace PedigreeBlock

open MeasureTheory
open scoped ENNReal BigOperators

universe u v

 theorem connected_iff_not_bad {n B : Nat} (hB : 0 < B) (x : Config n B) :
    Connected x ↔ ¬ Bad x := by
  classical
  simpa only [not_not] using (not_congr (not_connected_iff_bad hB x))

 theorem connected_probability (n B : Nat) (hB : 0 < B) :
    configLaw n B {x | Connected x} =
      1 - ((2 ^ n - 1 : Nat) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ (B * n) := by
  have hset : {x : Config n B | Connected x} = {x | ¬ Bad x} := by
    ext x
    exact connected_iff_not_bad hB x
  rw [hset]
  exact good_probability n B hB

/-- The probability of exact recovery of the sampled family partition by
connected components of the actual observed-symbol sharing graph. -/
theorem recovered_probability {Family : Type u} [Fintype Family]
    {Symbol : Type v} (n : Family → Nat) (B : Nat) (hB : 0 < B)
    (symbols : Fin B → Family × Bool → Symbol)
    (hinj : ∀ j, Function.Injective (symbols j)) :
    familyLaw n B {x | Recovered x symbols} =
      ∏ i, (1 - ((2 ^ (n i) - 1 : Nat) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ (B * n i)) := by
  have hset : {x : ∀ i, Config (n i) B | Recovered x symbols} =
      {x | ∀ i, ¬ Bad (x i)} := by
    ext x
    change Recovered x symbols ↔ ∀ i, ¬ Bad (x i)
    rw [recovered_iff_connected x symbols hinj]
    exact forall_congr' (fun i => connected_iff_not_bad hB (x i))
  rw [hset]
  exact families_good_probability n B hB

/-- Correctness predicate on observed data alone, relative to the target
sampled-family partition. It stores no latent choice array. -/
def OutputRecovered {Family : Type u} {Symbol : Type v} {B : Nat}
    (n : Family → Nat) (obs : Children n → Fin B → Symbol) : Prop :=
  ∀ a b : Children n, Relation.ReflTransGen (ObservedShare obs) a b ↔ a.1 = b.1

/-- The actual law of the observed symbol array. The finite alphabet may be
arbitrarily relabeled; its parent-symbol assignment is supplied separately. -/
def observationLaw {Family : Type u} [Fintype Family]
    {Symbol : Type v} [Fintype Symbol] [MeasurableSpace Symbol]
    [MeasurableSingletonClass Symbol] (n : Family → Nat) (B : Nat)
    (symbols : Fin B → Family × Bool → Symbol) :
    Measure (Children n → Fin B → Symbol) :=
  (familyLaw n B).map (fun x => familyObservations x symbols)

instance observationLaw_probability {Family : Type u} [Fintype Family]
    {Symbol : Type v} [Fintype Symbol] [MeasurableSpace Symbol]
    [MeasurableSingletonClass Symbol] (n : Family → Nat) (B : Nat)
    (symbols : Fin B → Family × Bool → Symbol) :
    IsProbabilityMeasure (observationLaw n B symbols) :=
  Measure.isProbabilityMeasure_map (measurable_of_finite _).aemeasurable

/-- The exact recovery formula directly under the observed-output law. -/
theorem output_recovery_probability {Family : Type u} [Fintype Family]
    {Symbol : Type v} [Fintype Symbol] [MeasurableSpace Symbol]
    [MeasurableSingletonClass Symbol] (n : Family → Nat) (B : Nat) (hB : 0 < B)
    (symbols : Fin B → Family × Bool → Symbol)
    (hinj : ∀ j, Function.Injective (symbols j)) :
    observationLaw n B symbols {obs | OutputRecovered n obs} =
      ∏ i, (1 - ((2 ^ (n i) - 1 : Nat) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ (B * n i)) := by
  calc
    observationLaw n B symbols {obs | OutputRecovered n obs} =
        familyLaw n B {x | Recovered x symbols} := by
      rw [observationLaw, Measure.map_apply (measurable_of_finite _)
        (Set.toFinite _).measurableSet]
      rfl
    _ = _ := recovered_probability n B hB symbols hinj

end PedigreeBlock

#print axioms PedigreeBlock.connected_probability
#print axioms PedigreeBlock.recovered_probability

#print axioms PedigreeBlock.observationLaw_probability
#print axioms PedigreeBlock.output_recovery_probability
