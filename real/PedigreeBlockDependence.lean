import PedigreeBlockProbability
import PedigreeBlockGraph

set_option autoImplicit false

/-!
# Correct single-block marginals without independent blocks

Draw one fair independent choice per child from configLaw n 1, then repeat
that choice at every observed block. This actual pushforward law has the
correct joint law across children at each individual block. Among positive
block counts, adding blocks never changes its sharing graph or recovery probability.

The construction is an observation-law counterexample. It is not coupled
to Wong's continuous ARG process and makes no claim about its recombination
parameter.
-/

namespace PedigreeBlock

open MeasureTheory
open scoped ENNReal Classical
noncomputable section

def repeatBlock (B : ℕ) {n : ℕ} (x : Config n 1) : Config n B :=
  fun i _ => x i 0

/-- Read one block, represented as a one-block configuration on the same
labeled children. -/
def readBlock {n B : ℕ} (b : Fin B) (x : Config n B) : Config n 1 :=
  fun i _ => x i b

theorem readBlock_repeatBlock {n B : ℕ} (b : Fin B) (x : Config n 1) :
    readBlock b (repeatBlock B x) = x := by
  funext i j
  have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
  subst j
  rfl

theorem repeatBlock_share_iff {n B : ℕ} (hB : 0 < B) (x : Config n 1)
    (a b : Fin (n+1)) : Share (repeatBlock B x) a b ↔ Share x a b := by
  constructor
  · rintro ⟨different,j,agree⟩
    exact ⟨different,0,agree⟩
  · rintro ⟨different,j,agree⟩
    have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
    subst j
    exact ⟨different,⟨0,hB⟩,agree⟩

theorem repeatBlock_connected_iff {n B : ℕ} (hB : 0 < B) (x : Config n 1) :
    Connected (repeatBlock B x) ↔ Connected x := by
  have edges : Share (repeatBlock B x) = Share x := by
    funext a b
    exact propext (repeatBlock_share_iff hB x a b)
  unfold Connected
  rw [edges]

/-- The repeated-block law is the actual measurable pushforward of the
checked uniform one-block law; no event mass is supplied as a parameter. -/
def repeatedLaw (n B : ℕ) : Measure (Config n B) :=
  (configLaw n 1).map (repeatBlock B)

instance repeatedLaw_probability (n B : ℕ) : IsProbabilityMeasure (repeatedLaw n B) :=
  Measure.isProbabilityMeasure_map
    (measurable_of_countable (repeatBlock B : Config n 1 → Config n B)).aemeasurable

/-- Each block has the entire fair, independent-across-children one-block
law, even though the blocks themselves share exactly the same choices. -/
theorem repeatedLaw_block_marginal (n B : ℕ) (b : Fin B) :
    (repeatedLaw n B).map (readBlock b) = configLaw n 1 := by
  unfold repeatedLaw
  rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  have identity : (readBlock b) ∘ (repeatBlock B : Config n 1 → Config n B) = id := by
    funext x
    exact readBlock_repeatBlock b x
  rw [identity,Measure.map_id]

/-- The entire connectedness event, and hence its probability, is unchanged
by repeating the same positive number of blocks. -/
theorem repeatedLaw_connected_eq_one_block (n B : ℕ) (hB : 0 < B) :
    repeatedLaw n B {x | Connected x} = configLaw n 1 {x | Connected x} := by
  unfold repeatedLaw
  rw [Measure.map_apply (measurable_of_countable _)
    (Set.toFinite {x : Config n B | Connected x}).measurableSet]
  congr 1
  ext x
  exact repeatBlock_connected_iff hB x

/-- General repeated-block counterexample: recovery success stays at the
one-block value for every positive B, despite correct block marginals. -/
theorem repeatedLaw_connected_probability (n B : ℕ) (hB : 0 < B) :
    repeatedLaw n B {x | Connected x} =
      1 - ((2 ^ n - 1 : ℕ) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ n := by
  rw [repeatedLaw_connected_eq_one_block n B hB]
  have event : {x : Config n 1 | Connected x} = {x | ¬ Bad x} := by
    ext x
    simpa only [Set.mem_setOf_eq,not_not] using
      not_congr (not_connected_iff_bad (Nat.zero_lt_succ 0) x)
  rw [event,good_probability n 1 (Nat.zero_lt_succ 0),Nat.one_mul]

#print axioms repeatBlock_share_iff
#print axioms repeatBlock_connected_iff
#print axioms repeatedLaw_probability
#print axioms repeatedLaw_block_marginal
#print axioms repeatedLaw_connected_eq_one_block
#print axioms repeatedLaw_connected_probability

end
end PedigreeBlock

