import Std
import Init.Data.Rat.Lemmas

/-!
An exact rational-vector form of the static-mixing obstruction.

The inclusion does not require convexity: a point in every input set can be
used as every summand of any normalized weighted Minkowski combination.
This module proves that algebraic comparison, not Alexander's lifeline
existence theorem or convergence of a spaceship's paths.
-/

namespace StaticMixing

abbrev Vector := Rat × Rat
abbrev Region := Vector → Prop

def scale (a : Rat) (v : Vector) : Vector := (a * v.1, a * v.2)
def add (u v : Vector) : Vector := (u.1 + v.1, u.2 + v.2)

def weightSum {ι : Type} (indices : List ι) (weight : ι → Rat) : Rat :=
  match indices with
  | [] => 0
  | i :: rest => weight i + weightSum rest weight

def weightedSum {ι : Type} (indices : List ι) (weight : ι → Rat)
    (point : ι → Vector) : Vector :=
  match indices with
  | [] => (0, 0)
  | i :: rest => add (scale (weight i) (point i)) (weightedSum rest weight point)

theorem weightedSum_constant {ι : Type} (indices : List ι)
    (weight : ι → Rat) (v : Vector) :
    weightedSum indices weight (fun _ => v) = scale (weightSum indices weight) v := by
  induction indices with
  | nil => simp [weightedSum, weightSum, scale]
  | cons i rest ih =>
      simp only [weightedSum, weightSum, ih, add, scale]
      exact Prod.ext (Rat.add_mul _ _ _).symm (Rat.add_mul _ _ _).symm

def Normalized {ι : Type} (indices : List ι) (weight : ι → Rat) : Prop :=
  (∀ i ∈ indices, 0 ≤ weight i) ∧ weightSum indices weight = 1

def Intersection {ι : Type} (indices : List ι) (regions : ι → Region) : Region :=
  fun v => ∀ i ∈ indices, regions i v

def WeightedMix {ι : Type} (indices : List ι) (weight : ι → Rat)
    (regions : ι → Region) : Region :=
  fun v => ∃ point : ι → Vector,
    (∀ i ∈ indices, regions i (point i)) ∧ weightedSum indices weight point = v

/-- Constant-region intersection is contained in every normalized static mix. -/
theorem intersection_subset_weightedMix {ι : Type}
    (indices : List ι) (weight : ι → Rat) (regions : ι → Region)
    (normalized : Normalized indices weight) (v : Vector)
    (common : Intersection indices regions v) :
    WeightedMix indices weight regions v := by
  refine ⟨fun _ => v, common, ?_⟩
  rw [weightedSum_constant, normalized.2]
  simp [scale]

def midpoint (u v : Vector) : Vector := ((u.1 + v.1) / 2, (u.2 + v.2) / 2)

private theorem rat_midpoint_self (x : Rat) : (x + x) / 2 = x := by
  have h : x + x = x * 2 := by
    calc
      x + x = x * 1 + x * 1 := by simp
      _ = x * (1 + 1) := (Rat.mul_add _ _ _).symm
      _ = x * 2 := congrArg (fun q : Rat => x * q) (by decide +kernel)
  rw [h]
  exact Rat.mul_div_cancel (by decide)

theorem midpoint_self (v : Vector) : midpoint v v = v := by
  exact Prod.ext (rat_midpoint_self v.1) (rat_midpoint_self v.2)

def MidpointMix (a b : Region) : Region :=
  fun v => ∃ x y, a x ∧ b y ∧ midpoint x y = v

theorem intersection_subset_midpointMix (a b : Region) (v : Vector)
    (ha : a v) (hb : b v) : MidpointMix a b v := by
  exact ⟨v, v, ha, hb, midpoint_self v⟩

/-- A strict example: the two vertical half-segments meet only at (1,0). -/
def upperSegment : Region := fun v => v.1 = 1 ∧ 0 ≤ v.2 ∧ v.2 ≤ 1
def lowerSegment : Region := fun v => v.1 = 1 ∧ (-1 : Rat) ≤ v.2 ∧ v.2 ≤ 0

theorem strict_midpoint_example :
    MidpointMix upperSegment lowerSegment (1, (1 : Rat) / 2) ∧
    ¬ (upperSegment (1, (1 : Rat) / 2) ∧ lowerSegment (1, (1 : Rat) / 2)) := by
  constructor
  · refine ⟨(1, 1), (1, 0), ?_, ?_, ?_⟩
    · unfold upperSegment; decide +kernel
    · unfold lowerSegment; decide +kernel
    · unfold midpoint; decide +kernel
  · unfold upperSegment lowerSegment; decide +kernel

end StaticMixing
