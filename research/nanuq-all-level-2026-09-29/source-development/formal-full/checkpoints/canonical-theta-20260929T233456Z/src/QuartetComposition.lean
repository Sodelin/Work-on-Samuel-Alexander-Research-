import QuartetSemantics
import Mathlib.Tactic.Ring

/-!
Exact rational mass-counting and cancellation in the blob-composition argument.
The graph-theoretic switching identity and the quartet-localization identity are
explicit hypotheses of `source_composition_of_switching_and_localization`.
This theorem does not claim those identities for raw source networks by itself.
-/

namespace Nanuq.Composition

open scoped BigOperators

variable {X P B : Type*} [Fintype X] [Fintype P] [Fintype B]
  [DecidableEq X] [DecidableEq P]

/-- Number of original taxa attached at a port, retained as an exact rational. -/
def portMass (project : X → P) (p : P) : ℚ :=
  ((Finset.univ.filter fun x => project x = p).card : ℚ)

/-- Counting by ports is a theorem, not a mass-counting hypothesis. -/
theorem sum_by_ports (project : X → P) (f : P → ℚ) :
    (∑ x, f (project x)) = ∑ p, portMass project p * f p := by
  rw [← Finset.sum_fiberwise' Finset.univ project f]
  simp only [Finset.sum_const, nsmul_eq_mul, portMass]

theorem sum_pairs_by_ports (project : X → P) (f : P → P → ℚ) :
    (∑ x, ∑ y, f (project x) (project y)) =
      ∑ p, ∑ q, portMass project p * portMass project q * f p q := by
  rw [sum_by_ports project (fun p => ∑ y, f p (project y))]
  simp_rw [sum_by_ports project, Finset.mul_sum, mul_assoc]

theorem portMass_pos_of_surjective (project : X → P)
    (hproject : Function.Surjective project) (p : P) :
    0 < portMass project p := by
  obtain ⟨x, hx⟩ := hproject p
  have hcard : 0 < (Finset.univ.filter fun x => project x = p).card :=
    Finset.card_pos.mpr ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩⟩
  unfold portMass
  exact_mod_cast hcard

theorem total_portMass (project : X → P) :
    (∑ p, portMass project p) = Fintype.card X := by
  simpa using (sum_by_ports project (fun _ => 1)).symm

/-- Ordered-pair form of the source sum. A proper quartet tensor is zero whenever
the four taxa are not distinct; symmetry in z,w makes this equal to twice the
unordered-pair sum in the paper. The diagonal is explicitly zero. -/
def sourceDistance (rho : X → X → X → X → ℚ) (x y : X) : ℚ :=
  if x = y then 0 else (∑ z, ∑ w, rho x y z w) + 2 * Fintype.card X - 4

def localWeighted (rho : P → P → P → P → ℚ) (m : P → ℚ) (a b : P) : ℚ :=
  if a = b then 0 else
    (∑ c, ∑ d, m c * m d * rho a b c d) +
      (m a + m b) * (∑ c ∈ Finset.univ.filter (fun c => c ≠ a ∧ c ≠ b), m c)

def sourceError (rho rhoSw : X → X → X → X → ℚ) (x y : X) : ℚ :=
  if x = y then 0 else ∑ z, ∑ w, (rho x y z w - rhoSw x y z w)

def localError (rho rhoSw : P → P → P → P → ℚ) (m : P → ℚ) (a b : P) : ℚ :=
  if a = b then 0 else ∑ c, ∑ d, m c * m d * (rho a b c d - rhoSw a b c d)

theorem source_eq_switching_add_error (rho rhoSw : X → X → X → X → ℚ)
    (x y : X) :
    sourceDistance rho x y = sourceDistance rhoSw x y + sourceError rho rhoSw x y := by
  by_cases h : x = y
  · simp [sourceDistance, sourceError, h]
  · simp only [sourceDistance, sourceError, h, if_false, Finset.sum_sub_distrib]
    ring

theorem local_eq_switching_add_error (rho rhoSw : P → P → P → P → ℚ)
    (m : P → ℚ) (a b : P) :
    localWeighted rho m a b = localWeighted rhoSw m a b + localError rho rhoSw m a b := by
  by_cases h : a = b
  · simp [localWeighted, localError, h]
  · simp only [localWeighted, localError, h, if_false, mul_sub, Finset.sum_sub_distrib]
    ring

/-- Once the graph argument localizes each quartet discrepancy, this theorem
proves the required m(c)m(d) multiplicities and the global error identity. -/
theorem error_localization_by_ports
    (rho rhoSw : X → X → X → X → ℚ)
    (localRho localSw : B → P → P → P → P → ℚ)
    (project : B → X → P)
    (hzero : ∀ i a c d, localRho i a a c d = localSw i a a c d)
    (hlocalize : ∀ x y z w,
      rho x y z w - rhoSw x y z w =
        ∑ i, (localRho i (project i x) (project i y) (project i z) (project i w) -
          localSw i (project i x) (project i y) (project i z) (project i w)))
    (x y : X) :
    sourceError rho rhoSw x y =
      ∑ i, localError (localRho i) (localSw i) (portMass (project i)) (project i x) (project i y) := by
  by_cases hxy : x = y
  · subst y
    simp [sourceError, localError]
  · simp only [sourceError, hxy, if_false]
    simp_rw [hlocalize]
    rw [Finset.sum_comm_cycle]
    apply Finset.sum_congr rfl
    intro i _
    rw [sum_pairs_by_ports (project i) (fun c d =>
      localRho i (project i x) (project i y) c d -
        localSw i (project i x) (project i y) c d)]
    by_cases hi : project i x = project i y
    · simp [localError, hi, hzero]
    · simp [localError, hi]

/-- Algebraic assembly, with the two remaining GRAPH identities stated openly. -/
theorem source_composition_of_switching_and_localization
    (rho rhoSw : X → X → X → X → ℚ)
    (localRho localSw : B → P → P → P → P → ℚ)
    (project : B → X → P)
    (hzero : ∀ i a c d, localRho i a a c d = localSw i a a c d)
    (hlocalize : ∀ x y z w,
      rho x y z w - rhoSw x y z w =
        ∑ i, (localRho i (project i x) (project i y) (project i z) (project i w) -
          localSw i (project i x) (project i y) (project i z) (project i w)))
    (hswitch : ∀ x y, sourceDistance rhoSw x y =
      ∑ i, localWeighted (localSw i) (portMass (project i)) (project i x) (project i y))
    (x y : X) :
    sourceDistance rho x y =
      ∑ i, localWeighted (localRho i) (portMass (project i)) (project i x) (project i y) := by
  rw [source_eq_switching_add_error rho rhoSw, hswitch,
    error_localization_by_ports rho rhoSw localRho localSw project hzero hlocalize,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact (local_eq_switching_add_error _ _ _ _ _).symm

#print axioms sum_pairs_by_ports
#print axioms portMass_pos_of_surjective
#print axioms source_composition_of_switching_and_localization

end Nanuq.Composition
