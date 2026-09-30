import QuartetComposition

/-! Heterogeneous port sets: different blobs have different finite port types.
The two graph identities remain explicit premises, rather than hidden fields. -/
namespace Nanuq.Composition

open scoped BigOperators

variable {X B : Type*} [Fintype X] [DecidableEq X] [Fintype B]
variable (Port : B → Type*) [∀ b, Fintype (Port b)] [∀ b, DecidableEq (Port b)]

theorem error_localization_dependent_ports
    (rho rhoSw : X → X → X → X → ℚ)
    (localRho localSw : ∀ b, Port b → Port b → Port b → Port b → ℚ)
    (project : ∀ b, X → Port b)
    (hzero : ∀ b a c d, localRho b a a c d = localSw b a a c d)
    (hlocalize : ∀ x y z w,
      rho x y z w - rhoSw x y z w =
        ∑ b, (localRho b (project b x) (project b y) (project b z) (project b w) -
          localSw b (project b x) (project b y) (project b z) (project b w)))
    (x y : X) :
    sourceError rho rhoSw x y =
      ∑ b, localError (localRho b) (localSw b) (portMass (project b)) (project b x) (project b y) := by
  by_cases hxy : x = y
  · subst y
    simp [sourceError, localError]
  · simp only [sourceError, hxy, if_false]
    simp_rw [hlocalize]
    rw [Finset.sum_comm_cycle]
    apply Finset.sum_congr rfl
    intro b _
    rw [sum_pairs_by_ports (project b) (fun c d =>
      localRho b (project b x) (project b y) c d -
        localSw b (project b x) (project b y) c d)]
    by_cases hb : project b x = project b y
    · simp [localError, hb, hzero]
    · simp [localError, hb]

theorem source_composition_dependent_ports
    (rho rhoSw : X → X → X → X → ℚ)
    (localRho localSw : ∀ b, Port b → Port b → Port b → Port b → ℚ)
    (project : ∀ b, X → Port b)
    (hzero : ∀ b a c d, localRho b a a c d = localSw b a a c d)
    (hlocalize : ∀ x y z w,
      rho x y z w - rhoSw x y z w =
        ∑ b, (localRho b (project b x) (project b y) (project b z) (project b w) -
          localSw b (project b x) (project b y) (project b z) (project b w)))
    (hswitch : ∀ x y, sourceDistance rhoSw x y =
      ∑ b, localWeighted (localSw b) (portMass (project b)) (project b x) (project b y))
    (x y : X) :
    sourceDistance rho x y =
      ∑ b, localWeighted (localRho b) (portMass (project b)) (project b x) (project b y) := by
  rw [source_eq_switching_add_error rho rhoSw, hswitch,
    error_localization_dependent_ports Port rho rhoSw localRho localSw project hzero hlocalize,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  exact (local_eq_switching_add_error _ _ _ _ _).symm

#print axioms error_localization_dependent_ports
#print axioms source_composition_dependent_ports

end Nanuq.Composition
