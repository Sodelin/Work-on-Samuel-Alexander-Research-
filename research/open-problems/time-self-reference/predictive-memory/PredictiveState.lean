import ExactAbstraction
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Quot

set_option autoImplicit false

/-!
Task-relative predictive states for deterministic controlled systems.
This is the standard behavioral quotient / deterministic-machine minimization
construction, not a novelty or biological-realization claim. All actions are
total; a finite word specifies the same interventions in the compared systems.
-/
namespace PredictiveState

universe u v w r i
variable {A : Type u} {X : Type v} {O : Type w} {R : Type r}

def run (T : A → X → X) : List A → X → X
  | [], x => x
  | a :: word, x => run T word (T a x)

def FutureEq (T : A → X → X) (p : X → O) (x y : X) : Prop :=
  ∀ word : List A, p (run T word x) = p (run T word y)

theorem future_refl (T : A → X → X) (p : X → O) (x : X) :
    FutureEq T p x x := fun _ => rfl

theorem future_observe {T : A → X → X} {p : X → O} {x y : X}
    (h : FutureEq T p x y) : p x = p y := h []

theorem future_step {T : A → X → X} {p : X → O} {x y : X}
    (h : FutureEq T p x y) (a : A) : FutureEq T p (T a x) (T a y) :=
  fun word => h (a :: word)

def futureSetoid (T : A → X → X) (p : X → O) : Setoid X where
  r := FutureEq T p
  iseqv := ⟨future_refl T p, fun h word => (h word).symm,
    fun h k word => (h word).trans (k word)⟩

abbrev State (T : A → X → X) (p : X → O) := Quotient (futureSetoid T p)

def encode (T : A → X → X) (p : X → O) (x : X) : State T p :=
  Quotient.mk _ x

theorem encode_eq_iff (T : A → X → X) (p : X → O) (x y : X) :
    encode T p x = encode T p y ↔ FutureEq T p x y := by
  constructor
  · exact Quotient.exact
  · intro h
    exact Quotient.sound (s := futureSetoid T p) h

def observe (T : A → X → X) (p : X → O) : State T p → O :=
  Quotient.lift p (fun _ _ h => future_observe h)

def step (T : A → X → X) (p : X → O) (a : A) : State T p → State T p :=
  Quotient.lift (fun x => encode T p (T a x))
    (fun _ _ h => Quotient.sound (future_step h a))

theorem quotient_observe (T : A → X → X) (p : X → O) (x : X) :
    observe T p (encode T p x) = p x := rfl

theorem quotient_step (T : A → X → X) (p : X → O) (a : A) (x : X) :
    encode T p (T a x) = step T p a (encode T p x) := rfl

theorem run_commutes (T : A → X → X) (G : A → R → R) (c : X → R)
    (h : ∀ a x, c (T a x) = G a (c x)) (word : List A) (x : X) :
    c (run T word x) = run G word (c x) := by
  induction word generalizing x with
  | nil => rfl
  | cons a word ih =>
    change c (run T word (T a x)) = run G word (G a (c x))
    rw [ih, h]

theorem exact_refinement_future (T : A → X → X) (p : X → O)
    (c : X → R) (G : A → R → R) (d : R → O)
    (hobs : ∀ x, d (c x) = p x) (hstep : ∀ a x, c (T a x) = G a (c x))
    {x y : X} (hxy : c x = c y) : FutureEq T p x y := by
  intro word
  rw [← hobs, ← hobs, run_commutes T G c hstep,
    run_commutes T G c hstep, hxy]

/-- Static query sufficiency. Unused codes must be removed for uniqueness. -/
theorem factors_iff (c : X → R) (p : X → O) (onto : Function.Surjective c) :
    (∃ d : R → O, ∀ x, d (c x) = p x) ↔
      (∀ x y, c x = c y → p x = p y) := by
  constructor
  · rintro ⟨d, hd⟩ x y hxy
    rw [← hd, ← hd, hxy]
  · intro hf
    classical
    refine ⟨fun z => p (Classical.choose (onto z)), ?_⟩
    intro x
    exact hf _ _ (Classical.choose_spec (onto (c x)))

/-- Every exact output-preserving representation determines the behavioral
quotient, uniquely on attained codes. This is the coarseness theorem. -/
theorem coarsest_exact (T : A → X → X) (p : X → O)
    (c : X → R) (G : A → R → R) (d : R → O)
    (onto : Function.Surjective c)
    (hobs : ∀ x, d (c x) = p x) (hstep : ∀ a x, c (T a x) = G a (c x)) :
    ∃ H : R → State T p,
      Function.Surjective H ∧
      (∀ x, H (c x) = encode T p x) ∧
      (∀ a z, H (G a z) = step T p a (H z)) ∧
      (∀ z, observe T p (H z) = d z) ∧
      (∀ K : R → State T p, (∀ x, K (c x) = encode T p x) → K = H) := by
  obtain ⟨H, hH⟩ := (factors_iff c (encode T p) onto).mpr
    (fun _ _ hxy => Quotient.sound
      (exact_refinement_future T p c G d hobs hstep hxy))
  refine ⟨H, ?_, hH, ?_, ?_, ?_⟩
  · intro z
    refine Quotient.inductionOn z ?_
    intro x
    exact ⟨c x, hH x⟩
  · intro a z
    obtain ⟨x, rfl⟩ := onto z
    rw [← hstep, hH, hH]
    rfl
  · intro z
    obtain ⟨x, rfl⟩ := onto z
    rw [hH, quotient_observe, hobs]
  · intro K hK
    funext z
    obtain ⟨x, rfl⟩ := onto z
    exact (hK x).trans (hH x).symm

/-- A missing distinction always has a finite distinguishing intervention word.
Classical existence does not give a search algorithm for infinite systems. -/
theorem distinguishing_word (T : A → X → X) (p : X → O) (x y : X)
    (h : encode T p x ≠ encode T p y) :
    ∃ word, p (run T word x) ≠ p (run T word y) := by
  classical
  by_contra! hn
  exact h (Quotient.sound hn)

/-- A family of distinguishable states injects into every exact representation. -/
theorem distinguishable_injective {I : Type i}
    (T : A → X → X) (p : X → O) (c : X → R) (G : A → R → R) (d : R → O)
    (hobs : ∀ x, d (c x) = p x) (hstep : ∀ a x, c (T a x) = G a (c x))
    (xs : I → X) (sep : ∀ j k, j ≠ k → ¬ FutureEq T p (xs j) (xs k)) :
    Function.Injective (c ∘ xs) := by
  intro j k hjk
  by_contra hne
  exact sep j k hne (exact_refinement_future T p c G d hobs hstep hjk)

theorem distinguishable_card_le {I : Type i} [Fintype I] [Fintype R]
    (T : A → X → X) (p : X → O) (c : X → R) (G : A → R → R) (d : R → O)
    (hobs : ∀ x, d (c x) = p x) (hstep : ∀ a x, c (T a x) = G a (c x))
    (xs : I → X) (sep : ∀ j k, j ≠ k → ¬ FutureEq T p (xs j) (xs k)) :
    Fintype.card I ≤ Fintype.card R :=
  Fintype.card_le_of_injective _
    (distinguishable_injective T p c G d hobs hstep xs sep)

/-- Restricting interventions can only identify more states. -/
theorem restrict_actions {B : Type i} (T : A → X → X) (p : X → O)
    (includeAction : B → A) {x y : X} (h : FutureEq T p x y) :
    FutureEq (fun b => T (includeAction b)) p x y := by
  have hr : ∀ (word : List B) (z : X),
      run (fun b => T (includeAction b)) word z = run T (word.map includeAction) z := by
    intro word z
    induction word generalizing z with
    | nil => rfl
    | cons b word ih => exact ih _
  intro word
  rw [hr, hr]
  exact h _

/-- Finite-depth equivalence, computed by backward partition refinement. -/
def DepthEq (T : A → X → X) (p : X → O) : Nat → X → X → Prop
  | 0, x, y => p x = p y
  | n + 1, x, y => p x = p y ∧ ∀ a, DepthEq T p n (T a x) (T a y)

theorem depth_iff_words (T : A → X → X) (p : X → O) (n : Nat) (x y : X) :
    DepthEq T p n x y ↔
      ∀ word : List A, word.length ≤ n → p (run T word x) = p (run T word y) := by
  induction n generalizing x y with
  | zero =>
    constructor
    · intro h word hlen
      have hw : word = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hlen)
      subst word
      exact h
    · intro h
      exact h [] (Nat.zero_le 0)
  | succ n ih =>
    constructor
    · intro h word hlen
      cases word with
      | nil => exact h.1
      | cons a word => exact (ih _ _).mp (h.2 a) word (Nat.succ_le_succ_iff.mp hlen)
    · intro h
      refine ⟨h [] (Nat.zero_le _), ?_⟩
      intro a
      apply (ih _ _).mpr
      intro word hlen
      exact h (a :: word) (Nat.succ_le_succ hlen)

theorem future_depth (T : A → X → X) (p : X → O) {x y : X}
    (h : FutureEq T p x y) (n : Nat) : DepthEq T p n x y := by
  induction n generalizing x y with
  | zero => exact future_observe h
  | succ n ih => exact ⟨future_observe h, fun a => ih (future_step h a)⟩

/-- A global fixed-point certificate, unlike testing a few trajectories,
upgrades finite-depth indistinguishability to all finite horizons. -/
theorem stabilization_complete (T : A → X → X) (p : X → O) (n : Nat)
    (stable : ∀ x y, DepthEq T p n x y → DepthEq T p (n + 1) x y) :
    ∀ x y, DepthEq T p n x y ↔ FutureEq T p x y := by
  intro x y
  constructor
  · intro h word
    induction word generalizing x y with
    | nil => exact (stable x y h).1
    | cons a word ih => exact ih _ _ ((stable x y h).2 a)
  · intro h
    exact future_depth T p h n

/-- Observable feedback is safe when the same policy reads only the retained
observation. Hidden-state policies are deliberately not covered. -/
theorem feedback_commutes (T : A → X → X) (G : A → R → R) (c : X → R)
    (h : ∀ a x, c (T a x) = G a (c x)) (policy : R → A) (x : X) :
    c (T (policy (c x)) x) = G (policy (c x)) (c x) := h _ _

/-- An actual state-dependent controller transfers for all times when its
chosen action factors through the retained state. This is an extra hypothesis. -/
theorem feedback_trajectories (T : A → X → X) (G : A → R → R) (c : X → R)
    (commutes : ∀ a x, c (T a x) = G a (c x))
    (choose : X → A) (policy : R → A) (control : ∀ x, choose x = policy (c x))
    (x : X) (t : Nat) :
    c (ExactAbstraction.trajectory (fun (_ : Unit) y => T (choose y) y)
      (fun _ => ()) x t) =
    ExactAbstraction.trajectory (fun (_ : Unit) z => G (policy z) z)
      (fun _ => ()) (c x) t := by
  apply ExactAbstraction.trajectory_preservation
  intro _ y
  rw [control]
  exact commutes _ _

end PredictiveState
