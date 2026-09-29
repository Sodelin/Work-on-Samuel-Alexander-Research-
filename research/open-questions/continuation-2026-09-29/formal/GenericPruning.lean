import GenericCertificate

/-!
# The surviving core of a finitely branching matching relation

This extends the archived generic reachable-state certificates. No global
avoidance premise is used. After all finite leaf-pruning rounds, exactly the
states beginning infinite chains remain. This set is the greatest fixed point
of the successor operator. Applied to the exact reachable vertex/phase states,
it characterizes realization at arbitrary vertex and label types.

Only finite branching for each fixed label is required. The infinite-chain
notion is an infinite labelled walk for general relations; chronology makes
these walks injective paths in an Alexander population.
-/

namespace GenericPruning

open GenericCertificate
universe u v
variable {α : Type u}

/-- The child is the first relation argument. -/
def survives (R : α → α → Prop) : Nat → α → Prop
  | 0, _ => True
  | n+1, x => ∃ y, R y x ∧ survives R n y

def core (R : α → α → Prop) (x : α) : Prop := ∀ n, survives R n x

def Live (R : α → α → Prop) (x : α) : Prop :=
  ∃ f : Nat → α, f 0 = x ∧ ∀ n, R (f (n+1)) (f n)

theorem survives_mono (R : α → α → Prop) {n m : Nat} (hnm : n ≤ m)
    {x : α} (hx : survives R m x) : survives R n x := by
  induction m generalizing n x with
  | zero =>
    have : n = 0 := by omega
    subst n
    trivial
  | succ m ih =>
    cases n with
    | zero => trivial
    | succ n =>
      obtain ⟨y, hy, hs⟩ := hx
      exact ⟨y, hy, ih (by omega) hs⟩

/-- Explicit retention of the current set is redundant: these stages decrease. -/
theorem survives_successor_iff (R : α → α → Prop) (n : Nat) (x : α) :
    survives R (n+1) x ↔ survives R n x ∧ ∃ y, R y x ∧ survives R n y := by
  constructor
  · intro h
    exact ⟨survives_mono R (by omega) h, h⟩
  · exact fun h => h.2

theorem core_iff_child (R : α → α → Prop)
    (fin : ∀ x, Finite {y // R y x}) (x : α) :
    core R x ↔ ∃ y, R y x ∧ core R y := by
  classical
  constructor
  · intro hx
    by_contra hn
    let := fin x
    let := Fintype.ofFinite {y // R y x}
    have bad : ∀ y : {y // R y x}, ∃ n, ¬ survives R n y.1 := by
      intro y
      by_contra h
      apply hn
      refine ⟨y.1, y.2, ?_⟩
      intro n
      by_contra hs
      exact h ⟨n, hs⟩
    choose bound hbound using bad
    let M := Finset.univ.sup bound
    obtain ⟨y, hy, hs⟩ := hx (M+1)
    apply hbound ⟨y, hy⟩
    have hle : bound ⟨y,hy⟩ ≤ M :=
      Finset.le_sup (f := bound) (Finset.mem_univ (⟨y,hy⟩ : {y // R y x}))
    exact survives_mono R hle hs
  · rintro ⟨y, hy, hc⟩ n
    cases n with
    | zero => trivial
    | succ n => exact ⟨y, hy, hc n⟩

theorem live_implies_core (R : α → α → Prop) {x : α}
    (hx : Live R x) : core R x := by
  obtain ⟨f, hf0, hf⟩ := hx
  have hs : ∀ n k, survives R n (f k) := by
    intro n
    induction n with
    | zero => intro k; trivial
    | succ n ih =>
      intro k
      exact ⟨f (k+1), hf k, ih (k+1)⟩
  intro n
  rw [← hf0]
  exact hs n 0

theorem core_iff_live (R : α → α → Prop)
    (fin : ∀ x, Finite {y // R y x}) (x : α) : core R x ↔ Live R x := by
  classical
  constructor
  · intro hx
    have hnext : ∀ q : {x // core R x}, ∃ r : {x // core R x}, R r.1 q.1 := by
      intro q
      obtain ⟨y, hy, hc⟩ := (core_iff_child R fin q.1).mp q.2
      exact ⟨⟨y,hc⟩, hy⟩
    let next : {x // core R x} → {x // core R x} := fun q => Classical.choose (hnext q)
    let f : Nat → {x // core R x} := Nat.rec ⟨x,hx⟩ (fun _ q => next q)
    refine ⟨fun n => (f n).1, rfl, ?_⟩
    intro n
    exact Classical.choose_spec (hnext (f n))
  · exact live_implies_core R

def derivative (R : α → α → Prop) (S : Set α) : Set α :=
  {x | ∃ y, R y x ∧ y ∈ S}

theorem core_fixed_point (R : α → α → Prop)
    (fin : ∀ x, Finite {y // R y x}) :
    derivative R {x | core R x} = {x | core R x} := by
  ext x
  exact (core_iff_child R fin x).symm

/-- Every postfixed set is contained in the core, even without finite branching. -/
theorem postfixed_subset_core (R : α → α → Prop) (S : Set α)
    (hS : S ⊆ derivative R S) : S ⊆ {x | core R x} := by
  have hs : ∀ n x, x ∈ S → survives R n x := by
    intro n
    induction n with
    | zero => intro x hx; trivial
    | succ n ih =>
      intro x hx
      obtain ⟨y, hy, hyS⟩ := hS hx
      exact ⟨y, hy, ih y hyS⟩
  intro x hx n
  exact hs n x hx

theorem core_is_greatest_fixed_point (R : α → α → Prop)
    (fin : ∀ x, Finite {y // R y x}) :
    derivative R {x | core R x} = {x | core R x} ∧
      ∀ S, derivative R S = S → S ⊆ {x | core R x} := by
  refine ⟨core_fixed_point R fin, ?_⟩
  intro S hS
  apply postfixed_subset_core R S
  rw [hS]

variable {V : Type u} {Label : Type v}

def startState (E : Graph V Label) (s : Nat → Label) (vertex : V) : State E s :=
  ⟨(vertex,0), ⟨fun _ => vertex, rfl, by intro n hn; omega⟩⟩

/-- The surviving initial states identify the actual starting vertices. -/
theorem start_core_iff_realizes_from (E : Graph V Label) (s : Nat → Label)
    (fin : FiniteLabelChildren E) (vertex : V) :
    core (Step E s) (startState E s vertex) ↔
      ∃ p : Nat → V, p 0 = vertex ∧ ∀ n, E (p n) (p (n+1)) (s n) := by
  constructor
  · intro hx
    obtain ⟨f,hf0,hf⟩ :=
      (core_iff_live _ (finite_state_children E s fin) _).mp hx
    have phase : ∀ n, (f n).1.2 = n := by
      intro n
      induction n with
      | zero =>
        exact congrArg (fun q : State E s => q.1.2) hf0
      | succ n ih =>
        have h := (hf n).1
        omega
    refine ⟨fun n => (f n).1.1, ?_, ?_⟩
    · exact congrArg (fun q : State E s => q.1.1) hf0
    · intro n
      have h := (hf n).2
      simpa only [phase n] using h
  · rintro ⟨p,hp0,hp⟩
    let f : Nat → State E s := fun n => ⟨(p n,n), p, rfl, fun j _ => hp j⟩
    apply live_implies_core
    refine ⟨f, ?_, fun n => ⟨rfl,hp n⟩⟩
    apply Subtype.ext
    exact Prod.ext hp0 rfl

theorem realizes_iff_surviving_start (E : Graph V Label) (s : Nat → Label)
    (fin : FiniteLabelChildren E) :
    Realizes E s ↔ ∃ vertex, core (Step E s) (startState E s vertex) := by
  constructor
  · rintro ⟨p,hp⟩
    exact ⟨p 0, (start_core_iff_realizes_from E s fin (p 0)).mpr ⟨p,rfl,hp⟩⟩
  · rintro ⟨vertex,hx⟩
    obtain ⟨p,_,hp⟩ := (start_core_iff_realizes_from E s fin vertex).mp hx
    exact ⟨p,hp⟩

theorem state_core_iff_infinite_continuation (E : Graph V Label) (s : Nat → Label)
    (fin : FiniteLabelChildren E) (x : State E s) :
    core (Step E s) x ↔ Live (Step E s) x :=
  core_iff_live (Step E s) (finite_state_children E s fin) x

theorem realizes_iff_nonempty_core (E : Graph V Label) (s : Nat → Label)
    (fin : FiniteLabelChildren E) :
    Realizes E s ↔ ∃ x : State E s, core (Step E s) x := by
  constructor
  · intro h
    obtain ⟨f, hf⟩ := (realizes_iff_state_chain E s).mp h
    exact ⟨f 0, live_implies_core _ ⟨f, rfl, hf⟩⟩
  · rintro ⟨x, hx⟩
    obtain ⟨f, _, hf⟩ := (core_iff_live _ (finite_state_children E s fin) x).mp hx
    exact (realizes_iff_state_chain E s).mpr ⟨f, hf⟩

theorem avoids_iff_every_state_pruned (E : Graph V Label) (s : Nat → Label)
    (fin : FiniteLabelChildren E) :
    (¬ Realizes E s) ↔ ∀ x : State E s, ∃ n, ¬ survives (Step E s) n x := by
  classical
  rw [realizes_iff_nonempty_core E s fin]
  simp only [core, not_exists, not_forall]

theorem matching_core_is_greatest_fixed_point (E : Graph V Label)
    (s : Nat → Label) (fin : FiniteLabelChildren E) :
    derivative (Step E s) {x | core (Step E s) x} = {x | core (Step E s) x} ∧
      ∀ S, derivative (Step E s) S = S → S ⊆ {x | core (Step E s) x} :=
  core_is_greatest_fixed_point _ (finite_state_children E s fin)

#print axioms GenericPruning.survives_successor_iff
#print axioms GenericPruning.core_iff_child
#print axioms GenericPruning.core_iff_live
#print axioms GenericPruning.core_is_greatest_fixed_point
#print axioms GenericPruning.start_core_iff_realizes_from
#print axioms GenericPruning.realizes_iff_surviving_start
#print axioms GenericPruning.state_core_iff_infinite_continuation
#print axioms GenericPruning.realizes_iff_nonempty_core
#print axioms GenericPruning.avoids_iff_every_state_pruned
#print axioms GenericPruning.matching_core_is_greatest_fixed_point

end GenericPruning
