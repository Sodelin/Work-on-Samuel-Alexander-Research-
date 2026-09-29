import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import SamuelAlexanderResearch.BirthOrder
import FounderWindow

/-!
# Founding windows measured in literal real birth time

An actual earliest organism is selected from finite real birthdate sublevels.
Birth dates need not be injective: coeval founders and multiple organisms with
the same earliest birth time are allowed. Natural vertex identifiers carry no
chronological order. This module isolates the window and founder lemmas; it
does not prove maximal-cluster existence, directed-union IAP, or biological
plausibility of the duration parameter.
-/

namespace RealFounderWindow
open SpeciesBridge FounderWindowResearch

/-- Finiteness before every real time, with exactly the strict sublevel convention. -/
def StrictFiniteSublevels (birth : Nat → ℝ) : Prop :=
  ∀ t : ℝ, FiniteSupport (fun v => birth v < t)

/-- Birth times strictly increase along parent-to-child edges. -/
def Chronological (E : Graph) (birth : Nat → ℝ) : Prop :=
  ∀ a b, E a b → birth a < birth b

/-- Every founder is born within a fixed real duration of an actual earliest member.
The witness is an organism, but the bounds concern birth times, not vertex ranks. -/
def Window (E : Graph) (birth : Nat → ℝ) (duration : ℝ) (S : NatSet) : Prop :=
  ∃ start, S start ∧ (∀ v, S v → birth start ≤ birth v) ∧
    ∀ r, Founder E S r → birth r ≤ birth start + duration

theorem closed_sublevels {birth : Nat → ℝ} (finite : StrictFiniteSublevels birth) :
    BirthOrder.FiniteSublevels birth := by
  intro t
  obtain ⟨xs, hxs⟩ := finite (t + 1)
  exact ⟨xs, fun v hv => hxs v (by linarith)⟩

/-- Every nonempty set has an actual earliest birth, even when several vertices tie. -/
theorem nonempty_has_earliest {birth : Nat → ℝ}
    (finite : StrictFiniteSublevels birth) (S : NatSet) (nonempty : ∃ v, S v) :
    ∃ start, S start ∧ ∀ v, S v → birth start ≤ birth v :=
  BirthOrder.exists_least birth (closed_sublevels finite) S nonempty

theorem descendant_birth_strict {E : Graph} {birth : Nat → ℝ}
    (chronological : Chronological E birth) {a b : Nat} (h : Descendant E a b) :
    birth a < birth b := by
  induction h with
  | edge he => exact chronological _ _ he
  | snoc _ he ih => exact lt_trans ih (chronological _ _ he)

/-- Every earliest member is an ancestry founder; coeval unrelated members remain possible. -/
theorem earliest_is_founder {E : Graph} {birth : Nat → ℝ}
    (chronological : Chronological E birth) {S : NatSet} {start : Nat}
    (hstart : S start) (earliest : ∀ v, S v → birth start ≤ birth v) :
    Founder E S start := by
  refine ⟨hstart, ?_⟩
  intro a ha path
  exact (not_lt_of_ge (earliest a ha)) (descendant_birth_strict chronological path)

/-- Founder coverage in the original real-time model, with no rank reindexing. -/
theorem founder_covers {E : Graph} {birth : Nat → ℝ}
    (finite : StrictFiniteSublevels birth) (chronological : Chronological E birth)
    (S : NatSet) (v : Nat) (hv : S v) :
    ∃ r, Founder E S r ∧ (r = v ∨ Descendant E r v) := by
  obtain ⟨r, ⟨hr, hrv⟩, hmin⟩ := nonempty_has_earliest finite
    (fun a => S a ∧ (a = v ∨ Descendant E a v)) ⟨v, hv, Or.inl rfl⟩
  refine ⟨r, ⟨hr, ?_⟩, hrv⟩
  intro a ha har
  have hav : a = v ∨ Descendant E a v := by
    rcases hrv with h | h
    · subst r
      exact Or.inr har
    · exact Or.inr (har.trans h)
  exact (not_lt_of_ge (hmin a ⟨ha, hav⟩))
    (descendant_birth_strict chronological har)

/-- The fixed real founding period puts all founders into one finite real sublevel. -/
theorem window_finite_founders {E : Graph} {birth : Nat → ℝ}
    (finite : StrictFiniteSublevels birth) {duration : ℝ} {S : NatSet}
    (h : Window E birth duration S) : FiniteSupport (Founder E S) := by
  obtain ⟨start, _, _, hb⟩ := h
  obtain ⟨xs, hxs⟩ := finite (birth start + duration + 1)
  refine ⟨xs, ?_⟩
  intro r hr
  have hbound := hb r hr
  exact hxs r (by linarith)

/-- CA is a special case of every nonnegative real founding duration. -/
theorem commonAncestor_window {E : Graph} {birth : Nat → ℝ}
    (chronological : Chronological E birth) {S : NatSet}
    (common : CommonAncestor E S) (duration : ℝ) (nonnegative : 0 ≤ duration) :
    Window E birth duration S := by
  obtain ⟨a, ha, descendants⟩ := common
  refine ⟨a, ha, ?_, ?_⟩
  · intro v hv
    by_cases heq : v = a
    · subst v
      exact le_rfl
    · exact le_of_lt (descendant_birth_strict chronological (descendants v hv heq))
  · intro r hr
    by_cases heq : r = a
    · subst r
      linarith
    · exact False.elim (hr.2 a ha (descendants r hr.1 heq))

/-- A nonempty window in a chronological graph necessarily has nonnegative duration. -/
theorem window_nonnegative {E : Graph} {birth : Nat → ℝ}
    (chronological : Chronological E birth) {duration : ℝ} {S : NatSet}
    (h : Window E birth duration S) : 0 ≤ duration := by
  obtain ⟨start, hs, hm, hb⟩ := h
  have hbound := hb start (earliest_is_founder chronological hs hm)
  linarith

/-- Real founding windows survive every nonempty directed union. Only equality of
local/global earliest birth times is used; earliest organisms need not coincide. -/
theorem window_directed_union {E : Graph} {birth : Nat → ℝ}
    (finite : StrictFiniteSublevels birth) {I : Type} [Nonempty I]
    {C : I → NatSet} {duration : ℝ} (directed : Directed C)
    (windows : ∀ i, Window E birth duration (C i)) :
    Window E birth duration (Union C) := by
  classical
  have nonempty : ∃ v, Union C v := by
    obtain ⟨i⟩ := ‹Nonempty I›
    obtain ⟨v, hv, _⟩ := windows i
    exact ⟨v, i, hv⟩
  obtain ⟨start, hstart, earliest⟩ := nonempty_has_earliest finite (Union C) nonempty
  refine ⟨start, hstart, earliest, ?_⟩
  intro r hr
  obtain ⟨i, hi⟩ := hstart
  obtain ⟨j, hj⟩ := hr.1
  obtain ⟨k, hik, hjk⟩ := directed i j
  obtain ⟨localStart, hlocal, localEarliest, localBound⟩ := windows k
  have hle : birth start ≤ birth localStart := earliest _ ⟨k, hlocal⟩
  have hge : birth localStart ≤ birth start := localEarliest _ (hik _ hi)
  have dates : birth localStart = birth start := le_antisymm hge hle
  have root : Founder E (C k) r :=
    founder_restrict (fun v hv => ⟨k, hv⟩) hr (hjk _ hj)
  have bound := localBound r root
  simpa only [dates] using bound

theorem directed_union_finite_founders {E : Graph} {birth : Nat → ℝ}
    (finite : StrictFiniteSublevels birth) {I : Type} [Nonempty I]
    {C : I → NatSet} {duration : ℝ} (directed : Directed C)
    (windows : ∀ i, Window E birth duration (C i)) :
    FiniteSupport (Founder E (Union C)) :=
  window_finite_founders finite (window_directed_union finite directed windows)

end RealFounderWindow

#print axioms RealFounderWindow.nonempty_has_earliest
#print axioms RealFounderWindow.earliest_is_founder
#print axioms RealFounderWindow.founder_covers
#print axioms RealFounderWindow.window_finite_founders
#print axioms RealFounderWindow.commonAncestor_window
#print axioms RealFounderWindow.window_nonnegative
#print axioms RealFounderWindow.window_directed_union
#print axioms RealFounderWindow.directed_union_finite_founders
