import SamuelAlexanderResearch.SpeciesBridge

/-!
Isolated supporting lemmas for replacing a common ancestor with a bounded
founding period. This file proves founder coverage and directed-union closure
of the window constraint in the natural-date model. It does NOT formalize
the full real-birthdate existence theorem or its Koenig/Zorn arguments.
-/

namespace FounderWindowResearch

open SpeciesBridge

def Founder (E : Graph) (S : NatSet) (r : Nat) : Prop :=
  S r ∧ ∀ a, S a → ¬ Descendant E a r

def Window (E : Graph) (width : Nat) (S : NatSet) : Prop :=
  ∃ start, S start ∧ (∀ v, S v → start ≤ v) ∧
    ∀ r, Founder E S r → r ≤ start + width

def Union {I : Type} (C : I → NatSet) : NatSet := fun v => ∃ i, C i v

def Directed {I : Type} (C : I → NatSet) : Prop :=
  ∀ i j, ∃ k, (∀ v, C i v → C k v) ∧ (∀ v, C j v → C k v)

theorem descendant_strict {E : Graph} (horder : ∀ u v, E u v → u < v)
    {u v : Nat} (h : Descendant E u v) : u < v := by
  induction h with
  | edge he => exact horder _ _ he
  | snoc _ he ih => exact Nat.lt_trans ih (horder _ _ he)

/-- Every member has an ancestry-minimal member of the same set above it. -/
theorem founder_covers {E : Graph} (horder : ∀ u v, E u v → u < v)
    (S : NatSet) (v : Nat) (hv : S v) :
    ∃ r, Founder E S r ∧ (r = v ∨ Descendant E r v) := by
  classical
  induction v using Nat.strongRecOn with
  | ind v ih =>
    by_cases hex : ∃ a, S a ∧ Descendant E a v
    · obtain ⟨a, ha, hav⟩ := hex
      obtain ⟨r, hr, hra⟩ := ih a (descendant_strict horder hav) ha
      refine ⟨r, hr, Or.inr ?_⟩
      rcases hra with h | h
      · simpa [h] using hav
      · exact h.trans hav
    · exact ⟨v, ⟨hv, fun a ha hav => hex ⟨a, ha, hav⟩⟩, Or.inl rfl⟩

/-- A founder of a larger set is a founder in every smaller set containing it. -/
theorem founder_restrict {E : Graph} {S T : NatSet}
    (hST : ∀ v, S v → T v) {r : Nat} (hr : Founder E T r) (hSr : S r) :
    Founder E S r :=
  ⟨hSr, fun a ha => hr.2 a (hST a ha)⟩

theorem window_finite_founders {E : Graph} {width : Nat} {S : NatSet}
    (h : Window E width S) : FiniteSupport (Founder E S) := by
  obtain ⟨start, _, _, hb⟩ := h
  apply (finiteSupport_iff_bounded _).mpr
  exact ⟨start + width + 1, fun r hr => Nat.lt_succ_of_le (hb r hr)⟩

/-- CA is a special case of every nonnegative founding window. -/
theorem commonAncestor_window {E : Graph}
    (horder : ∀ u v, E u v → u < v) {S : NatSet}
    (hCA : CommonAncestor E S) (width : Nat) : Window E width S := by
  obtain ⟨a, ha, hdesc⟩ := hCA
  refine ⟨a, ha, ?_, ?_⟩
  · intro v hv
    by_cases heq : v = a
    · omega
    · exact Nat.le_of_lt (descendant_strict horder (hdesc v hv heq))
  · intro r hr
    by_cases heq : r = a
    · omega
    · exact False.elim (hr.2 a ha (hdesc r hr.1 heq))

theorem nonempty_has_minimum (S : NatSet) (v : Nat) (hv : S v) :
    ∃ start, S start ∧ ∀ w, S w → start ≤ w := by
  classical
  induction v using Nat.strongRecOn with
  | ind v ih =>
    by_cases hex : ∃ a, a < v ∧ S a
    · obtain ⟨a, hav, ha⟩ := hex
      exact ih a hav ha
    · refine ⟨v, hv, ?_⟩
      intro w hw
      apply Classical.byContradiction
      intro hle
      exact hex ⟨w, by omega, hw⟩
/-- Fixed founding windows survive every nonempty directed union. -/
theorem window_directed_union {E : Graph} {I : Type} [Nonempty I]
    {C : I → NatSet} {width : Nat} (hdir : Directed C)
    (hwindow : ∀ i, Window E width (C i)) : Window E width (Union C) := by
  classical
  have hex : ∃ v, Union C v := by
    obtain ⟨i⟩ := ‹Nonempty I›
    obtain ⟨v, hv, _⟩ := hwindow i
    exact ⟨v, i, hv⟩
  obtain ⟨v, hv⟩ := hex
  obtain ⟨start, hstart, hmin⟩ := nonempty_has_minimum (Union C) v hv
  refine ⟨start, hstart, hmin, ?_⟩
  intro r hr
  obtain ⟨i, hi⟩ := hstart
  obtain ⟨j, hj⟩ := hr.1
  obtain ⟨k, hik, hjk⟩ := hdir i j
  obtain ⟨localStart, hlocal, hlocalmin, hlocalbound⟩ := hwindow k
  have hle : start ≤ localStart := hmin _ ⟨k, hlocal⟩
  have hge : localStart ≤ start := hlocalmin _ (hik _ hi)
  have heq : localStart = start := Nat.le_antisymm hge hle
  have hroot : Founder E (C k) r :=
    founder_restrict (fun v hv => ⟨k, hv⟩) hr (hjk _ hj)
  have hbound := hlocalbound r hroot
  simpa [heq] using hbound

/-- The window constraint therefore supplies a finite founder set at the limit. -/
theorem directed_union_finite_founders {E : Graph} {I : Type} [Nonempty I]
    {C : I → NatSet} {width : Nat} (hdir : Directed C)
    (hwindow : ∀ i, Window E width (C i)) :
    FiniteSupport (Founder E (Union C)) :=
  window_finite_founders (window_directed_union hdir hwindow)

end FounderWindowResearch

#print axioms FounderWindowResearch.founder_covers
#print axioms FounderWindowResearch.commonAncestor_window
#print axioms FounderWindowResearch.window_directed_union
#print axioms FounderWindowResearch.directed_union_finite_founders


