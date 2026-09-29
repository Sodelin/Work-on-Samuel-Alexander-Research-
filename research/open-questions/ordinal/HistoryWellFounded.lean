import ReachableRankNecessity

namespace HistoryWellFounded

open SpeciesBridge BinaryPopulation PositiveUnavoidability ReachableRankNecessity

/-- A finite matching history, represented canonically by a path constant after its end. -/
structure History (E : LabelledGraph) (s : Nat → Bool) where
  len : Nat
  path : Nat → Nat
  stabilized : ∀ i, len ≤ i → path i = path len
  edge_valid : ∀ i, i < len → E (path i) (path (i+1)) (s i)

namespace History

def endpoint {E s} (h : History E s) : Nat := h.path h.len

def singleton (E : LabelledGraph) (s : Nat → Bool) (v : Nat) : History E s :=
  ⟨0, fun _ => v, fun _ _ => rfl, fun _ hi => False.elim (by omega)⟩

def extend {E s} (h : History E s) (w : Nat) (he : E h.endpoint w (s h.len)) :
    History E s where
  len := h.len + 1
  path := fun i => if i ≤ h.len then h.path i else w
  stabilized := by
    intro i hi
    simp only [show ¬i ≤ h.len by omega, show ¬h.len+1 ≤ h.len by omega, if_false]
  edge_valid := by
    intro i hi
    by_cases hsmall : i < h.len
    · simpa only [if_pos (show i ≤ h.len by omega),
        if_pos (show i+1 ≤ h.len by omega)] using h.edge_valid i hsmall
    · have hi' : i = h.len := by omega
      subst i
      simpa only [if_pos (Nat.le_refl _),
        if_neg (show ¬h.len+1 ≤ h.len by omega), endpoint] using he

@[simp] theorem extend_len {E s} (h : History E s) (w he) :
    (h.extend w he).len = h.len + 1 := rfl

@[simp] theorem extend_endpoint {E s} (h : History E s) (w he) :
    (h.extend w he).endpoint = w := by
  simp only [extend, endpoint, if_neg (show ¬h.len+1 ≤ h.len by omega)]

theorem finitePath {E s} (h : History E s) :
    FinitePath E s 0 h.len (h.path 0) h.endpoint := by
  have aux : ∀ n, n ≤ h.len → FinitePath E s 0 n (h.path 0) (h.path n) := by
    intro n
    induction n with
    | zero => intro _; exact .nil _ _
    | succ n ih =>
      intro hn
      exact (ih (by omega)).snoc (by simpa using h.edge_valid n (by omega))
  exact aux h.len (Nat.le_refl _)

theorem reachable {E s} (h : History E s) : Reachable E s h.endpoint h.len :=
  ⟨h.path 0, h.finitePath⟩

end History

def Child {E s} (child parent : History E s) : Prop :=
  ∃ (w : Nat) (he : E parent.endpoint w (s parent.len)), child = parent.extend w he

abbrev Node (E : LabelledGraph) (s : Nat → Bool) := Option (History E s)

/-- The artificial root has exactly the histories of length zero as children. -/
def Below {E s} : Node E s → Node E s → Prop
  | some child, some parent => Child child parent
  | some child, none => child.len = 0
  | none, _ => False

noncomputable def height (E : LabelledGraph) (s : Nat → Bool)
    (population : BinaryNatPopulation E) (avoids : ¬ Realizes E s)
    (h : History E s) : Nat :=
  rank E s population avoids h.endpoint h.len

theorem child_height_lt (E : LabelledGraph) (s : Nat → Bool)
    (population : BinaryNatPopulation E) (avoids : ¬ Realizes E s)
    {child parent : History E s} (hc : Child child parent) :
    height E s population avoids child < height E s population avoids parent := by
  obtain ⟨w, he, rfl⟩ := hc
  simpa only [height, History.extend_endpoint, History.extend_len] using rank_isCertificate E s population avoids
    parent.endpoint parent.len parent.reachable w he

theorem child_wellFounded (E : LabelledGraph) (s : Nat → Bool)
    (population : BinaryNatPopulation E) (avoids : ¬ Realizes E s) :
    WellFounded (Child (E := E) (s := s)) := by
  have aux : ∀ n, ∀ h : History E s, height E s population avoids h = n → Acc Child h := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro h hn
      apply Acc.intro h
      intro child hc
      exact ih _ (by have := child_height_lt E s population avoids hc; omega) child rfl
  exact ⟨fun h => aux _ h rfl⟩

theorem below_wellFounded (E : LabelledGraph) (s : Nat → Bool)
    (population : BinaryNatPopulation E) (avoids : ¬ Realizes E s) :
    WellFounded (Below (E := E) (s := s)) := by
  have childAcc := child_wellFounded E s population avoids
  have someAcc : ∀ h : History E s, Acc Below (some h) := by
    intro h
    induction h using childAcc.induction with
    | h h ih =>
      apply Acc.intro (some h)
      intro node hn
      cases node with
      | none => exact False.elim hn
      | some child => exact ih child hn
  constructor
  intro node
  cases node with
  | some h => exact someAcc h
  | none =>
    apply Acc.intro none
    intro child hc
    cases child with
    | none => exact False.elim hc
    | some h => exact someAcc h

/-- Full incoming-label coverage and finite roots force every prescribed finite prefix. -/
theorem finite_word_occurs (E : LabelledGraph) (s : Nat → Bool)
    (population : BinaryNatPopulation E) (n : Nat) :
    ∃ v w, FinitePath E s 0 n v w := by
  obtain ⟨rootBound, roots⟩ := (finiteSupport_iff_bounded _).mp population.2.2.1
  obtain ⟨bound, _, hback⟩ := backward_word E s population rootBound roots n
  obtain ⟨v, _, path⟩ := hback bound (Nat.le_refl _)
  exact ⟨v, bound, path⟩

theorem population_heights_unbounded (E : LabelledGraph) (s : Nat → Bool)
    (population : BinaryNatPopulation E) (avoids : ¬ Realizes E s) (n : Nat) :
    ∃ v, n ≤ height E s population avoids (History.singleton E s v) := by
  obtain ⟨v, w, hp⟩ := finite_word_occurs E s population n
  have hm := rank_isMaximum E s population avoids (reachable_zero E s v)
  exact ⟨v, hm.2 n ⟨w, hp⟩⟩

end HistoryWellFounded

#print axioms HistoryWellFounded.below_wellFounded
#print axioms HistoryWellFounded.finite_word_occurs
#print axioms HistoryWellFounded.population_heights_unbounded
