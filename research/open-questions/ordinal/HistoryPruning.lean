import HistoryWellFounded

namespace HistoryPruning

open SpeciesBridge BinaryPopulation PositiveUnavoidability
open ReachableRankNecessity HistoryWellFounded

/-- Membership after n rounds of deleting nodes with no remaining child. -/
def survives {E s} : Nat → Node E s → Prop
  | 0, _ => True
  | n+1, node => ∃ child, Below child node ∧ survives n child

theorem continuation_of_survives (E : LabelledGraph) (s : Nat → Bool)
    (n : Nat) (h : History E s) (hs : survives n (some h)) :
    ∃ w, FinitePath E s h.len n h.endpoint w := by
  induction n generalizing h with
  | zero => exact ⟨h.endpoint, .nil _ _⟩
  | succ n ih =>
    obtain ⟨child, hc, hs⟩ := hs
    cases child with
    | none => exact False.elim hc
    | some child =>
      obtain ⟨v, he, rfl⟩ := hc
      obtain ⟨w, hp⟩ := ih (h.extend v he) hs
      have hp' : FinitePath E s (h.len+1) n v w := by simpa using hp
      exact ⟨w, .cons he hp'⟩

theorem survives_of_continuation (E : LabelledGraph) (s : Nat → Bool)
    (n : Nat) (h : History E s) (w : Nat)
    (hp : FinitePath E s h.len n h.endpoint w) : survives n (some h) := by
  induction n generalizing h w with
  | zero => trivial
  | succ n ih =>
    cases hp with
    | @cons _ _ _ v _ he tail =>
      let child := h.extend v he
      have hp' : FinitePath E s child.len n child.endpoint w := by simpa [child] using tail
      exact ⟨some child, ⟨v, he, rfl⟩, ih child w hp'⟩

theorem root_survives_every_finite_stage (E : LabelledGraph) (s : Nat → Bool)
    (population : BinaryNatPopulation E) (n : Nat) :
    survives n (none : Node E s) := by
  cases n with
  | zero => trivial
  | succ n =>
    obtain ⟨v, w, hp⟩ := finite_word_occurs E s population n
    let h := History.singleton E s v
    exact ⟨some h, rfl, survives_of_continuation E s n h w hp⟩

/-- The first limit stage is the intersection of all finite derivatives. -/
def atOmega {E s} (node : Node E s) : Prop := ∀ n, survives n node

/-- Its successor applies the same child-retention operation once more. -/
def atOmegaSucc {E s} (node : Node E s) : Prop :=
  ∃ child, Below child node ∧ atOmega child

theorem omega_stage_iff_root (E : LabelledGraph) (s : Nat → Bool)
    (population : BinaryNatPopulation E) (avoids : ¬ Realizes E s) (node : Node E s) :
    atOmega node ↔ node = none := by
  cases node with
  | none => exact ⟨fun _ => rfl, fun _ => root_survives_every_finite_stage E s population⟩
  | some h =>
    constructor
    · intro hs
      let height := HistoryWellFounded.height E s population avoids h
      obtain ⟨w, hp⟩ := continuation_of_survives E s (height+1) h (hs (height+1))
      have hm := rank_isMaximum E s population avoids h.reachable
      have bound := hm.2 (height+1) ⟨w, hp⟩
      have bad : False := by dsimp [height, HistoryWellFounded.height] at bound; omega
      exact False.elim bad
    · intro bad
      cases bad

theorem omega_succ_stage_empty (E : LabelledGraph) (s : Nat → Bool)
    (population : BinaryNatPopulation E) (avoids : ¬ Realizes E s) (node : Node E s) :
    ¬ atOmegaSucc node := by
  rintro ⟨child, hc, hs⟩
  have eqnone := (omega_stage_iff_root E s population avoids child).mp hs
  subst child
  cases node <;> exact hc

end HistoryPruning

#print axioms HistoryPruning.root_survives_every_finite_stage
#print axioms HistoryPruning.omega_stage_iff_root
#print axioms HistoryPruning.omega_succ_stage_empty
