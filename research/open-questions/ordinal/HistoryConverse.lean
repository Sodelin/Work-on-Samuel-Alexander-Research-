import HistoryWellFounded

namespace HistoryConverse

open BinaryPopulation PositiveUnavoidability HistoryWellFounded

/-- A realization contradicts well-foundedness by extending its finite histories. -/
theorem wellFounded_below_excludes_realization (E : LabelledGraph) (s : Nat → Bool)
    (wf : WellFounded (Below (E := E) (s := s))) : ¬ Realizes E s := by
  have wfchild : WellFounded (Child (E := E) (s := s)) := InvImage.wf some wf
  have noTail : ∀ h : History E s, ∀ tail : Nat → Nat, tail 0 = h.endpoint →
      (∀ i, E (tail i) (tail (i+1)) (s (h.len+i))) → False := by
    intro h
    induction h using wfchild.induction with
    | h h ih =>
      intro tail hzero hedges
      have he : E h.endpoint (tail 1) (s h.len) := by simpa [hzero] using hedges 0
      let child := h.extend (tail 1) he
      apply ih child ⟨tail 1, he, rfl⟩ (fun i => tail (i+1))
      · simp [child]
      · intro i
        simpa only [child, History.extend_len, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using hedges (i+1)
  rintro ⟨path, hp⟩
  exact noTail (History.singleton E s (path 0)) path rfl (by simpa [History.singleton] using hp)

theorem below_wellFounded_iff_avoids (E : LabelledGraph) (s : Nat → Bool)
    (population : BinaryNatPopulation E) :
    WellFounded (Below (E := E) (s := s)) ↔ ¬ Realizes E s :=
  ⟨wellFounded_below_excludes_realization E s, below_wellFounded E s population⟩

end HistoryConverse

#print axioms HistoryConverse.wellFounded_below_excludes_realization
#print axioms HistoryConverse.below_wellFounded_iff_avoids
