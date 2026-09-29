import HistoryWellFounded
import Mathlib.SetTheory.Ordinal.Rank

/-!
The Mathlib ordinal rank of the actual matching-history tree.
Well-foundedness and all finite-height premises are derived from the existing
BinaryNatPopulation axioms and actual avoidance. The artificial root has
exactly the zero-edge histories as children.
-/

namespace OrdinalHistoryRank

open SpeciesBridge BinaryPopulation PositiveUnavoidability
open ReachableRankNecessity HistoryWellFounded

noncomputable def ordinalRank (E : LabelledGraph) (s : Nat → Bool)
    (population : BinaryNatPopulation E) (avoids : ¬ Realizes E s)
    (node : Node E s) : Ordinal :=
  ((below_wellFounded E s population avoids).apply node).rank

theorem ordinalRank_eq (E : LabelledGraph) (s : Nat → Bool)
    (population : BinaryNatPopulation E) (avoids : ¬ Realizes E s) (node : Node E s) :
    ordinalRank E s population avoids node =
      ⨆ child : {child // Below child node},
        Order.succ (ordinalRank E s population avoids child.1) := by
  exact Acc.rank_eq _

theorem ordinalRank_lt_of_below (E : LabelledGraph) (s : Nat → Bool)
    (population : BinaryNatPopulation E) (avoids : ¬ Realizes E s)
    {child parent : Node E s} (he : Below child parent) :
    ordinalRank E s population avoids child < ordinalRank E s population avoids parent := by
  exact Acc.rank_lt_of_rel ((below_wellFounded E s population avoids).apply parent) he

theorem history_rank_le_height (E : LabelledGraph) (s : Nat → Bool)
    (population : BinaryNatPopulation E) (avoids : ¬ Realizes E s) (h : History E s) :
    ordinalRank E s population avoids (some h) ≤ (height E s population avoids h : Ordinal) := by
  induction h using (child_wellFounded E s population avoids).induction with
  | h h ih =>
    rw [ordinalRank_eq]
    apply Ordinal.iSup_le
    intro ⟨node, hn⟩
    cases node with
    | none => exact False.elim hn
    | some child =>
      have hc : Child child h := hn
      apply (Order.succ_le_succ (ih child hc)).trans
      rw [← Ordinal.natCast_succ]
      exact Nat.cast_le.mpr (Nat.succ_le_of_lt (child_height_lt E s population avoids hc))

theorem continuation_le_history_rank (E : LabelledGraph) (s : Nat → Bool)
    (population : BinaryNatPopulation E) (avoids : ¬ Realizes E s)
    (n : Nat) (h : History E s) (w : Nat)
    (path : FinitePath E s h.len n h.endpoint w) :
    (n : Ordinal) ≤ ordinalRank E s population avoids (some h) := by
  induction n generalizing h w with
  | zero => exact bot_le
  | succ n ih =>
    cases path with
    | @cons _ _ _ v _ he tail =>
      let child := h.extend v he
      have hp : FinitePath E s child.len n child.endpoint w := by
        simpa only [child, History.extend_len, History.extend_endpoint] using tail
      have lower := ih child w hp
      have strict := ordinalRank_lt_of_below E s population avoids
        (child := some child) (parent := some h) (show Child child h from ⟨v, he, rfl⟩)
      rw [Ordinal.natCast_succ]
      exact Order.succ_le_iff.mpr (lt_of_le_of_lt lower strict)

/-- Mathlib's actual ordinal rank of every non-root history is its attained natural height. -/
theorem history_rank_eq_height (E : LabelledGraph) (s : Nat → Bool)
    (population : BinaryNatPopulation E) (avoids : ¬ Realizes E s) (h : History E s) :
    ordinalRank E s population avoids (some h) = (height E s population avoids h : Ordinal) := by
  apply le_antisymm (history_rank_le_height E s population avoids h)
  obtain ⟨w, hp⟩ := (rank_isMaximum E s population avoids h.reachable).1
  exact continuation_le_history_rank E s population avoids _ h w hp

/-- The artificial root has Mathlib ordinal rank omega, with no external cofinality premise. -/
theorem root_rank_eq_omega (E : LabelledGraph) (s : Nat → Bool)
    (population : BinaryNatPopulation E) (avoids : ¬ Realizes E s) :
    ordinalRank E s population avoids none = Ordinal.omega0 := by
  apply le_antisymm
  · rw [ordinalRank_eq]
    apply Ordinal.iSup_le
    intro ⟨node, hn⟩
    cases node with
    | none => exact False.elim hn
    | some h =>
      rw [history_rank_eq_height, ← Ordinal.natCast_succ]
      exact (Ordinal.natCast_lt_omega0 _).le
  · apply Ordinal.omega0_le.mpr
    intro n
    obtain ⟨v, w, hp⟩ := finite_word_occurs E s population n
    let h := History.singleton E s v
    have low := continuation_le_history_rank E s population avoids n h w hp
    have strict := ordinalRank_lt_of_below E s population avoids
      (child := some h) (parent := none) (show h.len = 0 from rfl)
    exact low.trans strict.le

theorem aperiodic_Ps_root_rank_eq_omega (s : Nat → Bool)
    (aperiodic : ¬ BinaryAvoidance.EventuallyPeriodic s) :
    ordinalRank (BinaryAvoidance.Edge s) s (edge_is_binaryNatPopulation s)
      (edge_avoids_aperiodic_target s aperiodic) none = Ordinal.omega0 :=
  root_rank_eq_omega (BinaryAvoidance.Edge s) s (edge_is_binaryNatPopulation s)
    (edge_avoids_aperiodic_target s aperiodic)

end OrdinalHistoryRank

#print axioms OrdinalHistoryRank.history_rank_eq_height
#print axioms OrdinalHistoryRank.root_rank_eq_omega
#print axioms OrdinalHistoryRank.aperiodic_Ps_root_rank_eq_omega
