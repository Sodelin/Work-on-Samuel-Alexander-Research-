import GraphSwitching

namespace Nanuq.Source.RootedBinary

variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X)

theorem hybrid_has_incoming {a : V} (hh : N.graph.IsHybrid a) :
    ∃ e, N.graph.target e = a := by
  have hc : 0 < (Finset.univ.filter (fun e => N.graph.target e = a)).card := by
    change 0 < N.graph.inDegree a
    rw [hh.1]
    exact Nat.zero_lt_succ 1
  obtain ⟨e, he⟩ := Finset.card_pos.mp hc
  exact ⟨e, (Finset.mem_filter.mp he).2⟩

/-- Existence is derived by choosing an actual incoming edge at every hybrid.
Thus the switching-tree theorem is not vacuous. -/
noncomputable def defaultSwitching : N.Switching := by
  classical
  let H := {a : V // N.graph.IsHybrid a}
  have hex : ∀ h : H, ∃ e, N.graph.target e = h.val :=
    fun h => N.hybrid_has_incoming h.property
  let select : H → E := fun h => Classical.choose (hex h)
  have select_target (h : H) : N.graph.target (select h) = h.val :=
    Classical.choose_spec (hex h)
  refine {
    keep := fun e => ¬ N.graph.IsHybrid (N.graph.target e) ∨ ∃ h : H, select h = e
    ordinary := fun _ hh => Or.inl hh
    hybrid_unique := ?_
  }
  intro a ha
  let h : H := ⟨a, ha⟩
  refine ⟨select h, select_target h, Or.inr ⟨h, rfl⟩, ?_⟩
  intro f hf hkeep
  rcases hkeep with hno | ⟨j, hj⟩
  · exact False.elim (hno (by rw [hf]; exact ha))
  · have hja : j.val = a := by
      rw [← select_target j, hj, hf]
    have hjh : j = h := Subtype.ext hja
    rw [hjh] at hj
    exact hj.symm

theorem switching_exists : Nonempty N.Switching := ⟨N.defaultSwitching⟩

theorem switching_tree_exists : ∃ S : N.Switching, S.graph.IsTree :=
  ⟨N.defaultSwitching, N.defaultSwitching.selected_is_tree⟩

end Nanuq.Source.RootedBinary

#print axioms Nanuq.Source.RootedBinary.switching_tree_exists
