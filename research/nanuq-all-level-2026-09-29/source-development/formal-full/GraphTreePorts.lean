import GraphQuartetExistence

namespace Nanuq.Source.EdgeGraph

variable {V E : Type*} [Fintype E] [DecidableEq V] (G : EdgeGraph V E)

theorem comparable_ancestors (hu : G.UniqueIncoming) {a b c : V}
    (hac : G.DReach a c) (hbc : G.DReach b c) : G.DReach a b ∨ G.DReach b a := by
  revert hac
  induction hbc with
  | refl => intro hac; exact Or.inl hac
  | @tail c d hbc hcd ih =>
      intro hac
      rcases Relation.ReflTransGen.cases_tail hac with heq | ⟨u, hau, hud⟩
      · apply Or.inr
        rw [← heq]
        exact hbc.tail hcd
      · obtain ⟨e, hes, het⟩ := hcd
        obtain ⟨f, hfs, hft⟩ := hud
        have hfe := hu f e (hft.trans het.symm)
        subst f
        have huc : u = c := hfs.symm.trans hes
        rw [huc] at hau
        exact ih hau

theorem sibling_descendants_disjoint (hu : G.UniqueIncoming) (ha : G.Acyclic)
    {e f : E} (hne : e ≠ f) (hs : G.source e = G.source f) {a : V}
    (he : G.DReach (G.target e) a) (hf : G.DReach (G.target f) a) : False := by
  rcases G.comparable_ancestors hu he hf with h | h
  · have hret := G.descendant_parent_of_other_edge hu e f hne.symm h
    rw [← hs] at hret
    exact ha (G.source e) (Relation.TransGen.head' ⟨e, rfl, rfl⟩ hret)
  · have hret := G.descendant_parent_of_other_edge hu f e hne h
    rw [hs] at hret
    exact ha (G.source f) (Relation.TransGen.head' ⟨f, rfl, rfl⟩ hret)

/-- An actual incident edge pointing from the vertex into the component
containing the destination. This is the raw meaning of a port direction. -/
def IsPortTo (v a : V) (e : E) : Prop :=
  (G.source e = v ∧ G.ReachWithout e (G.target e) a) ∨
  (G.target e = v ∧ G.ReachWithout e (G.source e) a)

theorem port_unique (hu : G.UniqueIncoming) (ha : G.Acyclic) {v a : V} {e f : E}
    (he : G.IsPortTo v a e) (hf : G.IsPortTo v a f) : e = f := by
  classical
  by_cases hef : e = f
  · exact hef
  · rcases he with ⟨hes, he⟩ | ⟨het, he⟩ <;>
      rcases hf with ⟨hfs, hf⟩ | ⟨hft, hf⟩
    · exact False.elim (G.sibling_descendants_disjoint hu ha hef (hes.trans hfs.symm)
        ((G.target_side_iff_descendant hu ha e a).mp he)
        ((G.target_side_iff_descendant hu ha f a).mp hf))
    · have hva : G.DReach v a :=
        (Relation.ReflTransGen.single ⟨e, hes, rfl⟩).trans
          ((G.target_side_iff_descendant hu ha e a).mp he)
      have hfa : G.ReachWithout f (G.target f) a :=
        (G.target_side_iff_descendant hu ha f a).mpr (by rw [hft]; exact hva)
      exact False.elim (G.bridge_sides_disjoint (G.uniqueIncoming_all_bridges hu ha f) hf hfa)
    · have hva : G.DReach v a :=
        (Relation.ReflTransGen.single ⟨f, hfs, rfl⟩).trans
          ((G.target_side_iff_descendant hu ha f a).mp hf)
      have hea : G.ReachWithout e (G.target e) a :=
        (G.target_side_iff_descendant hu ha e a).mpr (by rw [het]; exact hva)
      exact False.elim (G.bridge_sides_disjoint (G.uniqueIncoming_all_bridges hu ha e) he hea)
    · exact hu e f (het.trans hft.symm)

theorem rooted_connected (root : V) (hr : ∀ a, G.DReach root a) (a b : V) :
    G.UReach (fun _ => True) a b :=
  (G.ureach_symm (G.dreach_ureach (hr a))).trans (G.dreach_ureach (hr b))

theorem port_exists (hu : G.UniqueIncoming) (ha : G.Acyclic)
    (root : V) (hr : ∀ a, G.DReach root a) (v a : V) (hne : a ≠ v) :
    ∃ e, G.IsPortTo v a e := by
  classical
  by_cases hdesc : G.DReach v a
  · rcases Relation.ReflTransGen.cases_head hdesc with heq | ⟨b, hvb, hba⟩
    · exact False.elim (hne heq.symm)
    · obtain ⟨e, hs, ht⟩ := hvb
      refine ⟨e, Or.inl ⟨hs, ?_⟩⟩
      apply (G.target_side_iff_descendant hu ha e a).mpr
      rw [ht]
      exact hba
  · have hnotroot : v ≠ root := by
      intro hv
      exact hdesc (by rw [hv]; exact hr a)
    rcases Relation.ReflTransGen.cases_tail (hr v) with hv | ⟨b, _, hbv⟩
    · exact False.elim (hnotroot hv)
    · obtain ⟨e, _, ht⟩ := hbv
      refine ⟨e, Or.inr ⟨ht, ?_⟩⟩
      rcases G.edge_side_cover e (G.rooted_connected root hr (G.source e) a) with hs | htgt
      · exact hs
      · apply False.elim
        apply hdesc
        have hh := (G.target_side_iff_descendant hu ha e a).mp htgt
        rw [ht] at hh
        exact hh

theorem port_exists_unique (hu : G.UniqueIncoming) (ha : G.Acyclic)
    (root : V) (hr : ∀ a, G.DReach root a) (v a : V) (hne : a ≠ v) :
    ∃! e, G.IsPortTo v a e := by
  obtain ⟨e, he⟩ := G.port_exists hu ha root hr v a hne
  exact ⟨e, he, fun f hf => G.port_unique hu ha hf he⟩

noncomputable def portTo (hu : G.UniqueIncoming) (ha : G.Acyclic)
    (root : V) (hr : ∀ a, G.DReach root a) (v a : V) (hne : a ≠ v) : E :=
  Classical.choose (G.port_exists_unique hu ha root hr v a hne)

theorem portTo_spec (hu : G.UniqueIncoming) (ha : G.Acyclic)
    (root : V) (hr : ∀ a, G.DReach root a) (v a : V) (hne : a ≠ v) :
    G.IsPortTo v a (G.portTo hu ha root hr v a hne) :=
  (Classical.choose_spec (G.port_exists_unique hu ha root hr v a hne)).1

end Nanuq.Source.EdgeGraph

#print axioms Nanuq.Source.EdgeGraph.port_exists_unique
