import GraphSwitchingDegree
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Nanuq.Source
namespace EdgeGraph

variable {V E : Type*} [Fintype E] [DecidableEq V] (G : EdgeGraph V E)

theorem dreach_eq_of_outdegree_zero {a b : V} (hzero : G.outDegree a = 0)
    (h : G.DReach a b) : a = b := by
  rcases Relation.ReflTransGen.cases_head h with heq | ⟨c, hac, _⟩
  · exact heq
  · obtain ⟨e, hs, _⟩ := hac
    have hc : 0 < G.outDegree a := Finset.card_pos.mpr
      ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩⟩
    rw [hzero] at hc
    exact False.elim (Nat.not_lt_zero _ hc)

/-- The target component of a unique-parent DAG edge is precisely its directed
descendants. This is derived from edge-avoiding walks, not an ancestry field. -/
theorem target_side_iff_descendant (hu : G.UniqueIncoming) (ha : G.Acyclic)
    (e : E) (b : V) :
    G.ReachWithout e (G.target e) b ↔ G.DReach (G.target e) b := by
  have he := G.uniqueIncoming_all_bridges hu ha e
  constructor
  · intro h
    have hclosed : ∀ ⦃a b⦄, G.UStep (fun f => f ≠ e) a b →
        G.DReach (G.target e) a → G.DReach (G.target e) b := by
      intro a b hab hp
      obtain ⟨f, hfe, hinc⟩ := hab
      rcases hinc with ⟨hs, ht⟩ | ⟨hs, ht⟩
      · exact hp.tail ⟨f, hs, ht⟩
      · rw [← ht] at hp
        rw [← hs]
        exact G.descendant_parent_of_other_edge hu e f hfe hp
    exact G.ureach_preserves hclosed h (.refl)
  · intro h
    apply G.dreach_preserves
      (P := fun a => G.ReachWithout e (G.target e) a)
      (fun _ _ hab hp => G.bridge_target_forward_closed he hab hp) h
    exact .refl

end EdgeGraph

namespace RootedBinary.Switching

open scoped BigOperators

variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable {N : RootedBinary V E X} (S : N.Switching)

/-- Selected descendants among four distinct original taxon leaves. -/
noncomputable def quartetDesc (q : Fin 4 ↪ X) (a : V) : Finset (Fin 4) := by
  classical
  exact Finset.univ.filter (fun i => S.graph.DReach a (N.leaf (q i)))

@[simp] theorem mem_quartetDesc (q : Fin 4 ↪ X) (a : V) (i : Fin 4) :
    i ∈ S.quartetDesc q a ↔ S.graph.DReach a (N.leaf (q i)) := by
  classical
  simp [quartetDesc]

theorem quartetDesc_root_card (q : Fin 4 ↪ X) :
    (S.quartetDesc q N.root).card = 4 := by
  classical
  simp [quartetDesc, S.selected_rooted]

theorem quartetDesc_leaf_card_le_one (q : Fin 4 ↪ X) (x : X) :
    (S.quartetDesc q (N.leaf x)).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro i hi j hj
  have hei := S.graph.dreach_eq_of_outdegree_zero (S.selected_leaf_degrees x).2
    ((S.mem_quartetDesc q _ i).mp hi)
  have hej := S.graph.dreach_eq_of_outdegree_zero (S.selected_leaf_degrees x).2
    ((S.mem_quartetDesc q _ j).mp hj)
  exact q.injective (N.leaf.injective (hei.symm.trans hej))

theorem quartetDesc_covered_by_children (q : Fin 4 ↪ X) (a : V)
    (hnotleaf : ∀ x, N.leaf x ≠ a) :
    S.quartetDesc q a ⊆
      (Finset.univ.filter (fun e : S.Edge => S.graph.source e = a)).biUnion
        (fun e => S.quartetDesc q (S.graph.target e)) := by
  classical
  intro i hi
  have h := (S.mem_quartetDesc q a i).mp hi
  rcases Relation.ReflTransGen.cases_head h with heq | ⟨b, hab, hb⟩
  · exact False.elim (hnotleaf (q i) heq.symm)
  · obtain ⟨e, hs, ht⟩ := hab
    apply Finset.mem_biUnion.mpr
    refine ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩, ?_⟩
    apply (S.mem_quartetDesc q _ i).mpr
    rw [ht]
    exact hb

theorem quartetDesc_small_children_bound (q : Fin 4 ↪ X) (a : V)
    (hnotleaf : ∀ x, N.leaf x ≠ a)
    (hsmall : ∀ e : S.Edge, S.graph.source e = a →
      (S.quartetDesc q (S.graph.target e)).card ≤ 1) :
    (S.quartetDesc q a).card ≤ S.graph.outDegree a := by
  classical
  let outs := Finset.univ.filter (fun e : S.Edge => S.graph.source e = a)
  calc
    (S.quartetDesc q a).card ≤
        (outs.biUnion (fun e => S.quartetDesc q (S.graph.target e))).card :=
      Finset.card_le_card (S.quartetDesc_covered_by_children q a hnotleaf)
    _ ≤ ∑ e ∈ outs, (S.quartetDesc q (S.graph.target e)).card := Finset.card_biUnion_le
    _ ≤ ∑ _e ∈ outs, 1 := Finset.sum_le_sum
      (fun e he => hsmall e (Finset.mem_filter.mp he).2)
    _ = S.graph.outDegree a := by simp [outs, EdgeGraph.outDegree]

/-- Descend whenever some child still contains at least two selected taxa. -/
theorem exists_lowest_quartet_fork (q : Fin 4 ↪ X) (a : V)
    (hc : 2 ≤ (S.quartetDesc q a).card) :
    ∃ b, 2 ≤ (S.quartetDesc q b).card ∧
      ∀ e : S.Edge, S.graph.source e = b →
        (S.quartetDesc q (S.graph.target e)).card ≤ 1 := by
  classical
  let r : V → V → Prop := fun b a => Relation.TransGen S.graph.DStep a b
  haveI : IsTrans V r := ⟨fun _ _ _ hab hbc => hbc.trans hab⟩
  haveI : Std.Irrefl r := ⟨fun a => S.selected_acyclic a⟩
  have hw : WellFounded r := Finite.wellFounded_of_trans_of_irrefl r
  refine hw.induction (C := fun a => 2 ≤ (S.quartetDesc q a).card →
    ∃ b, 2 ≤ (S.quartetDesc q b).card ∧ ∀ e : S.Edge,
      S.graph.source e = b → (S.quartetDesc q (S.graph.target e)).card ≤ 1) a ?_ hc
  intro b ih hb
  by_cases hchild : ∃ e : S.Edge, S.graph.source e = b ∧
      2 ≤ (S.quartetDesc q (S.graph.target e)).card
  · obtain ⟨e, hs, ht⟩ := hchild
    exact ih (S.graph.target e) (Relation.TransGen.single ⟨e, hs, rfl⟩) ht
  · refine ⟨b, hb, ?_⟩
    intro e he
    have hn : ¬ 2 ≤ (S.quartetDesc q (S.graph.target e)).card :=
      fun h => hchild ⟨e, he, h⟩
    exact Nat.le_of_lt_succ (Nat.lt_of_not_ge hn)

theorem exists_vertex_with_two_quartet_descendants (q : Fin 4 ↪ X) :
    ∃ a, a ≠ N.root ∧ (S.quartetDesc q a).card = 2 := by
  have hroot : 2 ≤ (S.quartetDesc q N.root).card := by
    rw [S.quartetDesc_root_card q]
    exact Nat.le_add_right 2 2
  obtain ⟨a, ha, hsmall⟩ := S.exists_lowest_quartet_fork q N.root hroot
  have hnotleaf : ∀ x, N.leaf x ≠ a := by
    intro x hx
    have hxcard := S.quartetDesc_leaf_card_le_one q x
    rw [hx] at hxcard
    exact Nat.not_succ_le_self 1 (ha.trans hxcard)
  have hle := (S.quartetDesc_small_children_bound q a hnotleaf hsmall).trans
    ((S.selected_outdegree_le a).trans (N.outDegree_le_two a))
  have hcard : (S.quartetDesc q a).card = 2 := Nat.le_antisymm hle ha
  refine ⟨a, ?_, hcard⟩
  intro haroot
  rw [haroot, S.quartetDesc_root_card q] at hcard
  cases hcard

noncomputable def quartetSide (q : Fin 4 ↪ X) (e : S.Edge) (a : V) : Finset (Fin 4) := by
  classical
  exact Finset.univ.filter (fun i => S.graph.ReachWithout e a (N.leaf (q i)))

@[simp] theorem mem_quartetSide (q : Fin 4 ↪ X) (e : S.Edge) (a : V) (i : Fin 4) :
    i ∈ S.quartetSide q e a ↔ S.graph.ReachWithout e a (N.leaf (q i)) := by
  classical
  simp [quartetSide]

theorem quartetSide_card_sum (q : Fin 4 ↪ X) (e : S.Edge) :
    (S.quartetSide q e (S.graph.source e)).card +
      (S.quartetSide q e (S.graph.target e)).card = 4 := by
  classical
  have he := S.graph.uniqueIncoming_all_bridges S.selected_uniqueIncoming S.selected_acyclic e
  have hdisj : Disjoint (S.quartetSide q e (S.graph.source e))
      (S.quartetSide q e (S.graph.target e)) := by
    apply Finset.disjoint_left.mpr
    intro i hs ht
    exact S.graph.bridge_sides_disjoint he
      ((S.mem_quartetSide q e _ i).mp hs) ((S.mem_quartetSide q e _ i).mp ht)
  have hcover : S.quartetSide q e (S.graph.source e) ∪
      S.quartetSide q e (S.graph.target e) = Finset.univ := by
    ext i
    simp only [Finset.mem_union, mem_quartetSide, Finset.mem_univ, iff_true]
    exact S.graph.edge_side_cover e (S.selected_connected _ _)
  rw [← Finset.card_union_of_disjoint hdisj, hcover]
  exact Fintype.card_fin 4

/-- Every quartet of distinct original taxa in every actual switching is
separated 2+2 by an actual edge. No quartet-resolution function is assumed. -/
theorem quartet_two_two_edge (q : Fin 4 ↪ X) :
    ∃ e : S.Edge,
      (S.quartetSide q e (S.graph.source e)).card = 2 ∧
      (S.quartetSide q e (S.graph.target e)).card = 2 := by
  classical
  obtain ⟨a, ha, hcard⟩ := S.exists_vertex_with_two_quartet_descendants q
  obtain ⟨e, he⟩ := S.selected_parent ha
  have htarget : S.quartetSide q e (S.graph.target e) = S.quartetDesc q a := by
    ext i
    simp only [mem_quartetSide, mem_quartetDesc]
    rw [← he]
    exact S.graph.target_side_iff_descendant S.selected_uniqueIncoming S.selected_acyclic e _
  have ht : (S.quartetSide q e (S.graph.target e)).card = 2 := by
    rw [htarget, hcard]
  have hs := S.quartetSide_card_sum q e
  rw [ht] at hs
  exact ⟨e, Nat.add_right_cancel hs, ht⟩

end RootedBinary.Switching
end Nanuq.Source

#print axioms Nanuq.Source.RootedBinary.Switching.quartet_two_two_edge
