import GraphBlobs

namespace Nanuq.Source
namespace EdgeGraph

variable {V E : Type*} (G : EdgeGraph V E)

theorem ureach_preserves {P : V → Prop} {keep : E → Prop}
    (hstep : ∀ ⦃a b⦄, G.UStep keep a b → P a → P b)
    {a b : V} (h : G.UReach keep a b) (ha : P a) : P b := by
  induction h with
  | refl => exact ha
  | tail _ hab ih => exact hstep hab ih

/-- Edge identities, not merely parent vertices, are unique. -/
def UniqueIncoming : Prop := ∀ e f, G.target e = G.target f → e = f

theorem descendant_parent_of_other_edge (hu : G.UniqueIncoming) (e f : E)
    (hne : f ≠ e) (h : G.DReach (G.target e) (G.target f)) :
    G.DReach (G.target e) (G.source f) := by
  rcases Relation.ReflTransGen.cases_tail h with heq | ⟨a, ha, g, hs, ht⟩
  · exact False.elim (hne (hu f e heq))
  · have hgf := hu g f ht
    subst g
    rw [← hs] at ha
    exact ha

/-- An acyclic graph with at most one incoming edge at each vertex has no
undirected cycle: every individual edge is a bridge. -/
theorem uniqueIncoming_all_bridges (hu : G.UniqueIncoming) (ha : G.Acyclic)
    (e : E) : G.IsBridge e := by
  intro hdetour
  have hclosed : ∀ ⦃a b⦄, G.UStep (fun f => f ≠ e) a b →
      G.DReach (G.target e) a → G.DReach (G.target e) b := by
    intro a b hab hp
    obtain ⟨f, hfe, hinc⟩ := hab
    rcases hinc with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · exact hp.tail ⟨f, hs, ht⟩
    · rw [← ht] at hp
      rw [← hs]
      exact G.descendant_parent_of_other_edge hu e f hfe hp
  have hreturn := G.ureach_preserves hclosed (G.ureach_symm hdetour)
    (Relation.ReflTransGen.refl (a := G.target e))
  exact ha (G.source e) (Relation.TransGen.head' ⟨e, rfl, rfl⟩ hreturn)

end EdgeGraph

namespace RootedBinary

variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X)

theorem indegree_one_of_nonroot_nonhybrid {a : V} (ha : a ≠ N.root)
    (hh : ¬ N.graph.IsHybrid a) : N.graph.inDegree a = 1 := by
  classical
  by_cases hl : ∃ x, N.leaf x = a
  · obtain ⟨x, rfl⟩ := hl
    exact (N.leaf_degrees x).1
  · have hnotleaf : ∀ x, N.leaf x ≠ a := by
      intro x hx
      exact hl ⟨x, hx⟩
    rcases N.internal_degrees a ha hnotleaf with ht | hhybrid
    · exact ht.1
    · exact False.elim (hh hhybrid)

theorem incoming_unique_of_indegree_one {a : V} (h : N.graph.inDegree a = 1) :
    ∃ e, N.graph.target e = a ∧ ∀ f, N.graph.target f = a → f = e := by
  classical
  obtain ⟨e, he, hu⟩ := Finset.card_eq_one_iff_existsUnique.mp h
  refine ⟨e, (Finset.mem_filter.mp he).2, ?_⟩
  intro f hf
  exact hu f (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf⟩)

/-- A switching retains all ordinary edges and precisely one incoming edge
at each hybrid. No tree, connectivity, or quartet property is an input. -/
structure Switching where
  keep : E → Prop
  ordinary : ∀ e, ¬ N.graph.IsHybrid (N.graph.target e) → keep e
  hybrid_unique : ∀ a, N.graph.IsHybrid a →
    ∃ e, N.graph.target e = a ∧ keep e ∧
      ∀ f, N.graph.target f = a → keep f → f = e

namespace Switching
variable {N} (S : N.Switching)

def Edge := {e : E // S.keep e}

noncomputable instance edgeFintype : Fintype S.Edge := by
  classical
  unfold Edge
  infer_instance

/-- The selected graph keeps exactly the original vertex and taxon sets. -/
def graph : EdgeGraph V S.Edge where
  source e := N.graph.source e.val
  target e := N.graph.target e.val

theorem dstep_original {a b : V} (h : S.graph.DStep a b) : N.graph.DStep a b := by
  obtain ⟨e, hs, ht⟩ := h
  exact ⟨e.val, hs, ht⟩

theorem selected_acyclic : S.graph.Acyclic := by
  intro a h
  exact N.acyclic a (Relation.TransGen.mono
    (r := S.graph.DStep) (p := N.graph.DStep) (fun _ _ hab => S.dstep_original hab) a a h)

theorem selected_parent {a : V} (ha : a ≠ N.root) :
    ∃ e : S.Edge, S.graph.target e = a := by
  classical
  by_cases hh : N.graph.IsHybrid a
  · obtain ⟨e, he, hk, _⟩ := S.hybrid_unique a hh
    exact ⟨⟨e, hk⟩, he⟩
  · obtain ⟨e, he, _⟩ := N.incoming_unique_of_indegree_one
      (N.indegree_one_of_nonroot_nonhybrid ha hh)
    have hk : S.keep e := S.ordinary e (by rw [he]; exact hh)
    exact ⟨⟨e, hk⟩, he⟩

theorem selected_uniqueIncoming : S.graph.UniqueIncoming := by
  classical
  intro e f htarget
  change N.graph.target e.val = N.graph.target f.val at htarget
  apply Subtype.ext
  by_cases hh : N.graph.IsHybrid (N.graph.target e.val)
  · obtain ⟨g, _, _, hg⟩ := S.hybrid_unique (N.graph.target e.val) hh
    exact (hg e.val rfl e.property).trans (hg f.val htarget.symm f.property).symm
  · obtain ⟨g, _, hg⟩ := N.incoming_unique_of_indegree_one
      (N.indegree_one_of_nonroot_nonhybrid (N.edge_target_ne_root e.val) hh)
    exact (hg e.val rfl).trans (hg f.val htarget.symm).symm

/-- Finite acyclic upward induction derives root reachability after selection. -/
theorem selected_rooted (a : V) : S.graph.DReach N.root a := by
  classical
  let r : V → V → Prop := fun a b => Relation.TransGen S.graph.DStep a b
  haveI : IsTrans V r := ⟨fun _ _ _ hab hbc => hab.trans hbc⟩
  haveI : Std.Irrefl r := ⟨fun a => S.selected_acyclic a⟩
  have hw : WellFounded r := Finite.wellFounded_of_trans_of_irrefl r
  refine hw.induction (C := fun v => S.graph.DReach N.root v) a ?_
  intro b ih
  by_cases hb : b = N.root
  · subst b
    exact .refl
  · obtain ⟨e, he⟩ := S.selected_parent hb
    have hstep : S.graph.DStep (S.graph.source e) b := ⟨e, rfl, he⟩
    exact (ih (S.graph.source e) (Relation.TransGen.single hstep)).tail hstep

theorem selected_connected (a b : V) : S.graph.UReach (fun _ => True) a b :=
  (S.graph.ureach_symm (S.graph.dreach_ureach (S.selected_rooted a))).trans
    (S.graph.dreach_ureach (S.selected_rooted b))

/-- An actual one-parent selection in the raw network is a tree. -/
theorem selected_is_tree : S.graph.IsTree :=
  ⟨⟨N.root⟩, S.selected_connected,
    S.graph.uniqueIncoming_all_bridges S.selected_uniqueIncoming S.selected_acyclic⟩

end Switching
end RootedBinary
end Nanuq.Source

#print axioms Nanuq.Source.EdgeGraph.uniqueIncoming_all_bridges
#print axioms Nanuq.Source.RootedBinary.Switching.selected_rooted
#print axioms Nanuq.Source.RootedBinary.Switching.selected_is_tree
