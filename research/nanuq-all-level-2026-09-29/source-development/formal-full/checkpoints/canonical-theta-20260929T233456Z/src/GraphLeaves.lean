import SourceNetwork
import Mathlib.Data.Fintype.EquivFin

namespace Nanuq.Source
namespace EdgeGraph

variable {V E : Type*} (G : EdgeGraph V E)

theorem dreach_preserves {P : V → Prop}
    (closed : ∀ a b, G.DStep a b → P a → P b)
    {a b : V} (hab : G.DReach a b) (ha : P a) : P b := by
  induction hab with
  | refl => exact ha
  | tail _ hstep ih => exact closed _ _ hstep ih

end EdgeGraph

namespace RootedBinary
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X)

theorem outDegree_pos_of_not_leaf {a : V} (h : ¬ ∃ x, N.leaf x = a) :
    0 < N.graph.outDegree a := by
  by_cases har : a = N.root
  · rw [har, N.root_degrees.2]
    exact Nat.zero_lt_succ 1
  · have hi := N.internal_degrees a har (fun x hx => h ⟨x, hx⟩)
    rcases hi with ht | hh
    · rw [ht.2]
      exact Nat.zero_lt_succ 1
    · rw [hh.2]
      exact Nat.zero_lt_succ 0

theorem leaf_iff_outDegree_zero (a : V) :
    (∃ x, N.leaf x = a) ↔ N.graph.outDegree a = 0 := by
  constructor
  · rintro ⟨x, rfl⟩
    exact (N.leaf_degrees x).2
  · intro hzero
    classical
    by_contra hn
    have hp := N.outDegree_pos_of_not_leaf hn
    rw [hzero] at hp
    exact Nat.lt_irrefl 0 hp

/-- Actual descendant-leaf existence derived from finite directed acyclicity. -/
theorem every_vertex_reaches_leaf (a : V) :
    ∃ x, N.graph.DReach a (N.leaf x) := by
  classical
  let r : V → V → Prop := fun b a => Relation.TransGen N.graph.DStep a b
  haveI : IsTrans V r := ⟨fun _ _ _ hab hbc => hbc.trans hab⟩
  haveI : Std.Irrefl r := ⟨fun a => N.acyclic a⟩
  have hw : WellFounded r := Finite.wellFounded_of_trans_of_irrefl r
  refine hw.induction (C := fun v => ∃ x, N.graph.DReach v (N.leaf x)) a ?_
  intro v ih
  by_cases hl : ∃ x, N.leaf x = v
  · obtain ⟨x, rfl⟩ := hl
    exact ⟨x, .refl⟩
  · have hp := N.outDegree_pos_of_not_leaf hl
    obtain ⟨e, he⟩ := Finset.card_pos.mp hp
    have hs : N.graph.source e = v := (Finset.mem_filter.mp he).2
    have hstep : N.graph.DStep v (N.graph.target e) := ⟨e, hs, rfl⟩
    obtain ⟨x, hx⟩ := ih (N.graph.target e) (Relation.TransGen.single hstep)
    exact ⟨x, (Relation.ReflTransGen.single hstep).trans hx⟩

theorem forward_closed_contains_leaf {P : V → Prop}
    (hclosed : ∀ a b, N.graph.DStep a b → P a → P b)
    {a : V} (ha : P a) : ∃ x, P (N.leaf x) := by
  obtain ⟨x, hx⟩ := N.every_vertex_reaches_leaf a
  exact ⟨x, N.graph.dreach_preserves hclosed hx ha⟩

/-- LSA supplies a real root-to-leaf walk avoiding every non-root vertex. -/
theorem exists_leaf_avoiding_of_ne_root {a : V} (hne : a ≠ N.root) :
    ∃ x, N.graph.AvoidReach a N.root (N.leaf x) := by
  classical
  by_contra hn
  apply hne
  apply N.least_stable a
  intro x hx
  exact hn ⟨x, hx⟩

end RootedBinary
end Nanuq.Source

#print axioms Nanuq.Source.RootedBinary.every_vertex_reaches_leaf
#print axioms Nanuq.Source.RootedBinary.forward_closed_contains_leaf
#print axioms Nanuq.Source.RootedBinary.exists_leaf_avoiding_of_ne_root
