import WongGARG

/-! Appendix F: local child sets are subsets of the ARG child set.
Arity counts distinct children, not stored records or interval fragments. -/
namespace WongLocalArity
open WongGARG
universe u v
noncomputable section
variable {Node : Type u} {Coord : Type v} [Fintype Node] [LinearOrder Coord]

def graphChildren (G : GARG Node Coord) (a : Node) : Finset Node := by
  classical
  exact Finset.univ.filter (G.Topology a)

def localChildren (G : GARG Node Coord) (x : Coord) (a : Node) : Finset Node := by
  classical
  exact Finset.univ.filter (G.AtLocus x a)

@[simp] theorem mem_graphChildren (G : GARG Node Coord) (a b : Node) :
    b ∈ graphChildren G a ↔ G.Topology a b := by
  classical
  simp [graphChildren]

@[simp] theorem mem_localChildren (G : GARG Node Coord) (x : Coord) (a b : Node) :
    b ∈ localChildren G x a ↔ G.AtLocus x a b := by
  classical
  simp [localChildren]

theorem local_children_subset (G : GARG Node Coord) (x : Coord) (a : Node) :
    localChildren G x a ⊆ graphChildren G a := by
  intro b hb
  exact (mem_graphChildren G a b).mpr
    (G.locus_edge_topology ((mem_localChildren G x a b).mp hb))

/-- The local arity bound uses no sample-resolution or unique-parent premise. -/
theorem local_arity_le_graph_arity (G : GARG Node Coord) (x : Coord) (a : Node) :
    (localChildren G x a).card ≤ (graphChildren G a).card :=
  Finset.card_le_card (local_children_subset G x a)

/-- A globally unary node is locally absent as a parent, or locally unary. -/
theorem graph_unary_local_zero_or_one (G : GARG Node Coord) (x : Coord) (a : Node)
    (h : (graphChildren G a).card = 1) :
    (localChildren G x a).card = 0 ∨ (localChildren G x a).card = 1 := by
  have := local_arity_le_graph_arity G x a
  omega

/-- At a coordinate where its child edge exists, a globally unary node is unary. -/
theorem graph_unary_present_locally_unary (G : GARG Node Coord) (x : Coord)
    (a b : Node) (h : (graphChildren G a).card = 1) (he : G.AtLocus x a b) :
    (localChildren G x a).card = 1 := by
  have hp : 0 < (localChildren G x a).card :=
    Finset.card_pos.mpr ⟨b, (mem_localChildren G x a b).mpr he⟩
  have := local_arity_le_graph_arity G x a
  omega

/-- A backward local walk can take no more steps than its starting rank.
This bounds traversal; it is not a runtime complexity claim about software. -/
theorem backward_local_walk_bound (G : GARG Node Coord) (x : Coord)
    (path : Nat → Node) (m : Nat)
    (edges : ∀ i, i < m → G.AtLocus x (path (i + 1)) (path i)) :
    m ≤ G.orderCode (path 0) := by
  have bound : ∀ k, k ≤ m → G.orderCode (path k) + k ≤ G.orderCode (path 0) := by
    intro k
    induction k with
    | zero => intro _; omega
    | succ k ih =>
      intro hk
      have prev := ih (by omega)
      have step := G.orderCode_edge (G.locus_edge_topology (edges k (by omega)))
      omega
  have := bound m (Nat.le_refl m)
  omega

theorem no_infinite_backward_local_walk (G : GARG Node Coord) (x : Coord) :
    ¬ ∃ path : Nat → Node, ∀ i, G.AtLocus x (path (i + 1)) (path i) := by
  rintro ⟨path, edges⟩
  have := backward_local_walk_bound G x path (G.orderCode (path 0) + 1)
    (fun i _ => edges i)
  omega

/-- The optional parent array obeys the same finite traversal bound. -/
theorem backward_parent_array_bound (G : GARG Node Coord) (x : Coord)
    (unique : G.UniqueParentAt x) (path : Nat → Node) (m : Nat)
    (steps : ∀ i, i < m → G.localParent x (path i) = some (path (i + 1))) :
    m < Fintype.card Node * Fintype.card Node := by
  have h := backward_local_walk_bound G x path m (fun i hi =>
    (G.localParent_eq_some_iff x unique _ _).mp (steps i hi))
  exact lt_of_le_of_lt h (G.orderCode_lt_bound _)
end
end WongLocalArity
#print axioms WongLocalArity.local_children_subset
#print axioms WongLocalArity.local_arity_le_graph_arity
#print axioms WongLocalArity.graph_unary_local_zero_or_one
#print axioms WongLocalArity.graph_unary_present_locally_unary

#print axioms WongLocalArity.backward_local_walk_bound
#print axioms WongLocalArity.no_infinite_backward_local_walk
#print axioms WongLocalArity.backward_parent_array_bound
