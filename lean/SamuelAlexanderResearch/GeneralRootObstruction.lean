import SamuelAlexanderResearch.InfiniteConservation
import SamuelAlexanderResearch.SpeciesRootCriterion

/-!
# The first `k` vertices are roots in a simple labelled chronological graph

The generic model requires only one optional label per ordered vertex pair,
strict natural edge order, and every label below `k` at each vertex having a
parent. It does not assume finite roots, finite children, or an outdegree cap.
The existing `InfiniteLabeledPopulation` model has this local structure.

This finite-alphabet root obstruction does not assert any word-realization or
unavoidability theorem for an arbitrary finite alphabet.
-/

namespace GeneralRootObstruction

open PopulationCounting SpeciesBridge

/-- A functional edge label, strict chronology, and local incoming coverage.
No root marker or global degree/support conditions are part of this model. -/
structure ChronologicalLabelledGraph (k : Nat) where
  edge : Nat → Nat → Option Nat
  birth_order : ∀ u v, (edge u v).isSome = true → u < v
  parent_of_label : ∀ v, (∃ u, (edge u v).isSome = true) →
    ∀ label, label < k → ∃ u, edge u v = some label

def Edge {k : Nat} (p : ChronologicalLabelledGraph k) : Graph :=
  fun u v => (p.edge u v).isSome = true

theorem no_parent_at_or_after {k : Nat} (p : ChronologicalLabelledGraph k)
    (u v : Nat) (hvu : v ≤ u) : p.edge u v = none := by
  cases he : p.edge u v with
  | none => rfl
  | some label =>
    have := p.birth_order u v (by simp [he])
    omega

/-- All parents of `v` are below `v`, so this counts its full incoming set. -/
def incomingCount {k : Nat} (p : ChronologicalLabelledGraph k) (v : Nat) : Nat :=
  sumBelow v (fun u => edgeBit (p.edge u v))

theorem incomingCount_le_vertex {k : Nat} (p : ChronologicalLabelledGraph k)
    (v : Nat) : incomingCount p v ≤ v := by
  calc
    incomingCount p v ≤ sumBelow v (fun _ => 1) := by
      apply sumBelow_mono
      intro u _
      cases p.edge u v <;> simp [edgeBit]
    _ = v := by simp

/-- Distinct labels require distinct parents because each ordered pair has
only one optional label. This lower bound is derived, not assumed. -/
theorem incomingCount_lower {k : Nat} (p : ChronologicalLabelledGraph k)
    (v : Nat) (hparent : ∃ u, Edge p u v) : k ≤ incomingCount p v := by
  have labels : ∀ label, label < k →
      1 ≤ sumBelow v (fun u => if p.edge u v = some label then 1 else 0) := by
    intro label hl
    obtain ⟨u, he⟩ := p.parent_of_label v hparent label hl
    have hu := p.birth_order u v (by simp [he])
    have h := term_le_sumBelow (fun u => if p.edge u v = some label then 1 else 0) hu
    simpa [he] using h
  calc
    k = sumBelow k (fun _ => 1) := by simp
    _ ≤ sumBelow k (fun label => sumBelow v
        (fun u => if p.edge u v = some label then 1 else 0)) := sumBelow_mono labels
    _ = sumBelow v (fun u => sumBelow k
        (fun label => if p.edge u v = some label then 1 else 0)) := sumBelow_swap k v _
    _ ≤ incomingCount p v :=
      sumBelow_mono (fun u _ => label_indicators_le_edge k (p.edge u v))

/-- Every one of the first `k` vertices has no parents in the actual graph. -/
theorem initial_vertex_root {k : Nat} (p : ChronologicalLabelledGraph k)
    (v : Nat) (hv : v < k) : Root (Edge p) v := by
  intro u hu
  have lower := incomingCount_lower p v ⟨u, hu⟩
  have upper := incomingCount_le_vertex p v
  omega

theorem at_least_k_distinct_roots {k : Nat} (p : ChronologicalLabelledGraph k) :
    ∃ roots : List Nat, roots.Nodup ∧ roots.length = k ∧
      ∀ v, v ∈ roots → Root (Edge p) v := by
  refine ⟨List.range k, List.nodup_range, List.length_range, ?_⟩
  intro v hv
  exact initial_vertex_root p v (List.mem_range.mp hv)

theorem not_commonAncestor {k : Nat} (p : ChronologicalLabelledGraph k)
    (hk : 2 ≤ k) : ¬ CommonAncestor (Edge p) Whole := by
  rintro ⟨a, _, ha⟩
  by_cases heq : a = 0
  · subst a
    exact SpeciesRootCriterion.root_has_no_ancestor
      (initial_vertex_root p 1 (by omega)) (ha 1 trivial (by omega))
  · exact SpeciesRootCriterion.root_has_no_ancestor
      (initial_vertex_root p 0 (by omega)) (ha 0 trivial (by omega))

/-- The global population axioms imply the local labelled chronological model. -/
def ofInfinitePopulation {k d : Nat} (p : InfiniteLabeledPopulation k d) :
    ChronologicalLabelledGraph k where
  edge := p.edge
  birth_order := p.birth_order
  parent_of_label := by
    intro v hparent label hl
    have hr : p.root v = false := by
      cases hroot : p.root v with
      | false => rfl
      | true =>
        obtain ⟨u, hu⟩ := hparent
        have hnone := p.root_no_parents v hroot u
        simp [hnone] at hu
    exact p.parent_of_label v hr label hl

theorem ofInfinitePopulation_edge {k d : Nat} (p : InfiniteLabeledPopulation k d) :
    Edge (ofInfinitePopulation p) = (fun u v => (p.edge u v).isSome = true) := rfl

theorem fullInDegree_le_vertex {k d : Nat} (p : InfiniteLabeledPopulation k d)
    (v : Nat) : InfiniteConservation.fullInDegree p v ≤ v :=
  incomingCount_le_vertex (ofInfinitePopulation p) v

/-- The actual first `k` roots are also marked as roots in the existing model. -/
theorem initial_declared_root {k d : Nat} (p : InfiniteLabeledPopulation k d)
    (v : Nat) (hv : v < k) : p.root v = true := by
  cases hr : p.root v with
  | true => rfl
  | false =>
    have lower := InfiniteConservation.full_indegree_lower p v hr
    have upper := fullInDegree_le_vertex p v
    omega

theorem initial_population_roots {k d : Nat} (p : InfiniteLabeledPopulation k d)
    (v : Nat) (hv : v < k) :
    p.root v = true ∧ Root (fun u w => (p.edge u w).isSome = true) v :=
  ⟨initial_declared_root p v hv, initial_vertex_root (ofInfinitePopulation p) v hv⟩

theorem alphabet_le_fullRootCount {k d : Nat} (p : InfiniteLabeledPopulation k d) :
    k ≤ fullRootCount p := by
  have hprefix : rootCount (infinitePrefix p k) = k := by
    change sumBelow k (fun v => if p.root v then 1 else 0) = k
    calc
      _ = sumBelow k (fun _ => 1) := by
        apply sumBelow_congr
        intro v hv
        simp [initial_declared_root p v hv]
      _ = k := by simp
  have hbound := infinite_prefix_root_bound p k
  omega

theorem population_not_commonAncestor {k d : Nat} (p : InfiniteLabeledPopulation k d)
    (hk : 2 ≤ k) :
    ¬ CommonAncestor (fun u v => (p.edge u v).isSome = true) Whole :=
  not_commonAncestor (ofInfinitePopulation p) hk

/-- The finite root count and the whole-graph CA obstruction, together. -/
theorem population_root_obstruction {k d : Nat} (p : InfiniteLabeledPopulation k d)
    (hk : 2 ≤ k) : k ≤ fullRootCount p ∧
      ¬ CommonAncestor (fun u v => (p.edge u v).isSome = true) Whole :=
  ⟨alphabet_le_fullRootCount p, population_not_commonAncestor p hk⟩

end GeneralRootObstruction

#print axioms GeneralRootObstruction.incomingCount_lower
#print axioms GeneralRootObstruction.initial_vertex_root
#print axioms GeneralRootObstruction.at_least_k_distinct_roots
#print axioms GeneralRootObstruction.not_commonAncestor
#print axioms GeneralRootObstruction.ofInfinitePopulation
#print axioms GeneralRootObstruction.initial_declared_root
#print axioms GeneralRootObstruction.alphabet_le_fullRootCount
#print axioms GeneralRootObstruction.population_not_commonAncestor
#print axioms GeneralRootObstruction.population_root_obstruction
