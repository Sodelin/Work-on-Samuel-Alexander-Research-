import SourceCompositionBridge

/-!
Exact weighted path arithmetic used in the tree-metrization step.
The graph-dependent fact still to instantiate is that two outside witnesses
separate the path endpoints precisely when they lie in different offshoots.
Here the counting and the per-vertex arithmetic themselves are proved.
-/
namespace Nanuq.TreePath

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Ordered pairs in different offshoots, already including the paper's factor 2. -/
def crossPairs (mass : I → ℚ) : ℚ :=
  ∑ i, ∑ j, if i ≠ j then mass i * mass j else 0

theorem crossPairs_eq_square_sub_squares (mass : I → ℚ) :
    crossPairs mass = (∑ i, mass i)^2 - ∑ i, (mass i)^2 := by
  have hterm : ∀ i j, (if i ≠ j then mass i * mass j else 0) =
      mass i * mass j - if j = i then mass i * mass j else 0 := by
    intro i j
    by_cases hij : i = j
    · simp [hij]
    · simp [hij, Ne.symm hij]
  unfold crossPairs
  simp_rw [hterm, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul, ← pow_two]

/-- The weighted quartet formula equals the sum of the internal path-vertex
contributions c_i (M-c_i). Endpoint masses can be arbitrary rationals. -/
theorem weighted_path_identity (mass : I → ℚ) (total endpointMass : ℚ)
    (hpartition : (∑ i, mass i) + endpointMass = total) :
    crossPairs mass + endpointMass * (∑ i, mass i) =
      ∑ i, mass i * (total - mass i) := by
  rw [crossPairs_eq_square_sub_squares, ← hpartition]
  simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, ← pow_two]
  ring

/-- A path vertex has offshoot, left, and right mass. Its two contributions
along the path equal the expression in weighted_path_identity. -/
theorem vertex_endpoint_contributions (off left right total : ℚ)
    (hpartition : off + left + right = total) :
    off * left + off * right = off * (total - off) := by
  rw [← hpartition]
  ring

/-- Substituting unit endpoint masses recovers the exact source constant 2n-4. -/
theorem unit_source_path_identity (mass : I → ℚ) (n : ℚ)
    (hpartition : (∑ i, mass i) = n - 2) :
    crossPairs mass + 2 * n - 4 = ∑ i, mass i * (n - mass i) := by
  have h := weighted_path_identity mass n 2 (by rw [hpartition]; ring)
  rw [hpartition] at h
  calc
    _ = crossPairs mass + 2 * (n - 2) := by ring
    _ = _ := h

#print axioms weighted_path_identity
#print axioms vertex_endpoint_contributions
#print axioms unit_source_path_identity

end Nanuq.TreePath
