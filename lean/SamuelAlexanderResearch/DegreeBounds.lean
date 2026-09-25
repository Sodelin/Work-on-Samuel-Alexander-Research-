import Std

/-!
Counting consequences of the population axioms.

The graph-theoretic counting step is an explicit premise: in a birthdate prefix
of `n` vertices with `r` roots, each non-root has `k` distinct parents, so
`k * (n - r)` edges lie within the prefix. An outdegree cap of `d` gives at
most `d * n` such edges. These lemmas verify the arithmetic conclusions from
those two counts. They do not formalize the graph or birthdate axioms.
-/

namespace PopulationDegree

theorem offspring_threshold
    (k d n r : Nat) (hr : r ≤ n)
    (hedges : k * (n - r) ≤ d * n) :
    (k - d) * n ≤ k * r := by
  by_cases hdk : d ≤ k
  · have hk : k = d + (k - d) := by omega
    have hn : n = (n - r) + r := by omega
    have hcount : k * n = k * (n - r) + k * r := by
      calc
        k * n = k * ((n - r) + r) := congrArg (fun x => k * x) hn
        _ = k * (n - r) + k * r := Nat.mul_add k (n - r) r
    have hsplit : k * n = d * n + (k - d) * n := by
      calc
        k * n = (d + (k - d)) * n := congrArg (fun x => x * n) hk
        _ = d * n + (k - d) * n := Nat.add_mul d (k - d) n
    omega
  · have hz : k - d = 0 := by omega
    simp [hz]

theorem binary_vertex_gender_balance
    (n r male female : Nat) (hr : r ≤ n)
    (hpartition : n = male + female)
    (hmale_edges : n - r ≤ 2 * male)
    (hfemale_edges : n - r ≤ 2 * female) :
    male ≤ female + r ∧ female ≤ male + r := by
  omega

end PopulationDegree
