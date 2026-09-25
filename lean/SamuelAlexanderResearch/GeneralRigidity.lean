import SamuelAlexanderResearch.MinimalCrossing

/-! Minimum root-free crossing width determines the k-th power of a ray,
for every finite number k of required labels. -/

namespace GeneralRigidity
open PopulationCounting InfiniteConservation

theorem sumBelow_eq_pointwise {n : Nat} {f g : Nat → Nat}
    (hle : ∀ i, i < n → f i ≤ g i)
    (heq : sumBelow n f = sumBelow n g) :
    ∀ i, i < n → f i = g i := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    have hs := sumBelow_mono (n := n) (f := f) (g := g)
      (fun i hi => hle i (by omega))
    have hn := hle n (by omega)
    simp only [sumBelow_succ] at heq
    have he : sumBelow n f = sumBelow n g := by omega
    intro i hi
    by_cases hin : i < n
    · exact ih (fun j hj => hle j (by omega)) he i hin
    · have : i = n := by omega
      subst i
      omega

theorem minimum_cut_no_late_target {k d : Nat}
    (p : InfiniteLabeledPopulation k d) (n : Nat)
    (hn : p.rootSupport ≤ n) (hc : crossingCount p n = triangular k)
    (u v : Nat) (hu : u < n) (hv : n+k ≤ v) : p.edge u v = none := by
  have h := MinimalCrossing.target_block_le_crossing p n (v-n+1)
  rw [sumBelow_succ] at h
  have hm := sumBelow_range_mono (show k ≤ v-n by omega)
    (fun i => incomingFromPrefix p n (n+i))
  have hl : triangular k ≤ sumBelow k (fun i => incomingFromPrefix p n (n+i)) :=
    sumBelow_mono (fun i _ => old_parent_lower p n i hn)
  have he : n+(v-n) = v := by omega
  rw [he, hc] at h
  have ht := term_le_sumBelow (fun a => edgeBit (p.edge a v)) hu
  change edgeBit (p.edge u v) ≤ incomingFromPrefix p n v at ht
  cases he : p.edge u v with
  | none => rfl
  | some label => simp [he, edgeBit] at ht; omega

theorem regular_of_equal_crossing {k : Nat} (p : InfiniteLabeledPopulation k k)
    (n : Nat) (hn : p.rootSupport ≤ n)
    (hc : crossingCount p (n+1) = crossingCount p n) :
    p.root n = false ∧ fullInDegree p n = k ∧ fullOutDegree p n = k := by
  have h0 := conservation p n
  have h1 := conservation p (n+1)
  rw [roots_stable p n hn] at h0
  rw [roots_stable p (n+1) (by omega)] at h1
  change totalDefect p n + crossingCount p n = _ at h0
  change totalDefect p (n+1) + crossingCount p (n+1) = _ at h1
  have hs := total_defect_succ p n
  have hd : localDefect p n = 0 := by omega
  have hr := p.no_roots_after n hn
  have hi := full_indegree_lower p n hr
  have ho : fullOutDegree p n ≤ k := p.child_cap n
  simp only [localDefect, hr, Bool.false_eq_true, ↓reduceIte] at hd
  exact ⟨hr, by omega, by omega⟩

theorem outdegree_short_block {k d : Nat} (p : InfiniteLabeledPopulation k d)
    (u : Nat) (hlong : ∀ v, u+1+k ≤ v → p.edge u v = none) :
    fullOutDegree p u = sumBelow k (fun i => edgeBit (p.edge u (u+1+i))) := by
  let f := fun v => edgeBit (p.edge u v)
  have hs : fullOutDegree p u = sumBelow (u+1+k) f := by
    apply Nat.le_antisymm
    · apply sumBelow_le_support f (u+1+k) (p.childSupport u)
      intro v hv
      simp [f, hlong v hv, edgeBit]
    · apply sumBelow_le_support f (p.childSupport u) (u+1+k)
      intro v hv
      simp [f, p.no_children_after u v hv, edgeBit]
  have hz : sumBelow (u+1) f = 0 := by
    calc
      _ = sumBelow (u+1) (fun _ => 0) := sumBelow_congr (fun v hv => by
        simp [f, no_parent_at_or_after p u v (by omega), edgeBit])
      _ = 0 := by simp
  rw [hs, sumBelow_shift, hz, Nat.zero_add]

/-- Every minimum-width root-free tail has exactly all edges of lengths 1,...,k. -/
theorem minimum_tail_edges {k : Nat} (p : InfiniteLabeledPopulation k k)
    (start : Nat) (hr : p.rootSupport ≤ start)
    (hc : ∀ n, start ≤ n → crossingCount p n = triangular k) :
    ∀ u, start ≤ u → ∀ v,
      (p.edge u v).isSome = true ↔ u < v ∧ v ≤ u+k := by
  intro u hu
  have hlong : ∀ v, u+1+k ≤ v → p.edge u v = none := by
    intro v hv
    exact minimum_cut_no_late_target p (u+1) (by omega)
      (hc (u+1) (by omega)) u v (by omega) hv
  have hregular := regular_of_equal_crossing p u (by omega)
    (by rw [hc u hu, hc (u+1) (by omega)])
  have hsum := outdegree_short_block p u hlong
  rw [hregular.2.2] at hsum
  have hevery : ∀ i, i < k → edgeBit (p.edge u (u+1+i)) = 1 := by
    apply sumBelow_eq_pointwise (g := fun _ => 1)
    · intro i _; exact edgeBit_le_one _
    · simpa using hsum.symm
  intro v
  constructor
  · intro he
    have ho := p.birth_order u v he
    by_cases hv : u+1+k ≤ v
    · rw [hlong v hv] at he
      contradiction
    · omega
  · intro hv
    have he := hevery (v-(u+1)) (by omega)
    have hv' : u+1+(v-(u+1)) = v := by omega
    rw [hv'] at he
    cases hx : p.edge u v with
    | none => simp [hx, edgeBit] at he
    | some label => simp

/-- Eventual equality in the displayed numerical triangular bound implies
eventual exact k-th-power-of-a-ray geometry, including k=0. -/
theorem eventually_minimum_tail_edges {k : Nat} (p : InfiniteLabeledPopulation k k)
    (hc : ∃ start, ∀ n, start ≤ n → crossingCount p n = k*(k+1)/2) :
    ∃ start, ∀ u, start ≤ u → ∀ v,
      (p.edge u v).isSome = true ↔ u < v ∧ v ≤ u+k := by
  obtain ⟨s, hs⟩ := hc
  refine ⟨s+p.rootSupport, minimum_tail_edges p (s+p.rootSupport) (by omega) ?_⟩
  intro n hn
  have he : k*(k+1)/2 = triangular k := by rw [← twice_triangular]; omega
  rw [hs n (by omega), he]

#print axioms minimum_cut_no_late_target
#print axioms minimum_tail_edges
#print axioms eventually_minimum_tail_edges

end GeneralRigidity
