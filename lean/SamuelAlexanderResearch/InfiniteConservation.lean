import SamuelAlexanderResearch.PopulationCounting
import SamuelAlexanderResearch.BinaryAvoidance

/-!
Full-degree conservation and finite defects in the actual naturally ordered
infinite population model. Finite support bounds certify all outgoing counts;
birth order certifies the full incoming counts. No aggregate count, cut bound,
or eventual regularity assumption is added to the population model.
-/

namespace InfiniteConservation
open PopulationCounting

/-- Once a summation range contains the support, it gives the full sum. -/
theorem sum_eq_support (f : Nat → Nat) (b m : Nat) (hb : b ≤ m)
    (hz : ∀ i, b ≤ i → f i = 0) : sumBelow m f = sumBelow b f :=
  Nat.le_antisymm (sumBelow_le_support f b m hz) (sumBelow_range_mono hb f)

/-- Birth order excludes every parent at or beyond the child's index. -/
theorem no_parent_at_or_after {k d : Nat} (p : InfiniteLabeledPopulation k d)
    (u v : Nat) (hvu : v ≤ u) : p.edge u v = none := by
  cases he : p.edge u v with
  | none => rfl
  | some label =>
    have h := p.birth_order u v (by simp [he])
    omega

/-- This is the full indegree: every actual parent of `v` has index below `v`. -/
def fullInDegree {k d : Nat} (p : InfiniteLabeledPopulation k d) (v : Nat) : Nat :=
  sumBelow v (fun u => edgeBit (p.edge u v))

def prefixRootCount {k d : Nat} (p : InfiniteLabeledPopulation k d) (n : Nat) : Nat :=
  sumBelow n (fun v => if p.root v then 1 else 0)

/-- Outgoing deficit uses the full infinite-graph outdegree. -/
def outgoingDeficit {k : Nat} (p : InfiniteLabeledPopulation k k) (n : Nat) : Nat :=
  sumBelow n (fun u => k - fullOutDegree p u)

/-- Incoming excess uses full indegrees and excludes roots. -/
def incomingExcess {k : Nat} (p : InfiniteLabeledPopulation k k) (n : Nat) : Nat :=
  sumBelow n (fun v => if p.root v then 0 else fullInDegree p v - k)

/-- Every actual edge from the first `n` vertices to its infinite complement. -/
def crossingCount {k d : Nat} (p : InfiniteLabeledPopulation k d) (n : Nat) : Nat :=
  sumBelow n (fun u => sumBelow (p.childSupport u)
    (fun v => if n ≤ v then edgeBit (p.edge u v) else 0))

def totalDefect {k : Nat} (p : InfiniteLabeledPopulation k k) (n : Nat) : Nat :=
  outgoingDeficit p n + incomingExcess p n

/-- A finite ambient range containing the prefix and all of its children's supports. -/
def ambientBound {k d : Nat} (p : InfiniteLabeledPopulation k d) (n : Nat) : Nat :=
  n + 1 + sumBelow n p.childSupport

theorem prefix_le_ambient {k d : Nat} (p : InfiniteLabeledPopulation k d) (n : Nat) :
    n ≤ ambientBound p n := by simp [ambientBound]; omega

theorem support_le_ambient {k d : Nat} (p : InfiniteLabeledPopulation k d)
    (n u : Nat) (hu : u < n) : p.childSupport u ≤ ambientBound p n := by
  have h := term_le_sumBelow p.childSupport hu
  simp only [ambientBound]
  omega

/-- Finite ambient outdegrees agree with full degrees once all children are included. -/
theorem finite_outdegree_eq {k d : Nat} (p : InfiniteLabeledPopulation k d)
    (m u : Nat) (hs : p.childSupport u ≤ m) :
    outDegree (infinitePrefix p m).toLabeledGraph u = fullOutDegree p u := by
  apply sum_eq_support (fun v => edgeBit (p.edge u v)) (p.childSupport u) m hs
  intro v hv
  simp [p.no_children_after u v hv, edgeBit]

/-- Finite ambient indegrees agree with full degrees once the vertex is included. -/
theorem finite_indegree_eq {k d : Nat} (p : InfiniteLabeledPopulation k d)
    (m v : Nat) (hv : v ≤ m) :
    inDegree (infinitePrefix p m).toLabeledGraph v = fullInDegree p v := by
  apply sum_eq_support (fun u => edgeBit (p.edge u v)) v m hv
  intro u hu
  simp [no_parent_at_or_after p u v hu, edgeBit]

theorem full_indegree_lower {k d : Nat} (p : InfiniteLabeledPopulation k d)
    (v : Nat) (hr : p.root v = false) : k ≤ fullInDegree p v := by
  have h := nonroot_indegree (infinitePrefix p (v+1)) v (by omega) hr
  rw [finite_indegree_eq p (v+1) v (by omega)] at h
  exact h

theorem full_indegree_root {k d : Nat} (p : InfiniteLabeledPopulation k d)
    (v : Nat) (hr : p.root v = true) : fullInDegree p v = 0 := by
  have h := root_indegree_zero (infinitePrefix p (v+1)) v (by omega) hr
  rw [finite_indegree_eq p (v+1) v (by omega)] at h
  exact h

/-- Transferring the finite cut count preserves every outgoing crossing edge. -/
theorem finite_crossing_eq {k d : Nat} (p : InfiniteLabeledPopulation k d) (n : Nat) :
    PopulationCounting.crossingCount (infinitePrefix p (ambientBound p n)).toLabeledGraph n =
      crossingCount p n := by
  apply sumBelow_congr
  intro u hu
  apply sum_eq_support (fun v => if n ≤ v then edgeBit (p.edge u v) else 0)
    (p.childSupport u) (ambientBound p n) (support_le_ambient p n u hu)
  intro v hv
  simp [p.no_children_after u v hv, edgeBit]

/-- Genuine infinite full-degree conservation for every natural birth-order prefix. -/
theorem conservation {k : Nat} (p : InfiniteLabeledPopulation k k) (n : Nat) :
    outgoingDeficit p n + incomingExcess p n + crossingCount p n = k * prefixRootCount p n := by
  let m := ambientBound p n
  let q := infinitePrefix p m
  have hm : n ≤ m := prefix_le_ambient p n
  have hc : PredecessorClosed q.toLabeledGraph n := by
    intro u _ v hv he
    have h := p.birth_order u v he
    omega
  have h := PopulationCounting.critical_degree_conservation q n hm hc
  have hd : PopulationCounting.outgoingDeficit q n = outgoingDeficit p n := by
    apply sumBelow_congr
    intro u hu
    rw [finite_outdegree_eq p m u (support_le_ambient p n u hu)]
  have he : PopulationCounting.incomingExcess q n = incomingExcess p n := by
    apply sumBelow_congr
    intro v hv
    rw [finite_indegree_eq p m v (by omega)]
    rfl
  have hx : PopulationCounting.crossingCount q.toLabeledGraph n = crossingCount p n :=
    finite_crossing_eq p n
  rw [hd, he, hx] at h
  exact h

/-- The parents of the first outside vertex are all counted among the crossing edges. -/
theorem indegree_le_crossing {k d : Nat} (p : InfiniteLabeledPopulation k d) (n : Nat) :
    fullInDegree p n ≤ crossingCount p n := by
  apply sumBelow_mono
  intro u _
  by_cases hs : n < p.childSupport u
  · have h := term_le_sumBelow (fun v => if n ≤ v then edgeBit (p.edge u v) else 0) hs
    simpa using h
  · have he := p.no_children_after u n (by omega)
    simp [he, edgeBit]

/-- After all roots, the first outside vertex forces at least `k` crossing edges. -/
theorem crossing_lower_after_roots {k d : Nat} (p : InfiniteLabeledPopulation k d)
    (n : Nat) (hn : p.rootSupport ≤ n) : k ≤ crossingCount p n := by
  exact Nat.le_trans (full_indegree_lower p n (p.no_roots_after n hn)) (indegree_le_crossing p n)

theorem roots_stable {k d : Nat} (p : InfiniteLabeledPopulation k d)
    (n : Nat) (hn : p.rootSupport ≤ n) : prefixRootCount p n = fullRootCount p := by
  apply sum_eq_support (fun v => if p.root v then 1 else 0) p.rootSupport n hn
  intro v hv
  simp [p.no_roots_after v hv]

/-- Every cut has width at most `k` times the full root count. -/
theorem crossing_upper {k : Nat} (p : InfiniteLabeledPopulation k k) (n : Nat) :
    crossingCount p n ≤ k * fullRootCount p := by
  have hc := conservation p n
  have hr := infinite_prefix_root_bound p n
  change prefixRootCount p n ≤ fullRootCount p at hr
  have hm := Nat.mul_le_mul_left k hr
  omega

/-- Total full-degree defects have a uniform bound at every prefix. -/
theorem total_defect_bound {k : Nat} (p : InfiniteLabeledPopulation k k) (n : Nat) :
    totalDefect p n ≤ k * fullRootCount p := by
  have hc := conservation p n
  have hr := infinite_prefix_root_bound p n
  change prefixRootCount p n ≤ fullRootCount p at hr
  have hm := Nat.mul_le_mul_left k hr
  unfold totalDefect
  omega

/-- The sharper defect budget after the last root. -/
theorem sharp_defect_bound_after_roots {k : Nat} (p : InfiniteLabeledPopulation k k)
    (n : Nat) (hn : p.rootSupport ≤ n) : totalDefect p n ≤ k * (fullRootCount p - 1) := by
  have hc := conservation p n
  rw [roots_stable p n hn] at hc
  have hl := crossing_lower_after_roots p n hn
  unfold totalDefect
  rw [Nat.mul_sub, Nat.mul_one]
  omega

#print axioms full_indegree_lower
#print axioms conservation
#print axioms indegree_le_crossing
#print axioms crossing_lower_after_roots
#print axioms crossing_upper
#print axioms sharp_defect_bound_after_roots

/-- A vertex's nonnegative outgoing deficit plus nonroot incoming excess. -/
def localDefect {k : Nat} (p : InfiniteLabeledPopulation k k) (v : Nat) : Nat :=
  (k - fullOutDegree p v) + (if p.root v then 0 else fullInDegree p v - k)

theorem total_defect_eq_sum {k : Nat} (p : InfiniteLabeledPopulation k k) (n : Nat) :
    totalDefect p n = sumBelow n (localDefect p) := by
  exact (sumBelow_add n _ _).symm

theorem total_defect_mono {k : Nat} (p : InfiniteLabeledPopulation k k)
    (n m : Nat) (hnm : n ≤ m) : totalDefect p n ≤ totalDefect p m := by
  rw [total_defect_eq_sum, total_defect_eq_sum]
  exact sumBelow_range_mono hnm _

theorem total_defect_succ {k : Nat} (p : InfiniteLabeledPopulation k k) (n : Nat) :
    totalDefect p (n+1) = totalDefect p n + localDefect p n := by
  rw [total_defect_eq_sum, sumBelow_succ, ← total_defect_eq_sum]

/-- The sharp budget also bounds earlier prefixes, by nonnegative monotonicity. -/
theorem sharp_defect_bound {k : Nat} (p : InfiniteLabeledPopulation k k) (n : Nat) :
    totalDefect p n ≤ k * (fullRootCount p - 1) := by
  exact Nat.le_trans (total_defect_mono p n (n + p.rootSupport) (by omega))
    (sharp_defect_bound_after_roots p (n + p.rootSupport) (by omega))

/-- Bounded integral defect sums eventually stop increasing. -/
theorem defects_stabilize {k : Nat} (p : InfiniteLabeledPopulation k k) :
    ∃ start, ∀ n, start ≤ n → totalDefect p n = totalDefect p start := by
  let budget := k * (fullRootCount p - 1)
  let remaining := fun n => budget - totalDefect p n
  have hdecr : ∀ n, remaining (n+1) ≤ remaining n := by
    intro n
    have hm := total_defect_mono p n (n+1) (by omega)
    dsimp [remaining]
    omega
  obtain ⟨start, hs⟩ := BinaryAvoidance.decreasing_nat_stabilizes remaining hdecr
  refine ⟨start, ?_⟩
  intro n hn
  have he := hs n hn
  have hbn := sharp_defect_bound p n
  have hbs := sharp_defect_bound p start
  dsimp [remaining, budget] at he
  omega

/-- Only finitely many vertices can contribute any incoming or outgoing defect. -/
theorem eventually_zero_local_defects {k : Nat} (p : InfiniteLabeledPopulation k k) :
    ∃ start, ∀ v, start ≤ v → localDefect p v = 0 := by
  obtain ⟨start, hs⟩ := defects_stabilize p
  refine ⟨start, ?_⟩
  intro v hv
  have hnow := hs v hv
  have hnext := hs (v+1) (by omega)
  have hstep := total_defect_succ p v
  omega

/-- A finite support certificate and the bound on the actual total of all defects.
Every later prefix has exactly the same total, because all omitted summands vanish. -/
theorem finite_total_defect {k : Nat} (p : InfiniteLabeledPopulation k k) :
    ∃ start, (∀ v, start ≤ v → localDefect p v = 0) ∧
      totalDefect p start ≤ k * (fullRootCount p - 1) ∧
      ∀ n, start ≤ n → totalDefect p n = totalDefect p start := by
  obtain ⟨start, hz⟩ := eventually_zero_local_defects p
  refine ⟨start, hz, sharp_defect_bound p start, ?_⟩
  intro n hn
  rw [total_defect_eq_sum, total_defect_eq_sum]
  exact sum_eq_support (localDefect p) start n hn hz

/-- Beyond a finite birth prefix, every vertex is a nonroot with exactly k parents
and k children, where both degrees count the full infinite graph. -/
theorem eventually_regular {k : Nat} (p : InfiniteLabeledPopulation k k) :
    ∃ start, ∀ v, start ≤ v →
      p.root v = false ∧ fullInDegree p v = k ∧ fullOutDegree p v = k := by
  obtain ⟨start, hz⟩ := eventually_zero_local_defects p
  refine ⟨start + p.rootSupport, ?_⟩
  intro v hv
  have hr := p.no_roots_after v (by omega)
  have hd := hz v (by omega)
  have hin := full_indegree_lower p v hr
  have hout : fullOutDegree p v ≤ k := p.child_cap v
  simp only [localDefect, hr, Bool.false_eq_true, ↓reduceIte] at hd
  exact ⟨hr, by omega, by omega⟩

/-- Once defects and roots have stabilized, the actual crossing width is constant. -/
theorem eventual_constant_crossing {k : Nat} (p : InfiniteLabeledPopulation k k) :
    ∃ start, ∀ n, start ≤ n → crossingCount p n = crossingCount p start := by
  obtain ⟨s, hs⟩ := defects_stabilize p
  let start := s + p.rootSupport
  refine ⟨start, ?_⟩
  intro n hn
  have hns : s ≤ n := by dsimp [start] at hn; omega
  have hss : s ≤ start := by dsimp [start]; omega
  have hnr : p.rootSupport ≤ n := by dsimp [start] at hn; omega
  have hsr : p.rootSupport ≤ start := by dsimp [start]; omega
  have hdn := hs n hns
  have hds := hs start hss
  have hcn := conservation p n
  have hcs := conservation p start
  rw [roots_stable p n hnr] at hcn
  rw [roots_stable p start hsr] at hcs
  change totalDefect p n + crossingCount p n = k * fullRootCount p at hcn
  change totalDefect p start + crossingCount p start = k * fullRootCount p at hcs
  omega

/-- One common tail has exact full degrees and a fixed crossing width. -/
theorem eventual_structure {k : Nat} (p : InfiniteLabeledPopulation k k) :
    ∃ start, p.rootSupport ≤ start ∧
      (∀ v, start ≤ v → p.root v = false ∧ fullInDegree p v = k ∧ fullOutDegree p v = k) ∧
      (∀ n, start ≤ n → crossingCount p n = crossingCount p start) ∧
      k ≤ crossingCount p start ∧ crossingCount p start ≤ k * fullRootCount p := by
  obtain ⟨regularStart, hr⟩ := eventually_regular p
  obtain ⟨crossStart, hc⟩ := eventual_constant_crossing p
  let start := regularStart + crossStart + p.rootSupport
  have hrs : regularStart ≤ start := by dsimp [start]; omega
  have hcs : crossStart ≤ start := by dsimp [start]; omega
  have hroot : p.rootSupport ≤ start := by dsimp [start]; omega
  refine ⟨start, hroot, ?_, ?_, crossing_lower_after_roots p start hroot, crossing_upper p start⟩
  · intro v hv
    exact hr v (by omega)
  · intro n hn
    have h1 := hc n (by omega)
    have h2 := hc start hcs
    omega

#print axioms sharp_defect_bound
#print axioms defects_stabilize
#print axioms eventually_zero_local_defects
#print axioms finite_total_defect
#print axioms eventually_regular
#print axioms eventual_constant_crossing
#print axioms eventual_structure

/-- Split a finite sum into an initial range and a shifted block. -/
theorem sumBelow_shift (n m : Nat) (f : Nat → Nat) :
    sumBelow (n+m) f = sumBelow n f + sumBelow m (fun i => f (n+i)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.add_succ, sumBelow_succ, ih, sumBelow_succ]
    omega

theorem edgeBit_le_one (e : Option Nat) : edgeBit e ≤ 1 := by
  cases e <;> simp [edgeBit]

/-- Edges entering one target from sources before a selected cut. -/
def incomingFromPrefix {k d : Nat} (p : InfiniteLabeledPopulation k d)
    (n v : Nat) : Nat := sumBelow n (fun u => edgeBit (p.edge u v))

/-- Of the parents of the i-th vertex after a root-free cut, at most i can
belong to that new block. The remaining required parents cross the cut. -/
theorem old_parent_lower {k d : Nat} (p : InfiniteLabeledPopulation k d)
    (n i : Nat) (hn : p.rootSupport ≤ n) : k - i ≤ incomingFromPrefix p n (n+i) := by
  have hl := full_indegree_lower p (n+i) (p.no_roots_after (n+i) (by omega))
  have hs := sumBelow_shift n i (fun u => edgeBit (p.edge u (n+i)))
  change fullInDegree p (n+i) = incomingFromPrefix p n (n+i) +
    sumBelow i (fun j => edgeBit (p.edge (n+j) (n+i))) at hs
  have hi : sumBelow i (fun j => edgeBit (p.edge (n+j) (n+i))) ≤ i := by
    calc
      _ ≤ sumBelow i (fun _ => 1) := sumBelow_mono (fun j _ => edgeBit_le_one _)
      _ = i := by simp
  omega

/-- A finite target block selects only actual crossing edges from one source. -/
theorem target_block_le_crossing_row {k d : Nat} (p : InfiniteLabeledPopulation k d)
    (n u m : Nat) :
    sumBelow m (fun i => edgeBit (p.edge u (n+i))) ≤
      sumBelow (p.childSupport u) (fun v => if n ≤ v then edgeBit (p.edge u v) else 0) := by
  let f := fun v => if n ≤ v then edgeBit (p.edge u v) else 0
  have hz : sumBelow n f = 0 := by
    calc
      _ = sumBelow n (fun _ => 0) := sumBelow_congr (fun v hv => by
        simp [f, show ¬n ≤ v by omega])
      _ = 0 := by simp
  have he : sumBelow m (fun i => f (n+i)) =
      sumBelow m (fun i => edgeBit (p.edge u (n+i))) := by
    apply sumBelow_congr
    intro i _
    simp [f]
  have hs := sumBelow_shift n m f
  rw [hz, he, Nat.zero_add] at hs
  rw [← hs]
  apply sumBelow_le_support f (p.childSupport u) (n+m)
  intro v hv
  simp [f, p.no_children_after u v hv, edgeBit]

/-- Count all required old parents of the first m vertices beyond a root-free cut. -/
theorem crossing_block_lower {k d : Nat} (p : InfiniteLabeledPopulation k d)
    (n m : Nat) (hn : p.rootSupport ≤ n) :
    sumBelow m (fun i => k-i) ≤ crossingCount p n := by
  calc
    _ ≤ sumBelow m (fun i => incomingFromPrefix p n (n+i)) :=
      sumBelow_mono (fun i _ => old_parent_lower p n i hn)
    _ = sumBelow n (fun u => sumBelow m (fun i => edgeBit (p.edge u (n+i)))) :=
      sumBelow_swap m n _
    _ ≤ crossingCount p n :=
      sumBelow_mono (fun u _ => target_block_le_crossing_row p n u m)

def triangular (k : Nat) : Nat := sumBelow k (fun i => k-i)

theorem triangular_succ (k : Nat) : triangular (k+1) = triangular k + (k+1) := by
  change sumBelow (k+1) (fun i => k+1-i) = sumBelow k (fun i => k-i) + (k+1)
  rw [sumBelow_succ]
  have he : sumBelow k (fun i => k+1-i) = sumBelow k (fun i => (k-i)+1) :=
    sumBelow_congr (fun i hi => by omega)
  rw [he, sumBelow_add, sumBelow_const]
  change sumBelow k (fun i => k-i) + 1*k + (k+1-k) =
    sumBelow k (fun i => k-i) + (k+1)
  omega

theorem twice_triangular (k : Nat) : 2 * triangular k = k * (k+1) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [triangular_succ, Nat.mul_add, ih]
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]
    omega

/-- Stronger universal root-free cut bound, independent of the offspring cap. -/
theorem crossing_triangular_lower {k d : Nat} (p : InfiniteLabeledPopulation k d)
    (n : Nat) (hn : p.rootSupport ≤ n) : k * (k+1) / 2 ≤ crossingCount p n := by
  have h := crossing_block_lower p n k hn
  change triangular k ≤ crossingCount p n at h
  have he : k * (k+1) / 2 = triangular k := by rw [← twice_triangular]; omega
  rw [he]
  exact h

/-- The triangular cut bound improves the critical full-defect budget. -/
theorem triangular_defect_bound_after_roots {k : Nat} (p : InfiniteLabeledPopulation k k)
    (n : Nat) (hn : p.rootSupport ≤ n) :
    totalDefect p n ≤ k * fullRootCount p - k * (k+1) / 2 := by
  have hc := conservation p n
  rw [roots_stable p n hn] at hc
  have hl := crossing_triangular_lower p n hn
  unfold totalDefect
  omega

/-- The stronger budget bounds every prefix and hence the entire finite defect set. -/
theorem triangular_defect_bound {k : Nat} (p : InfiniteLabeledPopulation k k) (n : Nat) :
    totalDefect p n ≤ k * fullRootCount p - k * (k+1) / 2 := by
  exact Nat.le_trans (total_defect_mono p n (n + p.rootSupport) (by omega))
    (triangular_defect_bound_after_roots p (n + p.rootSupport) (by omega))

theorem binary_crossing_lower {d : Nat} (p : InfiniteLabeledPopulation 2 d)
    (n : Nat) (hn : p.rootSupport ≤ n) : 3 ≤ crossingCount p n := by
  simpa using crossing_triangular_lower p n hn

theorem binary_defect_bound (p : InfiniteLabeledPopulation 2 2) (n : Nat) :
    totalDefect p n ≤ 2 * fullRootCount p - 3 := by
  simpa using triangular_defect_bound p n

/-- A certificate that the actual full defect total obeys the stronger budget. -/
theorem finite_total_defect_triangular {k : Nat} (p : InfiniteLabeledPopulation k k) :
    ∃ start, (∀ v, start ≤ v → localDefect p v = 0) ∧
      totalDefect p start ≤ k * fullRootCount p - k * (k+1) / 2 ∧
      ∀ n, start ≤ n → totalDefect p n = totalDefect p start := by
  obtain ⟨start, hz, _, hs⟩ := finite_total_defect p
  exact ⟨start, hz, triangular_defect_bound p start, hs⟩

#print axioms old_parent_lower
#print axioms crossing_block_lower
#print axioms crossing_triangular_lower
#print axioms triangular_defect_bound
#print axioms binary_crossing_lower
#print axioms binary_defect_bound
#print axioms finite_total_defect_triangular

end InfiniteConservation
