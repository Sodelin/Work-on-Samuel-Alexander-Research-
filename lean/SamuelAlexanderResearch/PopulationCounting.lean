import Std

/-!
Population counting from a simple directed edge relation. Finite graphs use
natural-number vertices below their bound; the infinite model uses all of Nat
already enumerated in birth order. No total-edge inequality is a hypothesis
of a population theorem in this module.
-/

namespace PopulationCounting

/-- Sum a natural-valued function over `0, ..., n - 1`. -/
def sumBelow : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => sumBelow n f + f n

@[simp] theorem sumBelow_zero (f : Nat → Nat) : sumBelow 0 f = 0 := rfl
@[simp] theorem sumBelow_succ (n : Nat) (f : Nat → Nat) :
    sumBelow (n + 1) f = sumBelow n f + f n := rfl

@[simp] theorem sumBelow_const (n c : Nat) : sumBelow n (fun _ => c) = c * n := by
  induction n with
  | zero => simp [sumBelow]
  | succ n ih => simp [sumBelow, ih, Nat.mul_succ]

theorem sumBelow_congr {n : Nat} {f g : Nat → Nat}
    (h : ∀ i, i < n → f i = g i) : sumBelow n f = sumBelow n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sumBelow_succ, sumBelow_succ, ih (fun i hi => h i (by omega)), h n (by omega)]

theorem sumBelow_add (n : Nat) (f g : Nat → Nat) :
    sumBelow n (fun i => f i + g i) = sumBelow n f + sumBelow n g := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sumBelow_succ, ih]; omega

theorem sumBelow_mul (n c : Nat) (f : Nat → Nat) :
    sumBelow n (fun i => c * f i) = c * sumBelow n f := by
  induction n with
  | zero => simp [sumBelow]
  | succ n ih => simp [sumBelow, ih, Nat.mul_add]

theorem sumBelow_mono {n : Nat} {f g : Nat → Nat}
    (h : ∀ i, i < n → f i ≤ g i) : sumBelow n f ≤ sumBelow n g := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    exact Nat.add_le_add (ih (fun i hi => h i (by omega))) (h n (by omega))

theorem term_le_sumBelow {n i : Nat} (f : Nat → Nat) (hi : i < n) :
    f i ≤ sumBelow n f := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases h : i < n
    · have := ih h; simp only [sumBelow_succ]; omega
    · have : i = n := by omega
      subst i
      simp only [sumBelow_succ]
      omega

/-- Finite double counting, proved without a finite-set library. -/
theorem sumBelow_swap (n m : Nat) (f : Nat → Nat → Nat) :
    sumBelow n (fun i => sumBelow m (f i)) =
      sumBelow m (fun j => sumBelow n (fun i => f i j)) := by
  induction n with
  | zero => simp [sumBelow]
  | succ n ih =>
    simp only [sumBelow_succ, ih]
    exact (sumBelow_add m (fun j => sumBelow n (fun i => f i j)) (f n)).symm

/-- A singleton contributes exactly one when its index is in range. -/
theorem sumBelow_singleton (n a : Nat) :
    sumBelow n (fun i => if a = i then 1 else 0) = if a < n then 1 else 0 := by
  induction n with
  | zero => simp [sumBelow]
  | succ n ih =>
    simp only [sumBelow_succ, ih]
    split <;> split <;> split <;> omega

/-- Every ordered pair has at most one edge, carrying one natural-number label. -/
structure LabeledGraph (n : Nat) where
  edge : Nat → Nat → Option Nat
  no_self : ∀ v, v < n → edge v v = none

/-- The Boolean adjacency indicator underlying all degree counts. -/
def edgeBit (e : Option Nat) : Nat := if e.isSome then 1 else 0

def inDegree {n : Nat} (g : LabeledGraph n) (v : Nat) : Nat :=
  sumBelow n (fun u => edgeBit (g.edge u v))

def outDegree {n : Nat} (g : LabeledGraph n) (u : Nat) : Nat :=
  sumBelow n (fun v => edgeBit (g.edge u v))

def edgeCount {n : Nat} (g : LabeledGraph n) : Nat :=
  sumBelow n (outDegree g)

/-- Both sums count the very same actual adjacency entries. -/
theorem double_count {n : Nat} (g : LabeledGraph n) :
    sumBelow n (inDegree g) = edgeCount g := by
  exact sumBelow_swap n n (fun v u => edgeBit (g.edge u v))

/-- Declared roots have no parents; every other vertex has every required label.
The cap is a bound on the actual number of distinct outgoing neighbors. -/
structure LabeledPopulation (n k d : Nat) extends LabeledGraph n where
  root : Nat → Bool
  root_no_parents : ∀ v, v < n → root v = true →
    ∀ u, u < n → edge u v = none
  parent_of_label : ∀ v, v < n → root v = false →
    ∀ l, l < k → ∃ u, u < n ∧ edge u v = some l
  child_cap : ∀ u, u < n → outDegree toLabeledGraph u ≤ d

def rootCount {n k d : Nat} (p : LabeledPopulation n k d) : Nat :=
  sumBelow n (fun v => if p.root v then 1 else 0)

def nonrootCount {n k d : Nat} (p : LabeledPopulation n k d) : Nat :=
  sumBelow n (fun v => if p.root v then 0 else 1)

theorem root_partition {n k d : Nat} (p : LabeledPopulation n k d) :
    rootCount p + nonrootCount p = n := by
  rw [rootCount, nonrootCount, ← sumBelow_add]
  calc
    _ = sumBelow n (fun _ => 1) := sumBelow_congr (fun i _ => by cases p.root i <;> rfl)
    _ = n := by simp

/-- Label uniqueness belongs to the edge representation, not an extra count premise. -/
theorem label_indicators_le_edge (k : Nat) (e : Option Nat) :
    sumBelow k (fun l => if e = some l then 1 else 0) ≤ edgeBit e := by
  cases e with
  | none => simp [edgeBit]
  | some a =>
    simp only [Option.some.injEq]
    rw [sumBelow_singleton]
    simp [edgeBit]
    split <;> omega

/-- Every required label gives a distinct incoming edge because an edge has one label. -/
theorem nonroot_indegree {n k d : Nat} (p : LabeledPopulation n k d)
    (v : Nat) (hv : v < n) (hr : p.root v = false) :
    k ≤ inDegree p.toLabeledGraph v := by
  have labels : ∀ l, l < k →
      1 ≤ sumBelow n (fun u => if p.edge u v = some l then 1 else 0) := by
    intro l hl
    obtain ⟨u, hu, he⟩ := p.parent_of_label v hv hr l hl
    have h := term_le_sumBelow (fun u => if p.edge u v = some l then 1 else 0) hu
    simpa [he] using h
  calc
    k = sumBelow k (fun _ => 1) := by simp
    _ ≤ sumBelow k (fun l => sumBelow n (fun u => if p.edge u v = some l then 1 else 0)) :=
      sumBelow_mono labels
    _ = sumBelow n (fun u => sumBelow k (fun l => if p.edge u v = some l then 1 else 0)) :=
      sumBelow_swap k n _
    _ ≤ inDegree p.toLabeledGraph v :=
      sumBelow_mono (fun u _ => label_indicators_le_edge k (p.edge u v))

/-- The lower and upper edge estimates are derived from local graph hypotheses. -/
theorem edge_bounds {n k d : Nat} (p : LabeledPopulation n k d) :
    k * (n - rootCount p) ≤ edgeCount p.toLabeledGraph ∧
      edgeCount p.toLabeledGraph ≤ d * n := by
  have partition := root_partition p
  have hnon : nonrootCount p = n - rootCount p := by omega
  constructor
  · rw [← hnon, nonrootCount, ← sumBelow_mul, ← double_count]
    apply sumBelow_mono
    intro v hv
    cases hr : p.root v with
    | false => simpa [hr] using nonroot_indegree p v hv hr
    | true => simp
  · calc
      edgeCount p.toLabeledGraph ≤ sumBelow n (fun _ => d) := sumBelow_mono p.child_cap
      _ = d * n := sumBelow_const n d

/-- End-to-end finite offspring inequality, with no aggregate-edge premise. -/
theorem offspring_edge_bound {n k d : Nat} (p : LabeledPopulation n k d) :
    k * (n - rootCount p) ≤ d * n := Nat.le_trans (edge_bounds p).1 (edge_bounds p).2

/-- End-to-end finite offspring threshold, including the trivial `k ≤ d` case. -/
theorem offspring_threshold {n k d : Nat} (p : LabeledPopulation n k d) :
    (k - d) * n ≤ k * rootCount p := by
  have hr : rootCount p ≤ n := by have := root_partition p; omega
  have he := offspring_edge_bound p
  by_cases hdk : d ≤ k
  · have hk : k = d + (k - d) := by omega
    have hn : n = (n - rootCount p) + rootCount p := by omega
    have hc : k * n = k * (n - rootCount p) + k * rootCount p := by
      calc
        k * n = k * ((n - rootCount p) + rootCount p) := congrArg (fun x => k * x) hn
        _ = _ := Nat.mul_add _ _ _
    have hs : k * n = d * n + (k - d) * n := by
      calc
        k * n = (d + (k - d)) * n := congrArg (fun x => x * n) hk
        _ = _ := Nat.add_mul _ _ _
    omega
  · have hz : k - d = 0 := by omega
    simp [hz]

/-- In particular, a strict cap bounds the number of vertices by `kR/(k-d)`. -/
theorem strict_offspring_size_bound {n k d : Nat} (p : LabeledPopulation n k d)
    (hdk : d < k) : n ≤ (k * rootCount p) / (k - d) := by
  apply (Nat.le_div_iff_mul_le (by omega : 0 < k - d)).2
  simpa [Nat.mul_comm] using offspring_threshold p

#print axioms double_count
#print axioms nonroot_indegree
#print axioms offspring_edge_bound
#print axioms offspring_threshold
#print axioms strict_offspring_size_bound

/-- Fixed source genders are vertex attributes, so one vertex cannot supply both
colors merely by using differently labelled outgoing edges. -/
structure GenderedPopulation (n : Nat) extends LabeledGraph n where
  root : Nat → Bool
  gender : Nat → Bool
  root_no_parents : ∀ v, v < n → root v = true →
    ∀ u, u < n → edge u v = none
  parent_of_gender : ∀ v, v < n → root v = false →
    ∀ c : Bool, ∃ u, u < n ∧ gender u = c ∧ (edge u v).isSome = true
  child_cap : ∀ u, u < n → outDegree toLabeledGraph u ≤ 2

def genderRootCount {n : Nat} (p : GenderedPopulation n) : Nat :=
  sumBelow n (fun v => if p.root v then 1 else 0)

def genderCount {n : Nat} (p : GenderedPopulation n) (c : Bool) : Nat :=
  sumBelow n (fun u => if p.gender u = c then 1 else 0)

def genderInDegree {n : Nat} (p : GenderedPopulation n) (c : Bool) (v : Nat) : Nat :=
  sumBelow n (fun u => if p.gender u = c then edgeBit (p.edge u v) else 0)

theorem gender_partition {n : Nat} (p : GenderedPopulation n) :
    genderCount p true + genderCount p false = n := by
  rw [genderCount, genderCount, ← sumBelow_add]
  calc
    _ = sumBelow n (fun _ => 1) := sumBelow_congr (fun u _ => by cases p.gender u <;> rfl)
    _ = n := by simp

theorem gender_root_partition {n : Nat} (p : GenderedPopulation n) :
    genderRootCount p + sumBelow n (fun v => if p.root v then 0 else 1) = n := by
  rw [genderRootCount, ← sumBelow_add]
  calc
    _ = sumBelow n (fun _ => 1) := sumBelow_congr (fun v _ => by cases p.root v <;> rfl)
    _ = n := by simp

theorem nonroot_gender_indegree {n : Nat} (p : GenderedPopulation n)
    (v : Nat) (hv : v < n) (hr : p.root v = false) (c : Bool) :
    1 ≤ genderInDegree p c v := by
  obtain ⟨u, hu, hc, he⟩ := p.parent_of_gender v hv hr c
  have h := term_le_sumBelow
    (fun u => if p.gender u = c then edgeBit (p.edge u v) else 0) hu
  simpa [edgeBit, hc, he, genderInDegree] using h

/-- Double-count only the edges whose source has a chosen permanent gender. -/
theorem gender_double_count {n : Nat} (p : GenderedPopulation n) (c : Bool) :
    sumBelow n (genderInDegree p c) =
      sumBelow n (fun u => if p.gender u = c then outDegree p.toLabeledGraph u else 0) := by
  change sumBelow n (fun v => sumBelow n (fun u => if p.gender u = c then edgeBit (p.edge u v) else 0)) = _
  rw [sumBelow_swap]
  apply sumBelow_congr
  intro u _
  by_cases h : p.gender u = c <;> simp [h, outDegree]

/-- Each color supplies enough actual edges, and each vertex supplies at most two. -/
theorem gender_edge_bound {n : Nat} (p : GenderedPopulation n) (c : Bool) :
    n - genderRootCount p ≤ 2 * genderCount p c := by
  have hp := gender_root_partition p
  have hn : n - genderRootCount p = sumBelow n (fun v => if p.root v then 0 else 1) := by
    omega
  calc
    n - genderRootCount p = sumBelow n (fun v => if p.root v then 0 else 1) := hn
    _ ≤ sumBelow n (genderInDegree p c) := by
      apply sumBelow_mono
      intro v hv
      cases hr : p.root v with
      | false => exact nonroot_gender_indegree p v hv hr c
      | true => exact Nat.zero_le _
    _ = sumBelow n (fun u => if p.gender u = c then outDegree p.toLabeledGraph u else 0) :=
      gender_double_count p c
    _ ≤ sumBelow n (fun u => 2 * (if p.gender u = c then 1 else 0)) := by
      apply sumBelow_mono
      intro u hu
      by_cases h : p.gender u = c
      · simpa [h] using p.child_cap u hu
      · simp [h]
    _ = 2 * genderCount p c := sumBelow_mul n 2 _

/-- The two one-sided inequalities express `|M-F| ≤ R` over natural counts. -/
theorem binary_vertex_gender_balance {n : Nat} (p : GenderedPopulation n) :
    genderCount p true ≤ genderCount p false + genderRootCount p ∧
      genderCount p false ≤ genderCount p true + genderRootCount p := by
  have hp := gender_partition p
  have hr := gender_root_partition p
  have hm := gender_edge_bound p true
  have hf := gender_edge_bound p false
  omega

/-- The same discrepancy bound with an explicit absolute value. -/
theorem binary_vertex_gender_abs_balance {n : Nat} (p : GenderedPopulation n) :
    Int.natAbs ((genderCount p true : Int) - (genderCount p false : Int)) ≤
      genderRootCount p := by
  have h := binary_vertex_gender_balance p
  omega

#print axioms gender_double_count
#print axioms gender_edge_bound
#print axioms binary_vertex_gender_balance
#print axioms binary_vertex_gender_abs_balance

/-- Extending the vertex range can only add nonnegative summands. -/
theorem sumBelow_range_mono {n m : Nat} (hn : n ≤ m) (f : Nat → Nat) :
    sumBelow n f ≤ sumBelow m f := by
  induction m with
  | zero =>
    have : n = 0 := by omega
    subst n
    exact Nat.le_refl _
  | succ m ih =>
    by_cases h : n ≤ m
    · have := ih h; simp only [sumBelow_succ]; omega
    · have : n = m + 1 := by omega
      subst n
      exact Nat.le_refl _

/-- Summing a prefix indicator inside a larger range gives the prefix sum. -/
theorem sumBelow_truncate {n m : Nat} (hn : n ≤ m) (f : Nat → Nat) :
    sumBelow m (fun i => if i < n then f i else 0) = sumBelow n f := by
  induction m with
  | zero =>
    have : n = 0 := by omega
    subst n
    rfl
  | succ m ih =>
    by_cases h : n ≤ m
    · rw [sumBelow_succ, ih h]
      simp [show ¬m < n by omega]
    · have he : n = m + 1 := by omega
      subst n
      apply sumBelow_congr
      intro i hi
      simp [hi]

/-- Split all adjacency entries into targets inside and outside the prefix. -/
theorem sumBelow_cut {n m : Nat} (hn : n ≤ m) (f : Nat → Nat) :
    sumBelow m f = sumBelow n f + sumBelow m (fun i => if n ≤ i then f i else 0) := by
  rw [← sumBelow_truncate hn f, ← sumBelow_add]
  apply sumBelow_congr
  intro i _
  by_cases h : i < n
  · simp [h, show ¬n ≤ i by omega]
  · simp [h, show n ≤ i by omega]

/-- Explicit predecessor closure of the first `n` vertices in an ambient graph. -/
def PredecessorClosed {m : Nat} (g : LabeledGraph m) (n : Nat) : Prop :=
  ∀ u, u < m → ∀ v, v < n → (g.edge u v).isSome = true → u < n

/-- Strict growth in a chosen birth index is a sufficient closure hypothesis. -/
theorem ordered_prefix_closed {m : Nat} (g : LabeledGraph m)
    (horder : ∀ u, u < m → ∀ v, v < m → (g.edge u v).isSome = true → u < v)
    {n : Nat} (hn : n ≤ m) : PredecessorClosed g n := by
  intro u hu v hv he
  have := horder u hu v (by omega) he
  omega

def restrictGraph {m : Nat} (g : LabeledGraph m) (n : Nat) (hn : n ≤ m) : LabeledGraph n where
  edge := g.edge
  no_self := fun v hv => g.no_self v (by omega)

/-- A closed prefix inherits label coverage and the actual outgoing degree cap. -/
def restrictPopulation {m k d : Nat} (p : LabeledPopulation m k d)
    (n : Nat) (hn : n ≤ m) (hc : PredecessorClosed p.toLabeledGraph n) :
    LabeledPopulation n k d where
  toLabeledGraph := restrictGraph p.toLabeledGraph n hn
  root := p.root
  root_no_parents := fun v hv hr u hu => p.root_no_parents v (by omega) hr u (by omega)
  parent_of_label := by
    intro v hv hr l hl
    obtain ⟨u, hu, he⟩ := p.parent_of_label v (by omega) hr l hl
    exact ⟨u, hc u hu v hv (by simp [he]), he⟩
  child_cap := by
    intro u hu
    exact Nat.le_trans (sumBelow_range_mono hn _) (p.child_cap u (by omega))

/-- The graph-count conclusion for an explicit predecessor-closed ambient prefix. -/
theorem prefix_offspring_threshold {m k d : Nat} (p : LabeledPopulation m k d)
    (n : Nat) (hn : n ≤ m) (hc : PredecessorClosed p.toLabeledGraph n) :
    (k - d) * n ≤ k * sumBelow n (fun v => if p.root v then 1 else 0) :=
  offspring_threshold (restrictPopulation p n hn hc)

/-- Finite graph counts also rule out a uniformly root-bounded family of every size.
Constructing that family from real birthdates is a separate, unformalized bridge. -/
theorem no_unbounded_finite_prefixes (k d r : Nat) (hdk : d < k)
    (hprefix : ∀ n, ∃ p : LabeledPopulation n k d, rootCount p ≤ r) : False := by
  obtain ⟨p, hr⟩ := hprefix (k * r + 1)
  have hb := offspring_threshold p
  have hl : k * r + 1 ≤ (k - d) * (k * r + 1) := by
    calc
      k * r + 1 = 1 * (k * r + 1) := by simp
      _ ≤ (k - d) * (k * r + 1) := Nat.mul_le_mul_right _ (by omega)
  have hk : k * rootCount p ≤ k * r := Nat.mul_le_mul_left k hr
  omega

/-- Closed prefixes have no nonzero incoming contribution from outside. -/
theorem incoming_prefix_degree {m : Nat} (g : LabeledGraph m)
    (n : Nat) (hn : n ≤ m) (hc : PredecessorClosed g n)
    (v : Nat) (hv : v < n) :
    inDegree g v = inDegree (restrictGraph g n hn) v := by
  change sumBelow m (fun u => edgeBit (g.edge u v)) = sumBelow n (fun u => edgeBit (g.edge u v))
  rw [← sumBelow_truncate hn (fun u => edgeBit (g.edge u v))]
  apply sumBelow_congr
  intro u hu
  by_cases h : u < n
  · simp [h]
  · have he : g.edge u v = none := by
      cases he : g.edge u v with
      | none => rfl
      | some l => have := hc u hu v hv (by simp [he]); omega
    simp [h, he, edgeBit]

/-- Outgoing crossing edges are counted from the actual ambient adjacency relation. -/
def crossingCount {m : Nat} (g : LabeledGraph m) (n : Nat) : Nat :=
  sumBelow n (fun u => sumBelow m (fun v => if n ≤ v then edgeBit (g.edge u v) else 0))

/-- Full outgoing degrees equal internal edges plus outgoing crossing edges. -/
theorem outgoing_prefix_split {m : Nat} (g : LabeledGraph m)
    (n : Nat) (hn : n ≤ m) :
    sumBelow n (outDegree g) = edgeCount (restrictGraph g n hn) + crossingCount g n := by
  change sumBelow n (fun u => sumBelow m (fun v => edgeBit (g.edge u v))) = _
  calc
    _ = sumBelow n (fun u => sumBelow n (fun v => edgeBit (g.edge u v)) +
          sumBelow m (fun v => if n ≤ v then edgeBit (g.edge u v) else 0)) :=
      sumBelow_congr (fun u _ => sumBelow_cut hn _)
    _ = _ := sumBelow_add n _ _

/-- Outgoing deficit uses full ambient degrees, never degrees truncated at the cut. -/
def outgoingDeficit {m k : Nat} (p : LabeledPopulation m k k) (n : Nat) : Nat :=
  sumBelow n (fun u => k - outDegree p.toLabeledGraph u)

/-- Incoming excess likewise uses full ambient degrees and excludes roots. -/
def incomingExcess {m k : Nat} (p : LabeledPopulation m k k) (n : Nat) : Nat :=
  sumBelow n (fun v => if p.root v then 0 else inDegree p.toLabeledGraph v - k)

theorem root_indegree_zero {m k d : Nat} (p : LabeledPopulation m k d)
    (v : Nat) (hv : v < m) (hr : p.root v = true) : inDegree p.toLabeledGraph v = 0 := by
  change sumBelow m (fun u => edgeBit (p.edge u v)) = 0
  calc
    _ = sumBelow m (fun _ => 0) := sumBelow_congr (fun u hu => by
      simp [p.root_no_parents v hv hr u hu, edgeBit])
    _ = 0 := by simp

theorem outgoing_deficit_sum {m k : Nat} (p : LabeledPopulation m k k)
    (n : Nat) (hn : n ≤ m) :
    outgoingDeficit p n + sumBelow n (outDegree p.toLabeledGraph) = k * n := by
  rw [outgoingDeficit, ← sumBelow_add]
  calc
    _ = sumBelow n (fun _ => k) := sumBelow_congr (fun u hu =>
      Nat.sub_add_cancel (p.child_cap u (by omega)))
    _ = k * n := sumBelow_const n k

theorem incoming_excess_sum {m k : Nat} (p : LabeledPopulation m k k)
    (n : Nat) (hn : n ≤ m) :
    sumBelow n (inDegree p.toLabeledGraph) =
      k * sumBelow n (fun v => if p.root v then 0 else 1) + incomingExcess p n := by
  rw [← sumBelow_mul, incomingExcess, ← sumBelow_add]
  apply sumBelow_congr
  intro v hv
  cases hr : p.root v with
  | true => simp [root_indegree_zero p v (by omega) hr]
  | false =>
    have h := nonroot_indegree p v (by omega) hr
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.mul_one]
    omega

/-- Critical-degree conservation in a finite ambient graph and a predecessor-closed
prefix. All three quantities are actual degree/edge counts from that ambient graph. -/
theorem critical_degree_conservation {m k : Nat} (p : LabeledPopulation m k k)
    (n : Nat) (hn : n ≤ m) (hc : PredecessorClosed p.toLabeledGraph n) :
    outgoingDeficit p n + incomingExcess p n + crossingCount p.toLabeledGraph n =
      k * sumBelow n (fun v => if p.root v then 1 else 0) := by
  have ho := outgoing_deficit_sum p n hn
  have hi := incoming_excess_sum p n hn
  have hs := outgoing_prefix_split p.toLabeledGraph n hn
  have he : sumBelow n (inDegree p.toLabeledGraph) =
      edgeCount (restrictGraph p.toLabeledGraph n hn) := by
    calc
      _ = sumBelow n (inDegree (restrictGraph p.toLabeledGraph n hn)) :=
        sumBelow_congr (fun v hv => incoming_prefix_degree p.toLabeledGraph n hn hc v hv)
      _ = _ := double_count _
  have hp := root_partition (restrictPopulation p n hn hc)
  change sumBelow n (fun v => if p.root v then 1 else 0) +
    sumBelow n (fun v => if p.root v then 0 else 1) = n at hp
  have hk : k * sumBelow n (fun v => if p.root v then 1 else 0) +
      k * sumBelow n (fun v => if p.root v then 0 else 1) = k * n := by
    rw [← Nat.mul_add, hp]
  omega

#print axioms ordered_prefix_closed
#print axioms prefix_offspring_threshold
#print axioms no_unbounded_finite_prefixes
#print axioms incoming_prefix_degree
#print axioms outgoing_prefix_split
#print axioms critical_degree_conservation

/-- Restriction preserves the permanent gender of every source vertex. -/
def restrictGenderedPopulation {m : Nat} (p : GenderedPopulation m)
    (n : Nat) (hn : n ≤ m) (hc : PredecessorClosed p.toLabeledGraph n) :
    GenderedPopulation n where
  toLabeledGraph := restrictGraph p.toLabeledGraph n hn
  root := p.root
  gender := p.gender
  root_no_parents := fun v hv hr u hu => p.root_no_parents v (by omega) hr u (by omega)
  parent_of_gender := by
    intro v hv hr c
    obtain ⟨u, hu, hg, he⟩ := p.parent_of_gender v (by omega) hr c
    exact ⟨u, hc u hu v hv he, hg, he⟩
  child_cap := by
    intro u hu
    exact Nat.le_trans (sumBelow_range_mono hn _) (p.child_cap u (by omega))

/-- Absolute source-gender discrepancy in an explicit predecessor-closed prefix. -/
theorem prefix_binary_gender_balance {m : Nat} (p : GenderedPopulation m)
    (n : Nat) (hn : n ≤ m) (hc : PredecessorClosed p.toLabeledGraph n) :
    Int.natAbs ((sumBelow n (fun u => if p.gender u = true then 1 else 0) : Int) -
      (sumBelow n (fun u => if p.gender u = false then 1 else 0) : Int)) ≤
      sumBelow n (fun v => if p.root v then 1 else 0) :=
  binary_vertex_gender_abs_balance (restrictGenderedPopulation p n hn hc)

/-- Every finite closed cut has bounded total degree defects and crossing width. -/
theorem critical_degree_budget {m k : Nat} (p : LabeledPopulation m k k)
    (n : Nat) (hn : n ≤ m) (hc : PredecessorClosed p.toLabeledGraph n) :
    outgoingDeficit p n + incomingExcess p n ≤
        k * sumBelow n (fun v => if p.root v then 1 else 0) ∧
      crossingCount p.toLabeledGraph n ≤
        k * sumBelow n (fun v => if p.root v then 1 else 0) := by
  have h := critical_degree_conservation p n hn hc
  omega

#print axioms prefix_binary_gender_balance
#print axioms critical_degree_budget

/-- A finite support bound certifies that a local sum is the full neighbor count. -/
theorem sumBelow_le_support (f : Nat → Nat) (b n : Nat)
    (hz : ∀ i, b ≤ i → f i = 0) : sumBelow n f ≤ sumBelow b f := by
  by_cases h : n ≤ b
  · exact sumBelow_range_mono h f
  · have hb : b ≤ n := by omega
    have he : sumBelow n f = sumBelow b f := by
      rw [← sumBelow_truncate hb f]
      apply sumBelow_congr
      intro i _
      by_cases hi : i < b
      · simp [hi]
      · simp [hi, hz i (by omega)]
    exact Nat.le_of_eq he

/-- An actually infinite population, already enumerated in strict birth order.
`childSupport u` bounds every child of `u`, so the degree cap concerns the full
outgoing edge set. `rootSupport` similarly bounds every root. No aggregate edge
estimate or family of finite prefixes is supplied as a field. -/
structure InfiniteLabeledPopulation (k d : Nat) where
  edge : Nat → Nat → Option Nat
  root : Nat → Bool
  birth_order : ∀ u v, (edge u v).isSome = true → u < v
  root_no_parents : ∀ v, root v = true → ∀ u, edge u v = none
  parent_of_label : ∀ v, root v = false → ∀ l, l < k → ∃ u, edge u v = some l
  childSupport : Nat → Nat
  no_children_after : ∀ u v, childSupport u ≤ v → edge u v = none
  child_cap : ∀ u, sumBelow (childSupport u) (fun v => edgeBit (edge u v)) ≤ d
  rootSupport : Nat
  no_roots_after : ∀ v, rootSupport ≤ v → root v = false

/-- A full outgoing degree, justified by `no_children_after`. -/
def fullOutDegree {k d : Nat} (p : InfiniteLabeledPopulation k d) (u : Nat) : Nat :=
  sumBelow (p.childSupport u) (fun v => edgeBit (p.edge u v))

/-- The full finite root count of the infinite graph. -/
def fullRootCount {k d : Nat} (p : InfiniteLabeledPopulation k d) : Nat :=
  sumBelow p.rootSupport (fun v => if p.root v then 1 else 0)

/-- A finite prefix is constructed from the one infinite adjacency relation. -/
def infinitePrefix {k d : Nat} (p : InfiniteLabeledPopulation k d) (n : Nat) :
    LabeledPopulation n k d where
  edge := p.edge
  no_self := by
    intro v _
    cases he : p.edge v v with
    | none => rfl
    | some l => have := p.birth_order v v (by simp [he]); omega
  root := p.root
  root_no_parents := fun v _ hr u _ => p.root_no_parents v hr u
  parent_of_label := by
    intro v hv hr l hl
    obtain ⟨u, he⟩ := p.parent_of_label v hr l hl
    have hu := p.birth_order u v (by simp [he])
    exact ⟨u, by omega, he⟩
  child_cap := by
    intro u _
    apply Nat.le_trans (sumBelow_le_support (fun v => edgeBit (p.edge u v)) (p.childSupport u) n _)
      (p.child_cap u)
    intro v hv
    simp [p.no_children_after u v hv, edgeBit]

theorem infinite_prefix_root_bound {k d : Nat} (p : InfiniteLabeledPopulation k d)
    (n : Nat) : rootCount (infinitePrefix p n) ≤ fullRootCount p := by
  apply sumBelow_le_support (fun v => if p.root v then 1 else 0) p.rootSupport n
  intro v hv
  simp [p.no_roots_after v hv]

/-- The subcritical infinite impossibility theorem for a naturally birth-ordered
population with finitely supported, fully counted children and finitely many roots. -/
theorem infinite_subcritical_impossible {k d : Nat} (p : InfiniteLabeledPopulation k d)
    (hdk : d < k) : False := by
  apply no_unbounded_finite_prefixes k d (fullRootCount p) hdk
  intro n
  exact ⟨infinitePrefix p n, infinite_prefix_root_bound p n⟩

/-- A type-level form of the same end-to-end infinite theorem. -/
theorem no_infinite_subcritical_population (k d : Nat) (hdk : d < k) :
    ¬Nonempty (InfiniteLabeledPopulation k d) := by
  intro ⟨p⟩
  exact infinite_subcritical_impossible p hdk

#print axioms infinite_prefix_root_bound
#print axioms infinite_subcritical_impossible
#print axioms no_infinite_subcritical_population

end PopulationCounting
