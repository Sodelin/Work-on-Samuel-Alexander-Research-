import SamuelAlexanderResearch.BinaryPopulation

/-!
Alexander's positive unavoidability theorem for the actual binary natural-date
population model. Source: arXiv:1212.0186v2, Section 2, Proposition 5 and Theorem 6.
The finite-branching compactness argument is proved internally; no positive
unavoidability or compactness theorem is an endpoint premise.
-/

namespace PositiveUnavoidability

open SpeciesBridge BinaryPopulation BinaryAvoidance

inductive FinitePath (E : LabelledGraph) (s : Nat → Bool) :
    Nat → Nat → Nat → Nat → Prop where
  | nil (k v : Nat) : FinitePath E s k 0 v v
  | cons {k n u v w : Nat} : E u v (s k) →
      FinitePath E s (k + 1) n v w → FinitePath E s k (n + 1) u w

theorem FinitePath.append {E : LabelledGraph} {s : Nat → Bool}
    {k n u v : Nat} (first : FinitePath E s k n u v)
    {m w : Nat} (second : FinitePath E s (k + n) m v w) :
    FinitePath E s k (n + m) u w := by
  induction first with
  | nil => simpa using second
  | @cons k n u v z he hp ih =>
    have hs : FinitePath E s ((k + 1) + n) m z w := by
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using second
    have ht := FinitePath.cons he (ih hs)
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ht

theorem FinitePath.snoc {E : LabelledGraph} {s : Nat → Bool}
    {k n u v w : Nat} (path : FinitePath E s k n u v)
    (edge : E v w (s (k + n))) : FinitePath E s k (n + 1) u w := by
  exact path.append (.cons edge (.nil _ _))

theorem FinitePath.le_end {E : LabelledGraph} {s : Nat → Bool}
    (strict : ∀ u v b, E u v b → u < v)
    {k n u v : Nat} (path : FinitePath E s k n u v) : u ≤ v := by
  induction path with
  | nil => exact Nat.le_refl _
  | cons edge _ ih => have := strict _ _ _ edge; omega

theorem FinitePath.lt_end {E : LabelledGraph} {s : Nat → Bool}
    (strict : ∀ u v b, E u v b → u < v)
    {k n u v : Nat} (path : FinitePath E s k n u v) (hn : 0 < n) : u < v := by
  cases path with
  | nil => omega
  | cons edge tail =>
    have := strict _ _ _ edge
    have := tail.le_end strict
    omega

theorem FinitePath.shift {E : LabelledGraph} {s : Nat → Bool} {d : Nat}
    (period : ∀ k, s (k + d) = s k)
    {k n u v : Nat} (path : FinitePath E s k n u v) :
    FinitePath E s (k + d) n u v := by
  induction path with
  | nil => exact .nil _ _
  | @cons k n u v w edge tail ih =>
    apply FinitePath.cons
    · simpa only [period] using edge
    · simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih

theorem finite_union_bound (P : Nat → Nat → Prop) (n : Nat)
    (bounded : ∀ i, i < n → ∃ b, ∀ w, P i w → w < b) :
    ∃ b, ∀ i, i < n → ∀ w, P i w → w < b := by
  induction n with
  | zero => exact ⟨0, fun _ hi => False.elim (by omega)⟩
  | succ n ih =>
    obtain ⟨a, ha⟩ := ih (fun i hi => bounded i (by omega))
    obtain ⟨b, hb⟩ := bounded n (by omega)
    refine ⟨a + b, ?_⟩
    intro i hi w hw
    by_cases hin : i < n
    · have := ha i hin w hw; omega
    · have : i = n := by omega
      subst i
      have := hb w hw; omega

theorem finite_children_uniform (E : LabelledGraph)
    (finite : ∀ u, FiniteSupport (ForgetLabels E u)) (n : Nat) :
    ∃ b, ∀ u, u < n → ∀ w label, E u w label → w < b := by
  obtain ⟨b, hb⟩ := finite_union_bound (ForgetLabels E) n (by
    intro u _
    exact (finiteSupport_iff_bounded _).mp (finite u))
  exact ⟨b, fun u hu w label he => hb u hu w ⟨label, he⟩⟩

def Endpoint (E : LabelledGraph) (s : Nat → Bool) (k v w : Nat) : Prop :=
  ∃ n, FinitePath E s k n v w

def Good (E : LabelledGraph) (s : Nat → Bool) (k v : Nat) : Prop :=
  ¬ BoundedSupport (Endpoint E s k v)

theorem good_large {E : LabelledGraph} {s : Nat → Bool} {k v : Nat}
    (good : Good E s k v) (bound : Nat) :
    ∃ w n, bound ≤ w ∧ FinitePath E s k n v w := by
  classical
  by_cases h : ∃ w n, bound ≤ w ∧ FinitePath E s k n v w
  · exact h
  · apply False.elim
    apply good
    refine ⟨bound, ?_⟩
    intro w hw
    obtain ⟨n, hn⟩ := hw
    by_cases hb : bound ≤ w
    · exact False.elim (h ⟨w, n, hb, hn⟩)
    · omega

/-- The finite-branching step behind the internal König construction. -/
theorem good_successor (E : LabelledGraph) (s : Nat → Bool)
    (finite : ∀ u, FiniteSupport (ForgetLabels E u)) (k v : Nat)
    (good : Good E s k v) :
    ∃ w, E v w (s k) ∧ Good E s (k + 1) w := by
  classical
  apply Classical.byContradiction
  intro hnone
  obtain ⟨children, hchildren⟩ := (finiteSupport_iff_bounded _).mp (finite v)
  have hb : ∀ w, w < children → ∃ b, ∀ z,
      (E v w (s k) ∧ Endpoint E s (k + 1) w z) → z < b := by
    intro w _
    by_cases he : E v w (s k)
    · have ng : ¬ Good E s (k + 1) w := fun hg => hnone ⟨w, he, hg⟩
      have bounded : BoundedSupport (Endpoint E s (k + 1) w) :=
        Classical.byContradiction (fun h => ng h)
      obtain ⟨b, hbound⟩ := bounded
      exact ⟨b, fun z hz => hbound z hz.2⟩
    · exact ⟨0, fun _ hz => False.elim (he hz.1)⟩
  obtain ⟨bound, hbound⟩ := finite_union_bound
    (fun w z => E v w (s k) ∧ Endpoint E s (k + 1) w z) children hb
  obtain ⟨z, n, hz, path⟩ := good_large good (bound + v + 1)
  cases path with
  | nil => omega
  | @cons _ _ _ w _ he tail =>
    have hw := hchildren w ⟨s k, he⟩
    have hsmall := hbound w hw z ⟨he, ⟨_, tail⟩⟩
    omega

theorem infinite_path_from_good (E : LabelledGraph) (s : Nat → Bool)
    (finite : ∀ u, FiniteSupport (ForgetLabels E u)) (k v : Nat)
    (good : Good E s k v) :
    ∃ path : Nat → Nat, path 0 = v ∧
      ∀ n, E (path n) (path (n + 1)) (s (k + n)) := by
  classical
  let next : Nat → Nat → Nat := fun phase vertex =>
    if h : ∃ w, E vertex w (s phase) ∧ Good E s (phase + 1) w
    then Classical.choose h else 0
  have next_spec : ∀ phase vertex, Good E s phase vertex →
      E vertex (next phase vertex) (s phase) ∧
      Good E s (phase + 1) (next phase vertex) := by
    intro phase vertex hg
    have h := good_successor E s finite phase vertex hg
    dsimp [next]
    rw [dif_pos h]
    exact Classical.choose_spec h
  let path : Nat → Nat := fun n =>
    Nat.rec v (fun n vertex => next (k + n) vertex) n
  have hpath : ∀ n, Good E s (k + n) (path n) := by
    intro n
    induction n with
    | zero => exact good
    | succ n ih =>
      have h := (next_spec (k + n) (path n) ih).2
      simpa [path, Nat.add_assoc] using h
  refine ⟨path, rfl, ?_⟩
  intro n
  exact (next_spec (k + n) (path n) (hpath n)).1

/-- Any fixed word can be pulled backward above a chosen root bound. -/
theorem backward_word (E : LabelledGraph) (s : Nat → Bool)
    (population : BinaryNatPopulation E) (base : Nat)
    (roots : ∀ w, Root (ForgetLabels E) w → w < base) (len : Nat) :
    ∃ bound, base ≤ bound ∧ ∀ w, bound ≤ w →
      ∃ u, base ≤ u ∧ FinitePath E s 0 len u w := by
  have finite := population.2.1.2.2.1
  induction len with
  | zero => exact ⟨base, Nat.le_refl _, fun w hw => ⟨w, hw, .nil _ _⟩⟩
  | succ len ih =>
    obtain ⟨bound, hbase, hbound⟩ := ih
    obtain ⟨ceiling, hceiling⟩ := finite_children_uniform E finite bound
    refine ⟨bound + ceiling, by omega, ?_⟩
    intro w hw
    have nonroot : ¬ Root (ForgetLabels E) w := by
      intro hr
      have := roots w hr
      omega
    obtain ⟨parent, edge⟩ := population.2.2.2 w nonroot (s len)
    have hp : bound ≤ parent := by
      by_cases h : parent < bound
      · have := hceiling parent h w (s len) edge
        omega
      · omega
    obtain ⟨u, hu, path⟩ := hbound parent hp
    exact ⟨u, hu, path.snoc (by simpa using edge)⟩

theorem period_mul {s : Nat → Bool} {p : Nat}
    (period : ∀ k, s (k + p) = s k) (q k : Nat) :
    s (k + p * q) = s k := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.mul_succ, ← Nat.add_assoc, period, ih]

/-- Every late vertex is reached by whole periodic blocks from one finite interval. -/
theorem periodic_spanning (E : LabelledGraph) (s : Nat → Bool)
    (population : BinaryNatPopulation E) (p : Nat) (hp : 0 < p)
    (period : ∀ k, s (k + p) = s k) (base : Nat)
    (roots : ∀ w, Root (ForgetLabels E) w → w < base) :
    ∃ bound, ∀ w, base ≤ w → ∃ u q,
      base ≤ u ∧ u < bound ∧ FinitePath E s 0 (p * q) u w := by
  obtain ⟨bound, hbase, hback⟩ := backward_word E s population base roots p
  refine ⟨bound, ?_⟩
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hw
    by_cases hsmall : w < bound
    · exact ⟨w, 0, hw, hsmall, by simpa using FinitePath.nil (E := E) (s := s) 0 w⟩
    · obtain ⟨z, hz, path⟩ := hback w (by omega)
      have strict : ∀ u v b, E u v b → u < v :=
        fun u v b he => population.2.1.1 u v ⟨b, he⟩
      have hzw := path.lt_end strict hp
      obtain ⟨u, q, hu, hub, priorPath⟩ := ih z hzw hz
      have shifted := path.shift (fun k => period_mul period q k)
      have combined := priorPath.append shifted
      refine ⟨u, q + 1, hu, hub, ?_⟩
      simpa only [Nat.mul_succ] using combined

theorem periodic_good_above (E : LabelledGraph) (s : Nat → Bool)
    (population : BinaryNatPopulation E) (p : Nat) (hp : 0 < p)
    (period : ∀ k, s (k + p) = s k) (base : Nat)
    (roots : ∀ w, Root (ForgetLabels E) w → w < base) :
    ∃ v, base ≤ v ∧ Good E s 0 v := by
  classical
  obtain ⟨bound, spanning⟩ := periodic_spanning E s population p hp period base roots
  apply Classical.byContradiction
  intro hnone
  have hb : ∀ u, u < bound → ∃ b, ∀ w,
      (base ≤ u ∧ Endpoint E s 0 u w) → w < b := by
    intro u _
    by_cases hu : base ≤ u
    · have ng : ¬ Good E s 0 u := fun hg => hnone ⟨u, hu, hg⟩
      have bounded : BoundedSupport (Endpoint E s 0 u) :=
        Classical.byContradiction (fun h => ng h)
      obtain ⟨b, hb⟩ := bounded
      exact ⟨b, fun w hw => hb w hw.2⟩
    · exact ⟨0, fun _ hw => False.elim (hu hw.1)⟩
  obtain ⟨ceiling, hc⟩ := finite_union_bound
    (fun u w => base ≤ u ∧ Endpoint E s 0 u w) bound hb
  obtain ⟨u, q, hu, hub, path⟩ := spanning (base + ceiling) (by omega)
  have := hc u hub (base + ceiling) ⟨hu, ⟨p * q, path⟩⟩
  omega

/-- The finite prefix is prepended in forward label order, not reversed. -/
theorem FinitePath.prepend_infinite {E : LabelledGraph} {s : Nat → Bool}
    {k n u v : Nat} (finitePath : FinitePath E s k n u v)
    (tail : Nat → Nat) (tail_start : tail 0 = v)
    (tail_edges : ∀ i, E (tail i) (tail (i + 1)) (s (k + n + i))) :
    ∃ path : Nat → Nat, path 0 = u ∧
      ∀ i, E (path i) (path (i + 1)) (s (k + i)) := by
  induction finitePath with
  | nil => exact ⟨tail, tail_start, by simpa using tail_edges⟩
  | @cons k n u v w edge segment ih =>
    have ht : ∀ i, E (tail i) (tail (i + 1)) (s ((k + 1) + n + i)) := by
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using tail_edges
    obtain ⟨rest, hrest, hedges⟩ := ih tail_start ht
    let path : Nat → Nat
      | 0 => u
      | i + 1 => rest i
    refine ⟨path, rfl, ?_⟩
    intro i
    cases i with
    | zero => simpa [path, hrest] using edge
    | succ i =>
      simpa [path, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hedges i

/-- A periodic word is realized from arbitrarily late starting vertices. -/
theorem periodic_realized_above (s : Nat → Bool) (p : Nat) (hp : 0 < p)
    (period : ∀ k, s (k + p) = s k) (E : LabelledGraph)
    (population : BinaryNatPopulation E) (requested : Nat) :
    ∃ path : Nat → Nat, requested ≤ path 0 ∧
      ∀ k, E (path k) (path (k + 1)) (s k) := by
  obtain ⟨rootBound, hroot⟩ :=
    (finiteSupport_iff_bounded _).mp population.2.2.1
  have roots : ∀ w, Root (ForgetLabels E) w → w < rootBound + requested := by
    intro w hw
    have := hroot w hw
    omega
  obtain ⟨v, hv, good⟩ := periodic_good_above E s population p hp period
    (rootBound + requested) roots
  obtain ⟨path, hstart, hedges⟩ := infinite_path_from_good E s
    population.2.1.2.2.1 0 v good
  exact ⟨path, by omega, by simpa using hedges⟩

/-- Alexander's positive theorem in the actual binary natural-date model.
There is no unavoidability, populated-layer, or compactness premise. -/
theorem eventuallyPeriodic_realized (s : Nat → Bool)
    (eventually : EventuallyPeriodic s) (E : LabelledGraph)
    (population : BinaryNatPopulation E) : Realizes E s := by
  obtain ⟨start, p, hp, periodic⟩ := eventually
  obtain ⟨rootBound, hroot⟩ :=
    (finiteSupport_iff_bounded _).mp population.2.2.1
  obtain ⟨bound, _, backwards⟩ := backward_word E s population rootBound hroot start
  let tailWord : Nat → Bool := fun k => s (start + k)
  have tail_period : ∀ k, tailWord (k + p) = tailWord k := by
    intro k
    simpa only [tailWord, Nat.add_assoc] using periodic (start + k) (by omega)
  obtain ⟨tail, htail, hedges⟩ := periodic_realized_above tailWord p hp
    tail_period E population bound
  obtain ⟨u, _, finitePath⟩ := backwards (tail 0) htail
  have tail_edges : ∀ i, E (tail i) (tail (i + 1)) (s (0 + start + i)) := by
    simpa [tailWord] using hedges
  obtain ⟨path, _, hpath⟩ := finitePath.prepend_infinite tail rfl tail_edges
  exact ⟨path, by simpa using hpath⟩

/-- Unconditional classification for all actual binary natural-date populations. -/
theorem binaryNat_classification (s : Nat → Bool) :
    (∀ E : LabelledGraph, BinaryNatPopulation E → Realizes E s) ↔
      EventuallyPeriodic s := by
  constructor
  · intro unavoidable
    exact specieslike_unavoidable_implies_eventuallyPeriodic s
      (fun E population _ => unavoidable E population)
  · intro periodic E population
    exact eventuallyPeriodic_realized s periodic E population

/-- The former positive premise is now supplied by a proved theorem. -/
theorem specieslike_classification (s : Nat → Bool) :
    SpecieslikeUnavoidable s ↔ EventuallyPeriodic s :=
  specieslike_classification_of_positive eventuallyPeriodic_realized s

#print axioms good_successor
#print axioms infinite_path_from_good
#print axioms backward_word
#print axioms periodic_spanning
#print axioms periodic_realized_above
#print axioms eventuallyPeriodic_realized
#print axioms binaryNat_classification
#print axioms specieslike_classification

end PositiveUnavoidability
