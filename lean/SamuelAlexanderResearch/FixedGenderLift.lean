import SamuelAlexanderResearch.BinaryPopulation

/-!
The fixed-source-gender lift of the binary avoiding population, encoded by
copy(v,b)=2*v+bit(b). The productive core retains exactly copies with a child.
Population assertions are explicitly about the retained Nat subset, not about
deleted vertices. Construction source: the classification manuscript, Section 3.
-/

namespace FixedGenderLift

open SpeciesBridge BinaryPopulation BinaryAvoidance

def bit (b : Bool) : Nat := if b then 1 else 0
def copy (v : Nat) (b : Bool) : Nat := 2 * v + bit b
def base (x : Nat) : Nat := x / 2
def gender (x : Nat) : Bool := decide (x % 2 = 1)

@[simp] theorem base_copy (v : Nat) (b : Bool) : base (copy v b) = v := by
  cases b <;> simp [base, copy, bit] <;> omega

@[simp] theorem gender_copy (v : Nat) (b : Bool) : gender (copy v b) = b := by
  cases b <;> simp only [gender, copy, bit] <;>
    have h0 : (2 * v) % 2 = 0 := by omega
  · simp [h0]
  · have h1 : (2 * v + 1) % 2 = 1 := by omega
    simp [h1]

theorem copy_decomposition (x : Nat) : copy (base x) (gender x) = x := by
  by_cases h : x % 2 = 1
  · simp [copy, bit, base, gender, h]
    omega
  · simp [copy, bit, base, gender, h]
    omega

def LiftEdge (s : Nat → Bool) : Graph := fun x y =>
  BinaryAvoidance.Edge s (base x) (base y) (gender x)

def Core (s : Nat → Bool) : NatSet := fun x =>
  ∃ w, BinaryAvoidance.Edge s (base x) w (gender x)

def Induced (E : Graph) (S : NatSet) : Graph := fun x y => S x ∧ S y ∧ E x y

def AncestrallyClosed (E : Graph) (S : NatSet) : Prop :=
  ∀ x y, S y → Descendant E x y → S x

def Inspecies (E : Graph) (S : NatSet) : Prop :=
  InfiniteSupport S ∧ AncestrallyClosed E S ∧
    ∀ T : NatSet, (∀ x, T x → S x) → InfiniteSupport T →
      AncestrallyClosed E T → ∀ x, S x → T x

theorem edge_copies (s : Nat → Bool) (u w : Nat) (a b : Bool) :
    LiftEdge s (copy u a) (copy w b) ↔ BinaryAvoidance.Edge s u w a := by
  simp [LiftEdge]

theorem edge_source_core {s : Nat → Bool} {x y : Nat} (h : LiftEdge s x y) :
    Core s x := ⟨base y, h⟩

theorem lift_strict {s : Nat → Bool} {x y : Nat} (h : LiftEdge s x y) : x < y := by
  have hbase : base x < base y := by
    obtain ⟨_, h | h⟩ := h <;> omega
  dsimp [base] at hbase
  omega

theorem descendant_source_core {s : Nat → Bool} {x y : Nat}
    (h : Descendant (LiftEdge s) x y) : Core s x := by
  induction h with
  | edge he => exact edge_source_core he
  | snoc _ _ ih => exact ih

theorem core_ancestrallyClosed (s : Nat → Bool) :
    AncestrallyClosed (LiftEdge s) (Core s) := by
  intro x y _ h
  exact descendant_source_core h

theorem core_convex (s : Nat → Bool) : Convex (LiftEdge s) (Core s) := by
  intro x _ hfuture
  obtain ⟨y, _, hxy⟩ := hfuture
  exact descendant_source_core hxy

theorem copy_successor_edge (s : Nat → Bool) (v : Nat) (hv : 1 ≤ v) (b : Bool) :
    LiftEdge s (copy v (row s (v + 1))) (copy (v + 1) b) := by
  apply (edge_copies _ _ _ _ _).2
  exact ⟨by omega, Or.inl ⟨rfl, rfl⟩⟩

theorem some_core_copy (s : Nat → Bool) (v : Nat) : ∃ b, Core s (copy v b) := by
  by_cases hv : v = 0
  · subst v
    refine ⟨!(row s 2), 2, ?_⟩
    simp only [base_copy, gender_copy]
    exact ⟨by omega, Or.inr ⟨rfl, rfl⟩⟩
  · refine ⟨row s (v + 1), v + 1, ?_⟩
    simp only [base_copy, gender_copy]
    exact ⟨by omega, Or.inl ⟨rfl, rfl⟩⟩

theorem core_infinite (s : Nat → Bool) : InfiniteSupport (Core s) := by
  intro finite
  obtain ⟨bound, hbound⟩ := (finiteSupport_iff_bounded _).1 finite
  obtain ⟨b, hb⟩ := some_core_copy s (bound + 1)
  have h := hbound _ hb
  have hc := base_copy (bound + 1) b
  dsimp [base] at hc
  omega

theorem propagate_copies (s : Nat → Bool) (x v : Nat) (hv : 1 ≤ v)
    (reached : ∀ b, Descendant (LiftEdge s) x (copy v b)) (n : Nat) :
    ∀ b, Descendant (LiftEdge s) x (copy (v + n) b) := by
  induction n with
  | zero => simpa using reached
  | succ n ih =>
    intro b
    have he := copy_successor_edge s (v + n) (by omega) b
    exact .snoc (ih (row s (v + n + 1))) he

/-- Every productive copy reaches every copy at sufficiently late base indices. -/
theorem core_reaches_late (s : Nat → Bool) (x : Nat) (hx : Core s x)
    (y : Nat) (hy : base x + 2 ≤ base y) : Descendant (LiftEdge s) x y := by
  obtain ⟨w, edge⟩ := hx
  have hw : 2 ≤ w := edge.1
  have hstep : w ≤ base x + 2 := by rcases edge.2 with h | h <;> omega
  have hcopies : ∀ b, Descendant (LiftEdge s) x (copy w b) := by
    intro b
    apply Descendant.edge
    simpa only [LiftEdge, base_copy] using edge
  have h := propagate_copies s x w (by omega) hcopies (base y - w) (gender y)
  have heq : w + (base y - w) = base y := by omega
  rw [heq, copy_decomposition] at h
  exact h

theorem core_nonDescendants_bounded (s : Nat → Bool) (x : Nat) (hx : Core s x) :
    ∀ y, ¬ Descendant (LiftEdge s) x y → y < 2 * (base x + 2) := by
  intro y hn
  have hsmall : base y < base x + 2 := by
    by_cases h : base x + 2 ≤ base y
    · exact False.elim (hn (core_reaches_late s x hx y h))
    · omega
  dsimp [base] at *
  omega

theorem core_iap (s : Nat → Bool) : IAP (LiftEdge s) (Core s) := by
  intro x hx
  apply Or.inr
  apply (finiteSupport_iff_bounded _).2
  exact ⟨2 * (base x + 2), fun y hy => core_nonDescendants_bounded s x hx y hy.2⟩

theorem descendant_weakReach_core (s : Nat → Bool) {x y : Nat}
    (h : Descendant (LiftEdge s) x y) (hy : Core s y) :
    WeakReach (LiftEdge s) (Core s) x y := by
  induction h with
  | edge he => exact .edge (edge_source_core he) hy (Or.inl he)
  | snoc _ he ih =>
    exact .trans (ih (edge_source_core he))
      (.edge (edge_source_core he) hy (Or.inl he))

theorem core_weaklyConnected (s : Nat → Bool) : WeaklyConnected (LiftEdge s) (Core s) := by
  obtain ⟨b, hb⟩ := some_core_copy s 2
  refine ⟨⟨copy 2 b, hb⟩, ?_⟩
  intro x y hx hy
  obtain ⟨c, hc⟩ := some_core_copy s (base x + base y + 2)
  have hxc := core_reaches_late s x hx (copy (base x + base y + 2) c) (by simp only [base_copy]; omega)
  have hyc := core_reaches_late s y hy (copy (base x + base y + 2) c) (by simp only [base_copy]; omega)
  exact .trans (descendant_weakReach_core s hxc hc)
    (descendant_weakReach_core s hyc hc).symm

theorem core_specieslike (s : Nat → Bool) : Specieslike (LiftEdge s) (Core s) :=
  ⟨core_weaklyConnected s, core_iap s, core_convex s⟩

theorem core_inspecies (s : Nat → Bool) : Inspecies (LiftEdge s) (Core s) := by
  refine ⟨core_infinite s, core_ancestrallyClosed s, ?_⟩
  intro T _ infiniteT closed x hx
  classical
  by_cases h : T x
  · exact h
  · apply False.elim
    apply infiniteT
    apply (finiteSupport_iff_bounded _).2
    refine ⟨2 * (base x + 2), ?_⟩
    intro y hy
    apply core_nonDescendants_bounded s x hx y
    intro hd
    exact h (closed x y hy hd)

theorem full_lift_avoids (s : Nat → Bool) (aperiodic : ¬ EventuallyPeriodic s) :
    ¬ ∃ path : Nat → Nat, ∀ k,
      LiftEdge s (path k) (path (k + 1)) ∧ gender (path k) = s k := by
  rintro ⟨path, hmatch⟩
  apply aperiodic_target_avoided s aperiodic
  refine ⟨fun k => base (path k), ?_⟩
  intro k
  have he := (hmatch k).1
  change BinaryAvoidance.Edge s (base (path k)) (base (path (k + 1))) (s k)
  simpa only [LiftEdge, (hmatch k).2] using he

theorem odd_core_gender (s : Nat → Bool) (j : Nat) (a : Bool) :
    Core s (copy (2 * j + 1) a) ↔ a = s (j + 1) := by
  simp only [Core, base_copy, gender_copy]
  constructor
  · rintro ⟨w, _, h | h⟩
    · obtain ⟨hw, ha⟩ := h
      have heq : w = 2 * (j + 1) := by omega
      simpa only [heq, row_even] using ha
    · obtain ⟨hw, ha⟩ := h
      have heq : w = 2 * (j + 1) + 1 := by omega
      simpa only [heq, row_odd, Bool.not_not] using ha
  · intro ha
    refine ⟨2 * (j + 1), by omega, Or.inl ⟨by omega, ?_⟩⟩
    simpa only [row_even] using ha

theorem zero_core_gender (s : Nat → Bool) (a : Bool) :
    Core s (copy 0 a) ↔ a = !(s 1) := by
  simp only [Core, base_copy, gender_copy]
  constructor
  · rintro ⟨w, hw, h | h⟩
    · omega
    · obtain ⟨hw, ha⟩ := h
      have heq : w = 2 * 1 := by omega
      simpa only [heq, row_even] using ha
  · intro ha
    refine ⟨2 * 1, by omega, Or.inr ⟨rfl, ?_⟩⟩
    simpa only [row_even] using ha

theorem core_copy_odd (s : Nat → Bool) (x j : Nat) (hx : Core s x)
    (hbase : base x = 2 * j + 1) : x = copy (2 * j + 1) (s (j + 1)) := by
  have active := hx
  rw [← copy_decomposition x, hbase] at active
  have hg := (odd_core_gender s j (gender x)).1 active
  have h := copy_decomposition x
  rw [hbase, hg] at h
  exact h.symm

theorem copy_options (x v : Nat) (hv : base x = v) :
    x = copy v false ∨ x = copy v true := by
  have h := copy_decomposition x
  rw [hv] at h
  cases hg : gender x
  · exact Or.inl (by simpa only [hg] using h.symm)
  · exact Or.inr (by simpa only [hg] using h.symm)

def ChildCap (E : Graph) (S : NatSet) (cap : Nat) : Prop :=
  ∀ x, S x → ∃ children : List Nat, children.length ≤ cap ∧
    ∀ y, S y → E x y → y ∈ children

/-- One successor base index is odd and has only one productive copy. -/
theorem core_child_cap_three (s : Nat → Bool) : ChildCap (LiftEdge s) (Core s) 3 := by
  intro x _
  let j := base x / 2
  by_cases even : base x % 2 = 0
  · have hbase : base x = 2 * j := by dsimp [j]; omega
    refine ⟨[copy (2*j+1) (s (j+1)), copy (2*j+2) false, copy (2*j+2) true], by simp, ?_⟩
    intro y hy he
    have hstep : base y = base x + 1 ∨ base y = base x + 2 :=
      he.2.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
    rcases hstep with h | h
    · have hybase : base y = 2*j+1 := by omega
      have hycopy := core_copy_odd s y j hy hybase
      simp [hycopy]
    · have hybase : base y = 2*j+2 := by omega
      rcases copy_options y (2*j+2) hybase with hcopy | hcopy <;> simp [hcopy]
  · have hbase : base x = 2 * j + 1 := by dsimp [j]; omega
    refine ⟨[copy (2*j+2) false, copy (2*j+2) true, copy (2*j+3) (s (j+2))], by simp, ?_⟩
    intro y hy he
    have hstep : base y = base x + 1 ∨ base y = base x + 2 :=
      he.2.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
    rcases hstep with h | h
    · have hybase : base y = 2*j+2 := by omega
      rcases copy_options y (2*j+2) hybase with hcopy | hcopy <;> simp [hcopy]
    · have hybase : base y = 2*(j+1)+1 := by omega
      have hycopy := core_copy_odd s y (j+1) hy hybase
      have heq : 2*(j+1)+1 = 2*j+3 := by omega
      simp only [heq, Nat.add_assoc] at hycopy
      simp [hycopy]

theorem core_incoming_gender (s : Nat → Bool) (w : Nat) (_hw : Core s w)
    (hbase : 2 ≤ base w) (b : Bool) :
    ∃ u, Core s u ∧ LiftEdge s u w ∧ gender u = b := by
  obtain ⟨v, he⟩ := incoming_each_label s (base w) hbase b
  have edge : LiftEdge s (copy v b) w := by simpa only [LiftEdge, base_copy, gender_copy] using he
  exact ⟨copy v b, edge_source_core edge, edge, gender_copy v b⟩

theorem core_root_iff (s : Nat → Bool) (x : Nat) (hx : Core s x) :
    Root (Induced (LiftEdge s) (Core s)) x ↔ base x < 2 := by
  constructor
  · intro root
    by_cases h : 2 ≤ base x
    · obtain ⟨u, hu, he, _⟩ := core_incoming_gender s x hx h false
      exact False.elim (root u ⟨hu, hx, he⟩)
    · omega
  · intro h u edge
    have := edge.2.2.1
    omega

theorem core_roots_exactly (s : Nat → Bool) (x : Nat) :
    (Core s x ∧ Root (Induced (LiftEdge s) (Core s)) x) ↔
      x = copy 0 (!(s 1)) ∨ x = copy 1 (s 1) := by
  constructor
  · rintro ⟨hx, hr⟩
    have hsmall := (core_root_iff s x hx).1 hr
    have hcases : base x = 0 ∨ base x = 1 := by omega
    rcases hcases with hbase | hbase
    · have active := hx
      rw [← copy_decomposition x, hbase] at active
      have hg := (zero_core_gender s (gender x)).1 active
      have h := copy_decomposition x
      rw [hbase, hg] at h
      exact Or.inl h.symm
    · exact Or.inr (by simpa using core_copy_odd s x 0 hx (by simpa using hbase))
  · intro h
    rcases h with h | h
    · subst x
      have hx := (zero_core_gender s (!(s 1))).2 rfl
      exact ⟨hx, (core_root_iff s _ hx).2 (by simp)⟩
    · subst x
      have hx : Core s (copy 1 (s 1)) := by simpa using (odd_core_gender s 0 (s 1)).2 rfl
      exact ⟨hx, (core_root_iff s _ hx).2 (by simp)⟩

theorem core_roots_distinct (s : Nat → Bool) : copy 0 (!(s 1)) ≠ copy 1 (s 1) := by
  intro h
  have := congrArg base h
  simp at this

/-- An explicit population on a retained Nat subset, with fixed source genders.
Deleted indices are not vertices and are not counted as extra roots. -/
def FixedGenderPopulation (E : Graph) (S : NatSet) (g : Nat → Bool) (cap : Nat) : Prop :=
  InfiniteSupport S ∧
  (∀ u w, S u → S w → E u w → u < w) ∧
  (∀ date, FiniteSupport (fun v => S v ∧ v < date)) ∧
  FiniteSupport (fun v => S v ∧ Root (Induced E S) v) ∧
  ChildCap E S cap ∧
  ∀ w, S w → ¬ Root (Induced E S) w →
    ∀ b, ∃ u, S u ∧ E u w ∧ g u = b

theorem core_fixedGenderPopulation (s : Nat → Bool) :
    FixedGenderPopulation (LiftEdge s) (Core s) gender 3 := by
  refine ⟨core_infinite s, fun _ _ _ _ h => lift_strict h, ?_, ?_,
    core_child_cap_three s, ?_⟩
  · intro date
    apply (finiteSupport_iff_bounded _).2
    exact ⟨date, fun _ h => h.2⟩
  · apply (finiteSupport_iff_bounded _).2
    refine ⟨4, ?_⟩
    intro v hv
    have h := (core_root_iff s v hv.1).1 hv.2
    dsimp [base] at h
    omega
  · intro w hw nonroot b
    have hbase : 2 ≤ base w := by
      by_cases h : base w < 2
      · exact False.elim (nonroot ((core_root_iff s w hw).2 h))
      · omega
    exact core_incoming_gender s w hw hbase b

theorem core_avoids (s : Nat → Bool) (aperiodic : ¬ EventuallyPeriodic s) :
    ¬ ∃ path : Nat → Nat, ∀ k, Core s (path k) ∧
      LiftEdge s (path k) (path (k + 1)) ∧ gender (path k) = s k := by
  rintro ⟨path, hpath⟩
  exact full_lift_avoids s aperiodic ⟨path, fun k => (hpath k).2⟩

/-- Three-child fixed-gender, specieslike and inspecies avoiding witness. -/
theorem productive_core_avoider (s : Nat → Bool) (aperiodic : ¬ EventuallyPeriodic s) :
    FixedGenderPopulation (LiftEdge s) (Core s) gender 3 ∧
    Specieslike (LiftEdge s) (Core s) ∧
    Inspecies (LiftEdge s) (Core s) ∧
    ¬ ∃ path : Nat → Nat, ∀ k, Core s (path k) ∧
      LiftEdge s (path k) (path (k + 1)) ∧ gender (path k) = s k :=
  ⟨core_fixedGenderPopulation s, core_specieslike s, core_inspecies s,
    core_avoids s aperiodic⟩

/-- Restricting to productive copies preserves every path to a retained endpoint. -/
theorem core_induced_descendant_iff (s : Nat → Bool) (x y : Nat) (hy : Core s y) :
    Descendant (Induced (LiftEdge s) (Core s)) x y ↔ Descendant (LiftEdge s) x y := by
  constructor
  · intro h
    induction h with
    | edge he => exact .edge he.2.2
    | snoc _ he ih => exact .snoc (ih he.1) he.2.2
  · intro h
    induction h with
    | edge he => exact .edge ⟨edge_source_core he, hy, he⟩
    | snoc _ he ih =>
      exact .snoc (ih (edge_source_core he)) ⟨edge_source_core he, hy, he⟩

theorem induced_weakReach (E : Graph) (S : NatSet) {x y : Nat}
    (h : WeakReach E S x y) : WeakReach (Induced E S) S x y := by
  induction h with
  | refl hx => exact .refl hx
  | edge hx hy he =>
    apply WeakReach.edge hx hy
    rcases he with he | he
    · exact Or.inl ⟨hx, hy, he⟩
    · exact Or.inr ⟨hy, hx, he⟩
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2

theorem induced_descendant_members (E : Graph) (S : NatSet) {x y : Nat}
    (h : Descendant (Induced E S) x y) : S x ∧ S y := by
  induction h with
  | edge he => exact ⟨he.1, he.2.1⟩
  | snoc _ he ih => exact ⟨ih.1, he.2.1⟩

theorem core_induced_specieslike (s : Nat → Bool) :
    Specieslike (Induced (LiftEdge s) (Core s)) (Core s) := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨nonempty, connected⟩ := core_weaklyConnected s
    exact ⟨nonempty, fun x y hx hy => induced_weakReach _ _ (connected x y hx hy)⟩
  · intro x hx
    apply Or.inr
    apply (finiteSupport_iff_bounded _).2
    refine ⟨2 * (base x + 2), ?_⟩
    intro y hy
    apply core_nonDescendants_bounded s x hx y
    intro hfull
    exact hy.2 ((core_induced_descendant_iff s x y hy.1).2 hfull)
  · intro x hpast _
    obtain ⟨a, _, hax⟩ := hpast
    exact (induced_descendant_members _ _ hax).2

theorem core_induced_inspecies (s : Nat → Bool) :
    Inspecies (Induced (LiftEdge s) (Core s)) (Core s) := by
  refine ⟨core_infinite s, ?_, ?_⟩
  · intro x y _ h
    exact (induced_descendant_members _ _ h).1
  · intro T subset infiniteT closed x hx
    classical
    by_cases h : T x
    · exact h
    · apply False.elim
      apply infiniteT
      apply (finiteSupport_iff_bounded _).2
      refine ⟨2 * (base x + 2), ?_⟩
      intro y hy
      apply core_nonDescendants_bounded s x hx y
      intro hd
      exact h (closed x y hy ((core_induced_descendant_iff s x y (subset y hy)).2 hd))

theorem core_reflection (s : Nat → Bool) : Reflection (LiftEdge s) (Core s) := by
  intro x hx _ finite
  obtain ⟨bound, hb⟩ := (finiteSupport_iff_bounded _).1 finite
  apply core_infinite s
  apply (finiteSupport_iff_bounded _).2
  refine ⟨bound + 2 * (base x + 2), ?_⟩
  intro y hy
  by_cases hd : Descendant (LiftEdge s) x y
  · have := hb y ⟨hy, hd⟩; omega
  · have := core_nonDescendants_bounded s x hx y hd; omega

theorem core_induced_reflection (s : Nat → Bool) :
    Reflection (Induced (LiftEdge s) (Core s)) (Core s) := by
  intro x _ infinite finite
  apply infinite
  exact finiteSupport_mono
    (fun y h => ⟨(induced_descendant_members _ _ h).2, h⟩) finite

/-- The same witness with species predicates evaluated in the actual induced graph. -/
theorem productive_core_induced_avoider (s : Nat → Bool)
    (aperiodic : ¬ EventuallyPeriodic s) :
    FixedGenderPopulation (LiftEdge s) (Core s) gender 3 ∧
    Specieslike (Induced (LiftEdge s) (Core s)) (Core s) ∧
    Inspecies (Induced (LiftEdge s) (Core s)) (Core s) ∧
    Reflection (Induced (LiftEdge s) (Core s)) (Core s) ∧
    ¬ ∃ path : Nat → Nat, ∀ k,
      Induced (LiftEdge s) (Core s) (path k) (path (k + 1)) ∧ gender (path k) = s k := by
  refine ⟨core_fixedGenderPopulation s, core_induced_specieslike s,
    core_induced_inspecies s, core_induced_reflection s, ?_⟩
  rintro ⟨path, hpath⟩
  exact full_lift_avoids s aperiodic ⟨path, fun k => ⟨(hpath k).1.2.2, (hpath k).2⟩⟩

/-- The earlier repair removes only the two isolated root copies. -/
def Clean (s : Nat → Bool) : NatSet := fun x => 2 ≤ base x ∨ Core s x

theorem clean_contains_core (s : Nat → Bool) (x : Nat) (hx : Core s x) : Clean s x :=
  Or.inr hx

theorem lift_edge_clean {s : Nat → Bool} {x y : Nat} (h : LiftEdge s x y) :
    Clean s x ∧ Clean s y := ⟨Or.inr (edge_source_core h), Or.inl h.1⟩

theorem weakReach_mono (E : Graph) {S T : NatSet} (subset : ∀ x, S x → T x)
    {x y : Nat} (h : WeakReach E S x y) : WeakReach E T x y := by
  induction h with
  | refl hx => exact .refl (subset _ hx)
  | edge hx hy he => exact .edge (subset _ hx) (subset _ hy) he
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2

theorem clean_weaklyConnected (s : Nat → Bool) : WeaklyConnected (LiftEdge s) (Clean s) := by
  obtain ⟨b, hb⟩ := some_core_copy s 2
  have coreConnect := (core_weaklyConnected s).2
  have fromAnchor : ∀ x, Clean s x → WeakReach (LiftEdge s) (Clean s) (copy 2 b) x := by
    intro x hx
    by_cases active : Core s x
    · exact weakReach_mono _ (clean_contains_core s) (coreConnect _ _ hb active)
    · have hbase : 2 ≤ base x := hx.elim id (fun h => False.elim (active h))
      obtain ⟨v, he⟩ := incoming_each_label s (base x) hbase false
      have edge : LiftEdge s (copy v false) x := by
        simpa only [LiftEdge, base_copy, gender_copy] using he
      have parentActive := edge_source_core edge
      exact .trans
        (weakReach_mono _ (clean_contains_core s) (coreConnect _ _ hb parentActive))
        (.edge (Or.inr parentActive) hx (Or.inl edge))
  exact ⟨⟨copy 2 b, Or.inr hb⟩, fun x y hx hy => .trans (fromAnchor x hx).symm (fromAnchor y hy)⟩

theorem clean_specieslike (s : Nat → Bool) : Specieslike (LiftEdge s) (Clean s) := by
  refine ⟨clean_weaklyConnected s, ?_, ?_⟩
  · intro x _
    by_cases active : Core s x
    · apply Or.inr
      apply (finiteSupport_iff_bounded _).2
      exact ⟨2*(base x+2), fun y hy => core_nonDescendants_bounded s x active y hy.2⟩
    · apply Or.inl
      exact ⟨[], fun y hy => False.elim (active (descendant_source_core hy.2))⟩
  · intro x _ future
    obtain ⟨y, _, hxy⟩ := future
    exact Or.inr (descendant_source_core hxy)

theorem full_child_cap_four (s : Nat → Bool) (S : NatSet) : ChildCap (LiftEdge s) S 4 := by
  intro x _
  refine ⟨[copy (base x+1) false, copy (base x+1) true,
    copy (base x+2) false, copy (base x+2) true], by simp, ?_⟩
  intro y _ he
  rcases he.2 with h | h
  · rcases copy_options y (base x+1) h.1 with hc | hc <;> simp [hc]
  · rcases copy_options y (base x+2) h.1 with hc | hc <;> simp [hc]

theorem clean_root_iff (s : Nat → Bool) (x : Nat) (hx : Clean s x) :
    Root (Induced (LiftEdge s) (Clean s)) x ↔ base x < 2 := by
  constructor
  · intro root
    by_cases h : 2 ≤ base x
    · obtain ⟨v, he⟩ := incoming_each_label s (base x) h false
      have edge : LiftEdge s (copy v false) x := by
        simpa only [LiftEdge, base_copy, gender_copy] using he
      exact False.elim (root _ ⟨(lift_edge_clean edge).1, hx, edge⟩)
    · omega
  · intro h u edge
    have := edge.2.2.1
    omega

theorem clean_roots_exactly (s : Nat → Bool) (x : Nat) :
    (Clean s x ∧ Root (Induced (LiftEdge s) (Clean s)) x) ↔
      x = copy 0 (!(s 1)) ∨ x = copy 1 (s 1) := by
  constructor
  · rintro ⟨hx, hr⟩
    have hsmall := (clean_root_iff s x hx).1 hr
    have active : Core s x := hx.elim (fun h => False.elim (by omega)) id
    exact (core_roots_exactly s x).1 ⟨active, (core_root_iff s x active).2 hsmall⟩
  · intro h
    obtain ⟨active, root⟩ := (core_roots_exactly s x).2 h
    have clean : Clean s x := Or.inr active
    exact ⟨clean, (clean_root_iff s x clean).2 ((core_root_iff s x active).1 root)⟩

theorem clean_fixedGenderPopulation (s : Nat → Bool) :
    FixedGenderPopulation (LiftEdge s) (Clean s) gender 4 := by
  have infinite : InfiniteSupport (Clean s) := by
    intro finite
    exact core_infinite s (finiteSupport_mono (clean_contains_core s) finite)
  refine ⟨infinite, fun _ _ _ _ h => lift_strict h, ?_, ?_, full_child_cap_four s _, ?_⟩
  · intro date
    exact (finiteSupport_iff_bounded _).2 ⟨date, fun _ h => h.2⟩
  · apply (finiteSupport_iff_bounded _).2
    refine ⟨4, ?_⟩
    intro v hv
    have h := (clean_root_iff s v hv.1).1 hv.2
    dsimp [base] at h
    omega
  · intro w hw nonroot b
    have hbase : 2 ≤ base w := by
      by_cases h : base w < 2
      · exact False.elim (nonroot ((clean_root_iff s w hw).2 h))
      · omega
    obtain ⟨v, he⟩ := incoming_each_label s (base w) hbase b
    have edge : LiftEdge s (copy v b) w := by
      simpa only [LiftEdge, base_copy, gender_copy] using he
    exact ⟨copy v b, (lift_edge_clean edge).1, edge, gender_copy v b⟩

def TerminalCopy (s : Nat → Bool) (j : Nat) : Nat :=
  copy (2*j+3) (!(s (j+2)))

theorem terminal_copy_clean (s : Nat → Bool) (j : Nat) : Clean s (TerminalCopy s j) := by
  apply Or.inl
  simp [TerminalCopy]

theorem terminal_copy_not_core (s : Nat → Bool) (j : Nat) : ¬ Core s (TerminalCopy s j) := by
  intro active
  have heq : 2*j+3 = 2*(j+1)+1 := by omega
  have h := (odd_core_gender s (j+1) (!(s (j+2)))).1 (by simpa [TerminalCopy, heq] using active)
  have h' : (!(s (j+2))) = s (j+2) := h
  cases hs : s (j+2) <;> simp [hs] at h'

theorem terminal_copy_no_children (s : Nat → Bool) (j y : Nat) :
    ¬ LiftEdge s (TerminalCopy s j) y :=
  fun h => terminal_copy_not_core s j (edge_source_core h)

theorem terminal_copies_infinite (s : Nat → Bool) :
    InfiniteSupport (fun x => ∃ j, x = TerminalCopy s j) := by
  intro finite
  obtain ⟨bound, hb⟩ := (finiteSupport_iff_bounded _).1 finite
  have h := hb (TerminalCopy s bound) ⟨bound, rfl⟩
  have hc : base (TerminalCopy s bound) = 2*bound+3 := by simp [TerminalCopy]
  dsimp [base] at hc
  omega

theorem clean_not_inspecies (s : Nat → Bool) : ¬ Inspecies (LiftEdge s) (Clean s) := by
  intro h
  have allCore := h.2.2 (Core s) (clean_contains_core s) (core_infinite s) (core_ancestrallyClosed s)
  exact terminal_copy_not_core s 0 (allCore _ (terminal_copy_clean s 0))

theorem clean_avoider (s : Nat → Bool) (aperiodic : ¬ EventuallyPeriodic s) :
    FixedGenderPopulation (LiftEdge s) (Clean s) gender 4 ∧
    Specieslike (LiftEdge s) (Clean s) ∧
    ¬ Inspecies (LiftEdge s) (Clean s) ∧
    ¬ ∃ path : Nat → Nat, ∀ k, Clean s (path k) ∧
      LiftEdge s (path k) (path (k + 1)) ∧ gender (path k) = s k := by
  refine ⟨clean_fixedGenderPopulation s, clean_specieslike s, clean_not_inspecies s, ?_⟩
  rintro ⟨path, hpath⟩
  exact full_lift_avoids s aperiodic ⟨path, fun k => (hpath k).2⟩

#print axioms core_reaches_late
#print axioms core_child_cap_three
#print axioms core_roots_exactly
#print axioms core_fixedGenderPopulation
#print axioms core_specieslike
#print axioms core_inspecies
#print axioms full_lift_avoids
#print axioms productive_core_avoider
#print axioms core_induced_descendant_iff
#print axioms productive_core_induced_avoider
#print axioms clean_roots_exactly
#print axioms terminal_copies_infinite
#print axioms clean_not_inspecies
#print axioms clean_avoider

end FixedGenderLift
