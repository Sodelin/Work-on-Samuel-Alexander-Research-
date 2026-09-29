import RealBridges
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union
import Mathlib.Logic.Encodable.Basic

/-! Finite-fibre blow-ups and absence of countable universal families.
    Uses literal real birthdates and a label-polymorphic copy of the population axioms.
    The binary case has an explicit adapter to the existing RealBridges model.
    Classical graph nonuniversality is not claimed as new.

    Scope: arbitrary label type (hence all finite nonempty alphabets), actual
    real birthdates, finitely many children and roots, functional edge labels,
    and a parent of every label at each nonroot. The construction preserves
    the complete infinite word language and gives an equivalence of root sets.
    It excludes countable locally finite host families under injective edge
    preservation, even allowing any finite global edge-stretch bound.
    It does NOT preserve a prescribed uniform child cap or exact parent counts;
    arbitrary unbounded-stretch topological/ancestry embeddings are not settled.
    This formalizes a population-specific adaptation of a classical graph
    obstruction; no worldwide priority or independent human review is claimed. -/

namespace GenericUniversalAvoiders

open RealBridges
universe u v w
variable {Label : Type w}


/-- Alexander's edge-labelled population axioms, with actual real dates.
Labels may be any type; finite nonempty alphabets are included. -/
structure Population (V : Type u) (Label : Type w) where
  edge : V → V → Label → Prop
  birth : V → ℝ
  infinite : BirthOrder.InfiniteVertices V
  sublevels : ∀ r, BirthOrder.FiniteCover (fun x => birth x ≤ r)
  chronological : ∀ x y b, edge x y b → birth x < birth y
  unique : ∀ x y a b, edge x y a → edge x y b → a = b
  roots : BirthOrder.FiniteCover (fun y => ∀ x b, ¬ edge x y b)
  children : ∀ x, BirthOrder.FiniteCover (fun y => ∃ b, edge x y b)
  parents : ∀ y, ¬ (∀ x b, ¬ edge x y b) → ∀ b, ∃ x, edge x y b

noncomputable def Population.enumeration {V : Type u} (p : Population V Label) :
    BirthOrder.OrderedEnumeration p.birth :=
  BirthOrder.orderedEnumeration p.birth p.infinite p.sublevels

/-- Literal adapter from the existing binary real-population model. -/
def ofBinary {V : Type u} (p : BinaryRealPopulation V) : Population V Bool where
  edge := p.edge
  birth := p.birth
  infinite := p.infinite
  sublevels := p.sublevels
  chronological := p.chronological
  unique := p.unique
  roots := p.roots
  children := p.children
  parents := p.parents

abbrev Fibre (V : Type u) (m : V → ℕ) := (x : V) × Fin (m x)

def section0 {V : Type u} (m : V → ℕ) (hm : ∀ x, 0 < m x) (x : V) :
    Fibre V m := ⟨x, ⟨0, hm x⟩⟩

theorem finiteCover_fibres {V : Type u} (m : V → ℕ) (S : V → Prop)
    (hf : BirthOrder.FiniteCover S) :
    BirthOrder.FiniteCover (fun x : Fibre V m => S x.1) := by
  classical
  obtain ⟨xs, hxs⟩ := hf
  refine ⟨xs.flatMap (fun x => (List.finRange (m x)).map (fun i => Sigma.mk x i)), ?_⟩
  rintro ⟨x, i⟩ hx
  apply List.mem_flatMap.mpr
  exact ⟨x, hxs x hx, by simp⟩

def liftedEdge {V : Type u} (p : Population V Label) (m : V → ℕ)
    (x y : Fibre V m) (b : Label) : Prop := p.edge x.1 y.1 b

theorem lifted_root_iff {V : Type u} (p : Population V Label)
    (m : V → ℕ) (hm : ∀ x, 0 < m x) (y : Fibre V m) :
    (∀ x b, ¬ liftedEdge p m x y b) ↔ (∀ x b, ¬ p.edge x y.1 b) := by
  constructor
  · intro h x b he
    exact h (section0 m hm x) b he
  · intro h x b he
    exact h x.1 b he

def blowUp {V : Type u} (p : Population V Label) (m : V → ℕ)
    (hm : ∀ x, 0 < m x) : Population (Fibre V m) Label where
  edge := liftedEdge p m
  birth := fun x => p.birth x.1
  infinite := by
    intro xs
    obtain ⟨x, hx⟩ := p.infinite (xs.map Sigma.fst)
    refine ⟨section0 m hm x, ?_⟩
    intro hi
    apply hx
    exact List.mem_map.mpr ⟨section0 m hm x, hi, rfl⟩
  sublevels := fun r => finiteCover_fibres m _ (p.sublevels r)
  chronological := fun x y b h => p.chronological x.1 y.1 b h
  unique := fun x y a b ha hb => p.unique x.1 y.1 a b ha hb
  roots := by
    obtain ⟨xs, hxs⟩ := finiteCover_fibres m _ p.roots
    exact ⟨xs, fun y hy => hxs y ((lifted_root_iff p m hm y).mp hy)⟩
  children := fun x => finiteCover_fibres m _ (p.children x.1)
  parents := by
    intro y hy b
    have hn : ¬ (∀ x a, ¬ p.edge x y.1 a) := fun h =>
      hy ((lifted_root_iff p m hm y).mpr h)
    obtain ⟨x, hx⟩ := p.parents y.1 hn b
    exact ⟨section0 m hm x, hx⟩

def Realizes {V : Type u} (p : Population V Label) (s : ℕ → Label) : Prop :=
  ∃ path : ℕ → V, ∀ k, p.edge (path k) (path (k+1)) (s k)

theorem blowUp_language {V : Type u} (p : Population V Label)
    (m : V → ℕ) (hm : ∀ x, 0 < m x) (s : ℕ → Label) :
    Realizes (blowUp p m hm) s ↔ Realizes p s := by
  constructor
  · rintro ⟨path, hpath⟩
    exact ⟨fun k => (path k).1, hpath⟩
  · rintro ⟨path, hpath⟩
    exact ⟨fun k => section0 m hm (path k), hpath⟩

structure LocallyFiniteHost (W : Type v) where
  adjacent : W → W → Prop
  neighbours_finite : ∀ x, Set.Finite {y | adjacent x y}

noncomputable def LocallyFiniteHost.neighbours {W : Type v}
    (H : LocallyFiniteHost W) (x : W) : Finset W :=
  (H.neighbours_finite x).toFinset

noncomputable def LocallyFiniteHost.ball {W : Type v}
    (H : LocallyFiniteHost W) (x : W) : ℕ → Finset W
  | 0 => {x}
  | n+1 => by
    classical
    exact (H.ball x n).biUnion (fun y => insert y (H.neighbours y))

theorem LocallyFiniteHost.mem_ball_zero {W : Type v}
    (H : LocallyFiniteHost W) (x : W) : x ∈ H.ball x 0 := by
  simp [LocallyFiniteHost.ball]

theorem LocallyFiniteHost.step_mem_ball {W : Type v}
    (H : LocallyFiniteHost W) {x y z : W} {n : ℕ}
    (hy : y ∈ H.ball x n) (he : H.adjacent y z) : z ∈ H.ball x (n+1) := by
  classical
  simp only [LocallyFiniteHost.ball, Finset.mem_biUnion]
  refine ⟨y, hy, ?_⟩
  exact Finset.mem_insert_of_mem ((H.neighbours_finite y).mem_toFinset.mpr he)

def PreservesEdges {V : Type u} {W : Type v}
    (p : Population V Label) (H : LocallyFiniteHost W) (f : V → W) : Prop :=
  ∀ x y b, p.edge x y b → H.adjacent (f x) (f y)


theorem finiteCover_bool_copies {V : Type u} (S : V → Prop)
    (h : BirthOrder.FiniteCover S) :
    BirthOrder.FiniteCover (fun x : V × Bool => S x.1) := by
  obtain ⟨xs, hxs⟩ := h
  refine ⟨xs.flatMap (fun x => [(x,false),(x,true)]), ?_⟩
  rintro ⟨x,b⟩ hx
  apply List.mem_flatMap.mpr
  refine ⟨x,hxs x hx,?_⟩
  cases b <;> simp

def doubledEdge {V : Type u} (p : Population V Label)
    (x y : V × Bool) (b : Bool) : Prop := (∃ a, p.edge x.1 y.1 a) ∧ x.2 = b

theorem doubled_root_iff {V : Type u} (p : Population V Label) (y : V × Bool) :
    (∀ x b, ¬ doubledEdge p x y b) ↔ (∀ x b, ¬ p.edge x y.1 b) := by
  constructor
  · intro h x b he
    exact h (x,false) false ⟨⟨b,he⟩,rfl⟩
  · intro h x b he
    obtain ⟨a,ha⟩ := he.1
    exact h x.1 a ha

/-- Auxiliary binary cover, used only to obtain a ray from the checked
binary positive theorem. Projecting its edges forgets the artificial gender.
No ray-existence or countability assumption is added to the final theorem. -/
def binaryCover {V : Type u} (p : Population V Label) : BinaryRealPopulation (V × Bool) where
  edge := doubledEdge p
  birth := fun x => p.birth x.1
  infinite := by
    intro xs
    obtain ⟨x,hx⟩ := p.infinite (xs.map Prod.fst)
    exact ⟨(x,false),fun h => hx (List.mem_map.mpr ⟨(x,false),h,rfl⟩)⟩
  sublevels := fun r => finiteCover_bool_copies _ (p.sublevels r)
  chronological := by
    intro x y b he
    obtain ⟨a,ha⟩ := he.1
    exact p.chronological x.1 y.1 a ha
  unique := fun _ _ _ _ ha hb => ha.2.symm.trans hb.2
  roots := by
    obtain ⟨xs,hxs⟩ := finiteCover_bool_copies _ p.roots
    exact ⟨xs,fun y hy => hxs y ((doubled_root_iff p y).mp hy)⟩
  children := by
    intro x
    obtain ⟨xs,hxs⟩ := finiteCover_bool_copies _ (p.children x.1)
    exact ⟨xs,fun y ⟨_,he⟩ => hxs y he.1⟩
  parents := by
    classical
    intro y hy b
    have hn : ¬ (∀ x a, ¬ p.edge x y.1 a) := fun h =>
      hy ((doubled_root_iff p y).mpr h)
    obtain ⟨x,hx⟩ := not_forall.mp hn
    obtain ⟨a,ha⟩ := not_forall.mp hx
    exact ⟨(x,b),⟨a,not_not.mp ha⟩,rfl⟩

theorem exists_ray {V : Type u} (p : Population V Label) :
    ∃ ray : ℕ → V, Function.Injective ray ∧
      (∀ k, ∃ b, p.edge (ray k) (ray (k+1)) b) := by
  have he : BinaryAvoidance.EventuallyPeriodic (fun _ : ℕ => false) :=
    ⟨0, 1, by omega, fun _ _ => rfl⟩
  obtain ⟨ray,hr⟩ := RealBridges.eventuallyPeriodic_realized (binaryCover p)
    (fun _ => false) he
  have hstep : ∀ k, ∃ b, p.edge (ray k).1 (ray (k+1)).1 b := fun k => (hr k).1
  have hs : StrictMono (fun n => p.birth (ray n).1) := by
    apply strictMono_nat_of_lt_succ
    intro k
    obtain ⟨b,hb⟩ := hstep k
    exact p.chronological _ _ b hb
  exact ⟨fun k => (ray k).1,fun _ _ h => hs.injective (congrArg p.birth h),hstep⟩

noncomputable def rayMultiplicity {V : Type u} (ray : ℕ → V)
    (demand : ℕ → ℕ) (x : V) : ℕ := by
  classical
  exact if h : ∃ k, ray (k+1) = x then demand (Classical.choose h) else 1

theorem rayMultiplicity_pos {V : Type u} (ray : ℕ → V)
    (demand : ℕ → ℕ) (hd : ∀ k, 0 < demand k) (x : V) :
    0 < rayMultiplicity ray demand x := by
  classical
  unfold rayMultiplicity
  split
  · exact hd _
  · omega

theorem rayMultiplicity_at {V : Type u} (ray : ℕ → V)
    (hi : Function.Injective ray) (demand : ℕ → ℕ) (k : ℕ) :
    rayMultiplicity ray demand (ray (k+1)) = demand k := by
  classical
  have ex : ∃ n, ray (n+1) = ray (k+1) := ⟨k, rfl⟩
  have heq : Classical.choose ex = k := by
    have h := hi (Classical.choose_spec ex)
    omega
  simp only [rayMultiplicity, dif_pos ex, heq]

theorem rayMultiplicity_root {V : Type u} (p : Population V Label)
    (ray : ℕ → V) (hr : ∀ k, ∃ b, p.edge (ray k) (ray (k+1)) b)
    (demand : ℕ → ℕ) (x : V) (hx : ∀ y b, ¬ p.edge y x b) :
    rayMultiplicity ray demand x = 1 := by
  classical
  have hn : ¬ ∃ k, ray (k+1) = x := by
    rintro ⟨k, hk⟩
    obtain ⟨b,hb⟩ := hr k
    exact hx (ray k) b (by simpa only [← hk] using hb)
  simp only [rayMultiplicity, dif_neg hn]

noncomputable def hostDemand (W : ℕ → Type v) [∀ j, Encodable (W j)]
    (H : ∀ j, LocallyFiniteHost (W j)) (k : ℕ) : ℕ :=
  match Encodable.decode (α := Σ j, W j) k with
  | none => 1
  | some x => ((H x.1).ball x.2 (k+1)).card + 1

theorem hostDemand_pos (W : ℕ → Type v) [∀ j, Encodable (W j)]
    (H : ∀ j, LocallyFiniteHost (W j)) (k : ℕ) : 0 < hostDemand W H k := by
  unfold hostDemand
  split <;> omega

theorem hostDemand_encode (W : ℕ → Type v) [∀ j, Encodable (W j)]
    (H : ∀ j, LocallyFiniteHost (W j)) (j : ℕ) (w : W j) :
    hostDemand W H (Encodable.encode (⟨j,w⟩ : Σ j, W j)) =
      ((H j).ball w (Encodable.encode (⟨j,w⟩ : Σ j, W j) + 1)).card + 1 := by
  simp only [hostDemand, Encodable.encodek]

theorem image_ray_mem_ball {V : Type u} {W : Type v}
    (p : Population V Label) (H : LocallyFiniteHost W)
    (m : V → ℕ) (hm : ∀ x, 0 < m x)
    (ray : ℕ → V) (hr : ∀ k, ∃ b, p.edge (ray k) (ray (k+1)) b)
    (f : Fibre V m → W) (he : PreservesEdges (blowUp p m hm) H f) (k : ℕ) :
    f (section0 m hm (ray k)) ∈ H.ball (f (section0 m hm (ray 0))) k := by
  induction k with
  | zero => exact H.mem_ball_zero _
  | succ k ih =>
    obtain ⟨b,hb⟩ := hr k
    exact H.step_mem_ball ih (he _ _ b hb)

theorem image_fibre_mem_ball {V : Type u} {W : Type v}
    (p : Population V Label) (H : LocallyFiniteHost W)
    (m : V → ℕ) (hm : ∀ x, 0 < m x)
    (ray : ℕ → V) (hr : ∀ k, ∃ b, p.edge (ray k) (ray (k+1)) b)
    (f : Fibre V m → W) (he : PreservesEdges (blowUp p m hm) H f)
    (k : ℕ) (i : Fin (m (ray (k+1)))) :
    f ⟨ray (k+1),i⟩ ∈ H.ball (f (section0 m hm (ray 0))) (k+1) := by
  obtain ⟨b,hb⟩ := hr k
  exact H.step_mem_ball (image_ray_mem_ball p H m hm ray hr f he k)
    (he (section0 m hm (ray k)) ⟨ray (k+1),i⟩ b hb)

/-- Complete nonuniversality theorem, including construction of an actual
real-birthdate population and equality of every infinite word language over the original label type.
The abstract host may even be directed; an undirected graph is a special case.
No symmetry, label preservation, nonedge preservation or root preservation
is required of the forbidden injective map. -/
theorem no_countable_host_family {V : Type u} (p : Population V Label)
    (W : ℕ → Type v) [∀ j, Encodable (W j)]
    (H : ∀ j, LocallyFiniteHost (W j)) :
    ∃ (m : V → ℕ) (hm : ∀ x, 0 < m x),
      (∀ x, (∀ y b, ¬ p.edge y x b) → m x = 1) ∧
      (∀ s, Realizes (blowUp p m hm) s ↔ Realizes p s) ∧
      ∀ j (f : Fibre V m → W j),
        Function.Injective f → ¬ PreservesEdges (blowUp p m hm) (H j) f := by
  classical
  obtain ⟨ray, hinj, hr⟩ := exists_ray p
  let m := rayMultiplicity ray (hostDemand W H)
  have hm : ∀ x, 0 < m x := rayMultiplicity_pos ray _ (hostDemand_pos W H)
  refine ⟨m, hm, ?_, fun s => blowUp_language p m hm s, ?_⟩
  · exact fun x hx => rayMultiplicity_root p ray hr _ x hx
  · intro j f hf he
    let start := f (section0 m hm (ray 0))
    let k := Encodable.encode (⟨j,start⟩ : Σ j, W j)
    have hsize : m (ray (k+1)) = ((H j).ball start (k+1)).card + 1 := by
      rw [show m (ray (k+1)) = hostDemand W H k from rayMultiplicity_at ray hinj _ k]
      exact hostDemand_encode W H j start
    let embed : Fin (m (ray (k+1))) → ↥((H j).ball start (k+1)) := fun i =>
      ⟨f ⟨ray (k+1),i⟩, image_fibre_mem_ball p (H j) m hm ray hr f he k i⟩
    have h_embed : Function.Injective embed := by
      intro a b hab
      have hs : (⟨ray (k+1),a⟩ : Fibre V m) = ⟨ray (k+1),b⟩ :=
        hf (congrArg Subtype.val hab)
      exact eq_of_heq (Sigma.mk.inj hs).2
    have hcard := Fintype.card_le_of_injective embed h_embed
    simp only [Fintype.card_fin, Fintype.card_coe] at hcard
    omega

noncomputable def populationHost {V : Type u} (p : Population V Label) :
    LocallyFiniteHost V where
  adjacent := fun x y => (∃ b, p.edge x y b) ∨ (∃ b, p.edge y x b)
  neighbours_finite := by
    intro x
    have hc := (finiteCover_iff_setFinite _).mp (p.children x)
    have hp : Set.Finite {y | ∃ b, p.edge y x b} := by
      apply ((finiteCover_iff_setFinite _).mp (p.sublevels (p.birth x))).subset
      intro y hy
      obtain ⟨b, hb⟩ := hy
      exact le_of_lt (p.chronological y x b hb)
    exact hc.union hp

@[instance_reducible]
noncomputable def populationEncodable {V : Type u} (p : Population V Label) :
    Encodable V := Encodable.ofLeftInverse p.enumeration.index p.enumeration.toFun
      p.enumeration.toFun_index

/-- Every candidate family consists of actual Alexander populations: its
countability and local finiteness are derived, not additional assumptions. -/
theorem no_countable_population_family {V : Type u} (p : Population V Label)
    (W : ℕ → Type v) (hosts : ∀ j, Population (W j) Label) :
    ∃ (m : V → ℕ) (hm : ∀ x, 0 < m x),
      (∀ x, (∀ y b, ¬ p.edge y x b) → m x = 1) ∧
      (∀ s, Realizes (blowUp p m hm) s ↔ Realizes p s) ∧
      ∀ j (f : Fibre V m → W j), Function.Injective f →
        ¬ PreservesEdges (blowUp p m hm) (populationHost (hosts j)) f := by
  let _ : ∀ j, Encodable (W j) := fun j => populationEncodable (hosts j)
  exact no_countable_host_family p W (fun j => populationHost (hosts j))

/-- Source-question specialization. The produced population avoids the same
specified sequence and embeds into none of the candidate populations, even
when all directions and labels are forgotten in the host. -/
theorem avoiding_no_countable_population_family {V : Type u}
    (p : Population V Label) (s : ℕ → Label) (ha : ¬ Realizes p s)
    (W : ℕ → Type v) (hosts : ∀ j, Population (W j) Label) :
    ∃ (m : V → ℕ) (hm : ∀ x, 0 < m x),
      (¬ Realizes (blowUp p m hm) s) ∧
      (∀ t, Realizes (blowUp p m hm) t ↔ Realizes p t) ∧
      (∀ x, (∀ y b, ¬ p.edge y x b) → m x = 1) ∧
      ∀ j (f : Fibre V m → W j), Function.Injective f →
        ¬ PreservesEdges (blowUp p m hm) (populationHost (hosts j)) f := by
  obtain ⟨m, hm, hroot, hlang, hno⟩ := no_countable_population_family p W hosts
  exact ⟨m, hm, fun h => ha ((hlang s).mp h), hlang, hroot, hno⟩


/-- The root projection is a genuine equivalence, not merely a finite-cover
claim, whenever root fibres are singletons. -/
def rootsEquiv {V : Type u} (p : Population V Label) (m : V → ℕ)
    (hm : ∀ x, 0 < m x)
    (hroot : ∀ x, (∀ y b, ¬ p.edge y x b) → m x = 1) :
    {x : Fibre V m // ∀ y b, ¬ (blowUp p m hm).edge y x b} ≃
      {x : V // ∀ y b, ¬ p.edge y x b} where
  toFun := fun x => ⟨x.1.1, (lifted_root_iff p m hm x.1).mp x.2⟩
  invFun := fun x => ⟨section0 m hm x.1,
    (lifted_root_iff p m hm (section0 m hm x.1)).mpr x.2⟩
  left_inv := by
    rintro ⟨⟨x,i⟩, hx⟩
    apply Subtype.ext
    have hr := (lifted_root_iff p m hm ⟨x,i⟩).mp hx
    have hz : i.val = 0 := by
      have hb := i.isLt
      have hb1 := hroot x hr
      omega
    have hi : i = (⟨0,hm x⟩ : Fin (m x)) := Fin.ext hz
    cases hi
    rfl
  right_inv := fun x => Subtype.ext rfl


/-- The L-step graph power uses the explicitly defined finite balls. -/
noncomputable def LocallyFiniteHost.power {W : Type v}
    (H : LocallyFiniteHost W) (L : ℕ) : LocallyFiniteHost W where
  adjacent := fun x y => y ∈ H.ball x L
  neighbours_finite := fun x => (H.ball x L).finite_toSet

/-- No single Q produced here has an injective finite-global-stretch map
into any listed host. The stretch bound is allowed to depend on the map. -/
theorem no_countable_bounded_stretch_family {V : Type u}
    (p : Population V Label) (W : ℕ → Type v)
    [∀ j, Encodable (W j)] (H : ∀ j, LocallyFiniteHost (W j)) :
    ∃ (m : V → ℕ) (hm : ∀ x, 0 < m x),
      (∀ x, (∀ y b, ¬ p.edge y x b) → m x = 1) ∧
      (∀ s, Realizes (blowUp p m hm) s ↔ Realizes p s) ∧
      ∀ j L (f : Fibre V m → W j), Function.Injective f →
        ¬ PreservesEdges (blowUp p m hm) ((H j).power L) f := by
  let W' : ℕ → Type v := fun k => W (Nat.unpair k).1
  let H' : ∀ k, LocallyFiniteHost (W' k) := fun k =>
    (H (Nat.unpair k).1).power (Nat.unpair k).2
  let _ : ∀ k, Encodable (W' k) := fun _ => inferInstance
  obtain ⟨m, hm, hr, hl, hn⟩ := no_countable_host_family p W' H'
  refine ⟨m, hm, hr, hl, ?_⟩
  intro j L
  have h := hn (Nat.pair j L)
  dsimp only [W', H'] at h
  rw [Nat.unpair_pair] at h
  exact h

/-- The same finite-stretch obstruction for a countable family of actual
populations, deriving all countability and local-finiteness hypotheses. -/
theorem avoiding_no_countable_bounded_stretch_population_family {V : Type u}
    (p : Population V Label) (s : ℕ → Label) (ha : ¬ Realizes p s)
    (W : ℕ → Type v) (hosts : ∀ j, Population (W j) Label) :
    ∃ (m : V → ℕ) (hm : ∀ x, 0 < m x),
      (¬ Realizes (blowUp p m hm) s) ∧
      (∀ t, Realizes (blowUp p m hm) t ↔ Realizes p t) ∧
      (∀ x, (∀ y b, ¬ p.edge y x b) → m x = 1) ∧
      ∀ j L (f : Fibre V m → W j), Function.Injective f →
        ¬ PreservesEdges (blowUp p m hm)
          ((populationHost (hosts j)).power L) f := by
  let _ : ∀ j, Encodable (W j) := fun j => populationEncodable (hosts j)
  obtain ⟨m, hm, hr, hl, hn⟩ := no_countable_bounded_stretch_family p W
    (fun j => populationHost (hosts j))
  exact ⟨m, hm, fun h => ha ((hl s).mp h), hl, hr, hn⟩

#print axioms GenericUniversalAvoiders.binaryCover
#print axioms GenericUniversalAvoiders.exists_ray
#print axioms GenericUniversalAvoiders.no_countable_bounded_stretch_family
#print axioms GenericUniversalAvoiders.avoiding_no_countable_bounded_stretch_population_family
#print axioms GenericUniversalAvoiders.rootsEquiv
#print axioms GenericUniversalAvoiders.blowUp
#print axioms GenericUniversalAvoiders.blowUp_language
#print axioms GenericUniversalAvoiders.no_countable_host_family
#print axioms GenericUniversalAvoiders.no_countable_population_family
#print axioms GenericUniversalAvoiders.avoiding_no_countable_population_family

end GenericUniversalAvoiders
