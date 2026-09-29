import GenericUniversalAvoiders

/-!
Terminal cloning strengthens the finite-fibre nonuniversality argument.
Only canonical copies have children. Every copy has exactly the original
incoming parent set, separately for every label. This uses Alexander's
permission for a vertex to have no children; it makes no claim for a subclass
requiring descendants at every vertex. No novelty or human-review claim.
-/

namespace TerminalCloneAvoiders

open GenericUniversalAvoiders

universe u v w
variable {Label : Type w}

/-- A clone has the original parents, each represented by its canonical copy. -/
def terminalEdge {V : Type u} (p : Population V Label) (m : V → ℕ)
    (x y : Fibre V m) (b : Label) : Prop :=
  x.2.val = 0 ∧ p.edge x.1 y.1 b

theorem terminal_root_iff {V : Type u} (p : Population V Label)
    (m : V → ℕ) (hm : ∀ x, 0 < m x) (y : Fibre V m) :
    (∀ x b, ¬ terminalEdge p m x y b) ↔ (∀ x b, ¬ p.edge x y.1 b) := by
  constructor
  · intro h x b he
    exact h (section0 m hm x) b ⟨rfl, he⟩
  · intro h x b he
    exact h x.1 b he.2

/-- Complete population object, with terminal noncanonical copies. -/
def terminalClone {V : Type u} (p : Population V Label) (m : V → ℕ)
    (hm : ∀ x, 0 < m x) : Population (Fibre V m) Label where
  edge := terminalEdge p m
  birth := fun x => p.birth x.1
  infinite := by
    intro xs
    obtain ⟨x, hx⟩ := p.infinite (xs.map Sigma.fst)
    refine ⟨section0 m hm x, ?_⟩
    intro hi
    apply hx
    exact List.mem_map.mpr ⟨section0 m hm x, hi, rfl⟩
  sublevels := fun r => finiteCover_fibres m _ (p.sublevels r)
  chronological := fun x y b h => p.chronological x.1 y.1 b h.2
  unique := fun x y a b ha hb => p.unique x.1 y.1 a b ha.2 hb.2
  roots := by
    obtain ⟨xs, hxs⟩ := finiteCover_fibres m _ p.roots
    exact ⟨xs, fun y hy => hxs y ((terminal_root_iff p m hm y).mp hy)⟩
  children := by
    intro x
    obtain ⟨xs, hxs⟩ := finiteCover_fibres m _ (p.children x.1)
    exact ⟨xs, fun y ⟨b, he⟩ => hxs y ⟨b, he.2⟩⟩
  parents := by
    intro y hy b
    have hn : ¬ (∀ x a, ¬ p.edge x y.1 a) := fun h =>
      hy ((terminal_root_iff p m hm y).mpr h)
    obtain ⟨x, hx⟩ := p.parents y.1 hn b
    exact ⟨section0 m hm x, rfl, hx⟩

/-- The new individuals do not generate additional descendants. -/
theorem noncanonical_has_no_children {V : Type u} (p : Population V Label)
    (m : V → ℕ) (hm : ∀ x, 0 < m x)
    (x : Fibre V m) (hx : x.2.val ≠ 0) :
    ∀ y b, ¬ (terminalClone p m hm).edge x y b := by
  intro y b he
  exact hx he.1

/-- Projection and the canonical section preserve the entire word language. -/
theorem terminalClone_language {V : Type u} (p : Population V Label)
    (m : V → ℕ) (hm : ∀ x, 0 < m x) (s : ℕ → Label) :
    Realizes (terminalClone p m hm) s ↔ Realizes p s := by
  constructor
  · rintro ⟨path, hpath⟩
    exact ⟨fun k => (path k).1, fun k => (hpath k).2⟩
  · rintro ⟨path, hpath⟩
    exact ⟨fun k => section0 m hm (path k), fun k => ⟨rfl, hpath k⟩⟩

/-- Every clone's incoming parents of a specified label are in bijection
with the original vertex's incoming parents of that label. -/
def incomingParentEquiv {V : Type u} (p : Population V Label)
    (m : V → ℕ) (hm : ∀ x, 0 < m x) (y : Fibre V m) (b : Label) :
    {x : Fibre V m // (terminalClone p m hm).edge x y b} ≃
      {x : V // p.edge x y.1 b} where
  toFun := fun x => ⟨x.1.1, x.2.2⟩
  invFun := fun x => ⟨section0 m hm x.1, rfl, x.2⟩
  left_inv := by
    rintro ⟨⟨x, i⟩, hx⟩
    apply Subtype.ext
    have hi : i = (⟨0, hm x⟩ : Fin (m x)) := Fin.ext hx.1
    cases hi
    rfl
  right_inv := fun x => Subtype.ext rfl

def ExactlyOneParentPerLabel {V : Type u} (p : Population V Label) : Prop :=
  ∀ y, ¬ (∀ x b, ¬ p.edge x y b) → ∀ b, ∃! x, p.edge x y b

theorem terminalClone_preserves_unique_parents {V : Type u}
    (p : Population V Label) (hp : ExactlyOneParentPerLabel p)
    (m : V → ℕ) (hm : ∀ x, 0 < m x) :
    ExactlyOneParentPerLabel (terminalClone p m hm) := by
  intro y hy b
  have hn : ¬ (∀ x a, ¬ p.edge x y.1 a) := fun h =>
    hy ((terminal_root_iff p m hm y).mpr h)
  obtain ⟨x, hx, huniq⟩ := hp y.1 hn b
  refine ⟨section0 m hm x, ⟨rfl, hx⟩, ?_⟩
  intro z hz
  have hfirst : z.1 = x := huniq z.1 hz.2
  rcases z with ⟨w, i⟩
  dsimp at hfirst
  subst w
  have hi : i = (⟨0, hm x⟩ : Fin (m x)) := Fin.ext hz.1
  cases hi
  rfl

/-- A genuine equivalence of actual biological root sets. -/
def rootsEquiv {V : Type u} (p : Population V Label) (m : V → ℕ)
    (hm : ∀ x, 0 < m x)
    (hroot : ∀ x, (∀ y b, ¬ p.edge y x b) → m x = 1) :
    {x : Fibre V m // ∀ y b, ¬ (terminalClone p m hm).edge y x b} ≃
      {x : V // ∀ y b, ¬ p.edge y x b} where
  toFun := fun x => ⟨x.1.1, (terminal_root_iff p m hm x.1).mp x.2⟩
  invFun := fun x => ⟨section0 m hm x.1,
    (terminal_root_iff p m hm (section0 m hm x.1)).mpr x.2⟩
  left_inv := by
    rintro ⟨⟨x, i⟩, hx⟩
    apply Subtype.ext
    have hr := (terminal_root_iff p m hm ⟨x, i⟩).mp hx
    have hz : i.val = 0 := by
      have hb := i.isLt
      have hb1 := hroot x hr
      omega
    have hi : i = (⟨0, hm x⟩ : Fin (m x)) := Fin.ext hz
    cases hi
    rfl
  right_inv := fun x => Subtype.ext rfl

theorem image_ray_mem_ball {V : Type u} {W : Type v}
    (p : Population V Label) (H : LocallyFiniteHost W)
    (m : V → ℕ) (hm : ∀ x, 0 < m x)
    (ray : ℕ → V) (hr : ∀ k, ∃ b, p.edge (ray k) (ray (k+1)) b)
    (f : Fibre V m → W) (he : PreservesEdges (terminalClone p m hm) H f) (k : ℕ) :
    f (section0 m hm (ray k)) ∈ H.ball (f (section0 m hm (ray 0))) k := by
  induction k with
  | zero => exact H.mem_ball_zero _
  | succ k ih =>
    obtain ⟨b, hb⟩ := hr k
    exact H.step_mem_ball ih (he _ _ b ⟨rfl, hb⟩)

theorem image_fibre_mem_ball {V : Type u} {W : Type v}
    (p : Population V Label) (H : LocallyFiniteHost W)
    (m : V → ℕ) (hm : ∀ x, 0 < m x)
    (ray : ℕ → V) (hr : ∀ k, ∃ b, p.edge (ray k) (ray (k+1)) b)
    (f : Fibre V m → W) (he : PreservesEdges (terminalClone p m hm) H f)
    (k : ℕ) (i : Fin (m (ray (k+1)))) :
    f ⟨ray (k+1), i⟩ ∈ H.ball (f (section0 m hm (ray 0))) (k+1) := by
  obtain ⟨b, hb⟩ := hr k
  exact H.step_mem_ball (image_ray_mem_ball p H m hm ray hr f he k)
    (he (section0 m hm (ray k)) ⟨ray (k+1), i⟩ b ⟨rfl, hb⟩)

/-- Same diagonal obstruction, with exact incoming parent sets preserved. -/
theorem no_countable_host_family {V : Type u} (p : Population V Label)
    (W : ℕ → Type v) [∀ j, Encodable (W j)]
    (H : ∀ j, LocallyFiniteHost (W j)) :
    ∃ (m : V → ℕ) (hm : ∀ x, 0 < m x),
      (∀ x, (∀ y b, ¬ p.edge y x b) → m x = 1) ∧
      (∀ s, Realizes (terminalClone p m hm) s ↔ Realizes p s) ∧
      ∀ j (f : Fibre V m → W j),
        Function.Injective f → ¬ PreservesEdges (terminalClone p m hm) (H j) f := by
  classical
  obtain ⟨ray, hinj, hr⟩ := exists_ray p
  let m := rayMultiplicity ray (hostDemand W H)
  have hm : ∀ x, 0 < m x := rayMultiplicity_pos ray _ (hostDemand_pos W H)
  refine ⟨m, hm, ?_, fun s => terminalClone_language p m hm s, ?_⟩
  · exact fun x hx => rayMultiplicity_root p ray hr _ x hx
  · intro j f hf he
    let start := f (section0 m hm (ray 0))
    let k := Encodable.encode (⟨j, start⟩ : Σ j, W j)
    have hsize : m (ray (k+1)) = ((H j).ball start (k+1)).card + 1 := by
      rw [show m (ray (k+1)) = hostDemand W H k from rayMultiplicity_at ray hinj _ k]
      exact hostDemand_encode W H j start
    let embed : Fin (m (ray (k+1))) → ↥((H j).ball start (k+1)) := fun i =>
      ⟨f ⟨ray (k+1), i⟩, image_fibre_mem_ball p (H j) m hm ray hr f he k i⟩
    have h_embed : Function.Injective embed := by
      intro a b hab
      have hs : (⟨ray (k+1), a⟩ : Fibre V m) = ⟨ray (k+1), b⟩ :=
        hf (congrArg Subtype.val hab)
      exact eq_of_heq (Sigma.mk.inj hs).2
    have hcard := Fintype.card_le_of_injective embed h_embed
    simp only [Fintype.card_fin, Fintype.card_coe] at hcard
    omega

/-- One terminal-clone population defeats every finite global stretch
bound, even when the bound varies with the map. -/
theorem no_countable_bounded_stretch_family {V : Type u}
    (p : Population V Label) (W : ℕ → Type v)
    [∀ j, Encodable (W j)] (H : ∀ j, LocallyFiniteHost (W j)) :
    ∃ (m : V → ℕ) (hm : ∀ x, 0 < m x),
      (∀ x, (∀ y b, ¬ p.edge y x b) → m x = 1) ∧
      (∀ s, Realizes (terminalClone p m hm) s ↔ Realizes p s) ∧
      ∀ j L (f : Fibre V m → W j), Function.Injective f →
        ¬ PreservesEdges (terminalClone p m hm) ((H j).power L) f := by
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

/-- In particular: no countable finite-stretch universal family even within
the subclass with exactly one parent of every label at every nonroot,
provided this subclass contains the supplied avoiding population. -/
theorem avoiding_no_countable_exact_parent_bounded_stretch_population_family
    {V : Type u} (p : Population V Label) (hp : ExactlyOneParentPerLabel p)
    (s : ℕ → Label) (ha : ¬ Realizes p s)
    (W : ℕ → Type v) (hosts : ∀ j, Population (W j) Label) :
    ∃ (m : V → ℕ) (hm : ∀ x, 0 < m x),
      (¬ Realizes (terminalClone p m hm) s) ∧
      (∀ t, Realizes (terminalClone p m hm) t ↔ Realizes p t) ∧
      (∀ x, (∀ y b, ¬ p.edge y x b) → m x = 1) ∧
      ExactlyOneParentPerLabel (terminalClone p m hm) ∧
      ∀ j L (f : Fibre V m → W j), Function.Injective f →
        ¬ PreservesEdges (terminalClone p m hm)
          ((populationHost (hosts j)).power L) f := by
  let _ : ∀ j, Encodable (W j) := fun j => populationEncodable (hosts j)
  obtain ⟨m, hm, hr, hl, hn⟩ := no_countable_bounded_stretch_family p W
    (fun j => populationHost (hosts j))
  exact ⟨m, hm, fun h => ha ((hl s).mp h), hl, hr,
    terminalClone_preserves_unique_parents p hp m hm, hn⟩


/-- Choose one original parent of each label at every original nonroot. -/
noncomputable def chosenParent {V : Type u} (p : Population V Label)
    (y : V) (hy : ¬ (∀ x b, ¬ p.edge x y b)) (b : Label) : V :=
  Classical.choose (p.parents y hy b)

theorem chosenParent_edge {V : Type u} (p : Population V Label)
    (y : V) (hy : ¬ (∀ x b, ¬ p.edge x y b)) (b : Label) :
    p.edge (chosenParent p y hy b) y b :=
  Classical.choose_spec (p.parents y hy b)

def selectedEdge {V : Type u} (p : Population V Label) (x y : V) (b : Label) :
    Prop :=
  ∃ hy : ¬ (∀ z a, ¬ p.edge z y a), x = chosenParent p y hy b

theorem selected_edge_sub {V : Type u} (p : Population V Label)
    {x y : V} {b : Label} (he : selectedEdge p x y b) : p.edge x y b := by
  rcases he with ⟨hy, rfl⟩
  exact chosenParent_edge p y hy b

theorem selected_root_iff {V : Type u} (p : Population V Label) (y : V) :
    (∀ x b, ¬ selectedEdge p x y b) ↔ (∀ x b, ¬ p.edge x y b) := by
  constructor
  · intro hy x b hxy
    have hn : ¬ (∀ z a, ¬ p.edge z y a) := fun h => h x b hxy
    exact hy (chosenParent p y hn b) b ⟨hn, rfl⟩
  · intro hy x b he
    exact hy x b (selected_edge_sub p he)

/-- Deleting all but one parent per label preserves the population axioms
and the actual root set. It can shrink the infinite word language. -/
def selectParents {V : Type u} (p : Population V Label) : Population V Label where
  edge := selectedEdge p
  birth := p.birth
  infinite := p.infinite
  sublevels := p.sublevels
  chronological := fun x y b he => p.chronological x y b (selected_edge_sub p he)
  unique := fun x y a b ha hb => p.unique x y a b
    (selected_edge_sub p ha) (selected_edge_sub p hb)
  roots := by
    obtain ⟨xs, hxs⟩ := p.roots
    exact ⟨xs, fun y hy => hxs y ((selected_root_iff p y).mp hy)⟩
  children := by
    intro x
    obtain ⟨xs, hxs⟩ := p.children x
    exact ⟨xs, fun y ⟨b, he⟩ => hxs y ⟨b, selected_edge_sub p he⟩⟩
  parents := by
    intro y hy b
    have hn : ¬ (∀ x a, ¬ p.edge x y a) := fun h =>
      hy ((selected_root_iff p y).mpr h)
    exact ⟨chosenParent p y hn b, hn, rfl⟩

theorem selectParents_exact {V : Type u} (p : Population V Label) :
    ExactlyOneParentPerLabel (selectParents p) := by
  intro y hy b
  have hn : ¬ (∀ x a, ¬ p.edge x y a) := fun h =>
    hy ((selected_root_iff p y).mpr h)
  refine ⟨chosenParent p y hn b, ⟨hn, rfl⟩, ?_⟩
  intro x hx
  rcases hx with ⟨_, hx⟩
  exact hx

theorem selectParents_realizes {V : Type u} (p : Population V Label)
    (s : ℕ → Label) (hs : Realizes (selectParents p) s) : Realizes p s := by
  rcases hs with ⟨path, hpath⟩
  exact ⟨path, fun k => selected_edge_sub p (hpath k)⟩

/-- Parent selection preserves roothood pointwise, on the same vertex type. -/
theorem selectParents_root_iff {V : Type u} (p : Population V Label) (y : V) :
    (∀ x b, ¬ (selectParents p).edge x y b) ↔
      (∀ x b, ¬ p.edge x y b) :=
  selected_root_iff p y

/-- Root equivalence for parent selection on the original vertex type. -/
def selectParents_rootsEquiv {V : Type u} (p : Population V Label) :
    {x : V // ∀ y b, ¬ (selectParents p).edge y x b} ≃
      {x : V // ∀ y b, ¬ p.edge y x b} where
  toFun := fun x => ⟨x.1, (selectParents_root_iff p x.1).mp x.2⟩
  invFun := fun x => ⟨x.1, (selectParents_root_iff p x.1).mpr x.2⟩
  left_inv := fun _ => Subtype.ext rfl
  right_inv := fun _ => Subtype.ext rfl

/-- The combined selection-and-cloning construction has the original
actual biological root set, via a canonical equivalence. -/
def selectedClone_rootsEquiv {V : Type u} (p : Population V Label)
    (m : V → ℕ) (hm : ∀ x, 0 < m x)
    (hroot : ∀ x, (∀ y b, ¬ p.edge y x b) → m x = 1) :
    {x : Fibre V m //
      ∀ y b, ¬ (terminalClone (selectParents p) m hm).edge y x b} ≃
      {x : V // ∀ y b, ¬ p.edge y x b} :=
  (rootsEquiv (selectParents p) m hm
    (fun x hx => hroot x ((selectParents_root_iff p x).mp hx))).trans
      (selectParents_rootsEquiv p)

/-- Every supplied avoiding population yields an exact-parent avoiding
population defeating every countable population family at every finite
global stretch bound. No hypothesis on the original parent counts is added.
Language inclusion (not equality with the original population) is asserted. -/
theorem avoiding_no_countable_exact_parent_family_from_any_population
    {V : Type u} (p : Population V Label)
    (s : ℕ → Label) (ha : ¬ Realizes p s)
    (W : ℕ → Type v) (hosts : ∀ j, Population (W j) Label) :
    ∃ (m : V → ℕ) (hm : ∀ x, 0 < m x),
      (¬ Realizes (terminalClone (selectParents p) m hm) s) ∧
      (∀ t, Realizes (terminalClone (selectParents p) m hm) t → Realizes p t) ∧
      (∀ x, (∀ y b, ¬ p.edge y x b) → m x = 1) ∧
      ExactlyOneParentPerLabel (terminalClone (selectParents p) m hm) ∧
      ∀ j L (f : Fibre V m → W j), Function.Injective f →
        ¬ PreservesEdges (terminalClone (selectParents p) m hm)
          ((populationHost (hosts j)).power L) f := by
  obtain ⟨m, hm, havoid, hlang, hroot, hparent, hno⟩ :=
    avoiding_no_countable_exact_parent_bounded_stretch_population_family
      (selectParents p) (selectParents_exact p) s
      (fun hs => ha (selectParents_realizes p s hs)) W hosts
  refine ⟨m, hm, havoid, ?_, ?_, hparent, hno⟩
  · intro t ht
    exact selectParents_realizes p t ((hlang t).mp ht)
  · intro x hx
    exact hroot x ((selectParents_root_iff p x).mpr hx)


#print axioms TerminalCloneAvoiders.terminalClone
#print axioms TerminalCloneAvoiders.noncanonical_has_no_children
#print axioms TerminalCloneAvoiders.terminalClone_language
#print axioms TerminalCloneAvoiders.incomingParentEquiv
#print axioms TerminalCloneAvoiders.terminalClone_preserves_unique_parents
#print axioms TerminalCloneAvoiders.rootsEquiv
#print axioms TerminalCloneAvoiders.no_countable_host_family
#print axioms TerminalCloneAvoiders.no_countable_bounded_stretch_family
#print axioms TerminalCloneAvoiders.avoiding_no_countable_exact_parent_bounded_stretch_population_family

#print axioms TerminalCloneAvoiders.selectParents
#print axioms TerminalCloneAvoiders.selectParents_exact
#print axioms TerminalCloneAvoiders.selectParents_realizes
#print axioms TerminalCloneAvoiders.selectParents_rootsEquiv
#print axioms TerminalCloneAvoiders.selectedClone_rootsEquiv
#print axioms TerminalCloneAvoiders.selectParents_root_iff
#print axioms TerminalCloneAvoiders.avoiding_no_countable_exact_parent_family_from_any_population

end TerminalCloneAvoiders

