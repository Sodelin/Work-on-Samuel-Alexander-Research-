import FiniteGenomeIdentifiability
import SamuelAlexanderResearch.ObservationPrediction
import SamuelAlexanderResearch.ProductiveCore

/-!
# What an owner projection can transfer from genomic history to a pedigree

The owner map and its biological interpretation are supplied, not inferred.
Genomic paths can collapse within one organism or span several generations.
The existing `HistoryProjection` theorem supplies that sound direction.

The new transfer result concerns a possibly infinite rich history on `Nat`.
It needs finite owner fibres, surjectivity, and ancestry reflection away from
one owner fibre. Those are substantial additional assumptions. A finite
sampled `WongGARG.GARG` cannot cover an infinite Alexander biosphere.

These are elementary deductions and counterexamples from the stated
interfaces, not a novelty claim or a biological species classifier.
-/

namespace WongPedigreeBridge

open SpeciesBridge SpeciesGlobalIAP HistoryProjection FiniteHistoryCompletion

/-- The complete candidate represented by all rich-history nodes of its owners. -/
def Pull (owner : Nat → Nat) (S : NatSet) : NatSet := fun a => S (owner a)

/-- A diploid genome model can have finitely many copies per organism; a
cell-level model must justify this condition separately. -/
def FiniteFibres (owner : Nat → Nat) : Prop :=
  ∀ v, FiniteSupport (fun a => owner a = v)

/-- Exact strict ancestry between distinct organisms, for every pair of
representatives. This is much stronger than sound genetic inheritance. -/
def AncestryExactAwayFromFibres (owner : Nat → Nat) (R E : Graph) : Prop :=
  ∀ a b, owner a ≠ owner b →
    (Descendant R a b ↔ Descendant E (owner a) (owner b))

/-- Soundness includes possible collapse of cell-level ancestry. -/
def PathSound (owner : Nat → Nat) (R E : Graph) : Prop :=
  ∀ a b, Descendant R a b → SameOrDescendant E (owner a) (owner b)

theorem pathSound_of_faithful (owner : Nat → Nat) {R E : Graph}
    (faithful : AncestryExactAwayFromFibres owner R E) : PathSound owner R E := by
  classical
  intro a b path
  by_cases same : owner a = owner b
  · exact Or.inl same
  · exact Or.inr ((faithful a b same).mp path)

theorem finiteSupport_preimage (owner : Nat → Nat) (fibres : FiniteFibres owner)
    {S : NatSet} (finite : FiniteSupport S) : FiniteSupport (Pull owner S) := by
  classical
  obtain ⟨xs, hxs⟩ := finite
  let cover : Nat → List Nat := fun v => Classical.choose (fibres v)
  have covers (v a : Nat) (ha : owner a = v) : a ∈ cover v :=
    Classical.choose_spec (fibres v) a ha
  refine ⟨xs.flatMap cover, ?_⟩
  intro a ha
  exact List.mem_flatMap.mpr ⟨owner a, hxs _ ha, covers _ _ rfl⟩

theorem finiteSupport_of_preimage (owner : Nat → Nat)
    (onto : Function.Surjective owner) {S : NatSet}
    (finite : FiniteSupport (Pull owner S)) : FiniteSupport S := by
  obtain ⟨xs, hxs⟩ := finite
  refine ⟨xs.map owner, ?_⟩
  intro v hv
  obtain ⟨a, rfl⟩ := onto v
  exact List.mem_map.mpr ⟨a, hxs a hv, rfl⟩

theorem finiteSupport_preimage_iff (owner : Nat → Nat)
    (onto : Function.Surjective owner) (fibres : FiniteFibres owner) (S : NatSet) :
    FiniteSupport (Pull owner S) ↔ FiniteSupport S :=
  ⟨finiteSupport_of_preimage owner onto, finiteSupport_preimage owner fibres⟩

theorem infiniteSupport_preimage_iff (owner : Nat → Nat)
    (onto : Function.Surjective owner) (fibres : FiniteFibres owner) (S : NatSet) :
    InfiniteSupport (Pull owner S) ↔ InfiniteSupport S :=
  not_congr (finiteSupport_preimage_iff owner onto fibres S)

/-- Finite changes in membership do not change finiteness. -/
theorem finiteSupport_iff_off_finite {A B Bad : NatSet}
    (finiteBad : FiniteSupport Bad)
    (agree : ∀ b, ¬ Bad b → (A b ↔ B b)) :
    FiniteSupport A ↔ FiniteSupport B := by
  classical
  constructor
  · intro finiteA
    apply finiteSupport_mono (T := fun b => A b ∨ Bad b) ?_
      (finiteSupport_union finiteA finiteBad)
    intro b hb
    by_cases bad : Bad b
    · exact Or.inr bad
    · exact Or.inl ((agree b bad).mpr hb)
  · intro finiteB
    apply finiteSupport_mono (T := fun b => B b ∨ Bad b) ?_
      (finiteSupport_union finiteB finiteBad)
    intro b hb
    by_cases bad : Bad b
    · exact Or.inr bad
    · exact Or.inl ((agree b bad).mp hb)

theorem finite_descendants_iff (owner : Nat → Nat) {R E : Graph}
    (onto : Function.Surjective owner) (fibres : FiniteFibres owner)
    (faithful : AncestryExactAwayFromFibres owner R E) (S : NatSet) (a : Nat) :
    FiniteSupport (fun b => Pull owner S b ∧ Descendant R a b) ↔
      FiniteSupport (fun v => S v ∧ Descendant E (owner a) v) := by
  apply Iff.trans ?_ (finiteSupport_preimage_iff owner onto fibres _)
  apply finiteSupport_iff_off_finite (fibres (owner a))
  intro b different
  exact and_congr Iff.rfl (faithful a b (Ne.symm different))

theorem finite_nondescendants_iff (owner : Nat → Nat) {R E : Graph}
    (onto : Function.Surjective owner) (fibres : FiniteFibres owner)
    (faithful : AncestryExactAwayFromFibres owner R E) (S : NatSet) (a : Nat) :
    FiniteSupport (fun b => Pull owner S b ∧ ¬ Descendant R a b) ↔
      FiniteSupport (fun v => S v ∧ ¬ Descendant E (owner a) v) := by
  apply Iff.trans ?_ (finiteSupport_preimage_iff owner onto fibres _)
  apply finiteSupport_iff_off_finite (fibres (owner a))
  intro b different
  exact and_congr Iff.rfl (not_congr (faithful a b (Ne.symm different)))

/-- IAP is invariant under a finite-to-one, onto owner projection when strict
ancestry is exact outside each finite owner fibre. No uniform fibre bound is needed. -/
theorem iap_iff (owner : Nat → Nat) {R E : Graph}
    (onto : Function.Surjective owner) (fibres : FiniteFibres owner)
    (faithful : AncestryExactAwayFromFibres owner R E) (S : NatSet) :
    IAP R (Pull owner S) ↔ IAP E S := by
  constructor
  · intro h v hv
    obtain ⟨a, rfl⟩ := onto v
    rcases h a hv with hd | hn
    · exact Or.inl ((finite_descendants_iff owner onto fibres faithful S a).mp hd)
    · exact Or.inr ((finite_nondescendants_iff owner onto fibres faithful S a).mp hn)
  · intro h a ha
    rcases h (owner a) ha with hd | hn
    · exact Or.inl ((finite_descendants_iff owner onto fibres faithful S a).mpr hd)
    · exact Or.inr ((finite_nondescendants_iff owner onto fibres faithful S a).mpr hn)

/-- Alexander's REF compares global and internal infinitude. Both comparisons
survive the same finite-fibre ancestry correspondence. -/
theorem reflection_iff (owner : Nat → Nat) {R E : Graph}
    (onto : Function.Surjective owner) (fibres : FiniteFibres owner)
    (faithful : AncestryExactAwayFromFibres owner R E) (S : NatSet) :
    Reflection R (Pull owner S) ↔ Reflection E S := by
  have global (a : Nat) :
      InfiniteSupport (Descendant R a) ↔
        InfiniteSupport (Descendant E (owner a)) := by
    simpa only [InfiniteSupport, Pull, Whole, true_and] using
      not_congr (finite_descendants_iff owner onto fibres faithful Whole a)
  have internal (a : Nat) :
      InfiniteSupport (fun b => Pull owner S b ∧ Descendant R a b) ↔
        InfiniteSupport (fun v => S v ∧ Descendant E (owner a) v) :=
    not_congr (finite_descendants_iff owner onto fibres faithful S a)
  constructor
  · intro h v hv infinite
    obtain ⟨a, rfl⟩ := onto v
    exact (internal a).mp (h a hv ((global a).mpr infinite))
  · intro h a ha infinite
    exact (internal a).mpr (h (owner a) ha ((global a).mp infinite))

/-- A rich-history common ancestor gives a pedigree common ancestor under
sound projection and surjectivity alone. Its own fibre need not collapse to
a directed path, so this theorem deliberately states only descent. -/
theorem commonAncestor_descends (owner : Nat → Nat) {R E : Graph}
    (onto : Function.Surjective owner) (sound : PathSound owner R E)
    {S : NatSet} (ancestor : CommonAncestor R (Pull owner S)) :
    CommonAncestor E S := by
  obtain ⟨a, ha, ancestor⟩ := ancestor
  refine ⟨owner a, ha, ?_⟩
  intro v hv different
  obtain ⟨b, rfl⟩ := onto v
  have differentNodes : b ≠ a := by
    intro same
    exact different (congrArg owner same)
  rcases sound a b (ancestor b hv differentNodes) with same | path
  · exact False.elim (different same.symm)
  · exact path

/-- Convexity pulls back even when genomic paths collapse within organisms. -/
theorem convex_pullback (owner : Nat → Nat) {R E : Graph}
    (sound : PathSound owner R E) {S : NatSet} (convex : Convex E S) :
    Convex R (Pull owner S) := by
  intro b hab hbd
  obtain ⟨a, ha, ab⟩ := hab
  obtain ⟨d, hd, bd⟩ := hbd
  rcases sound a b ab with same | ab'
  · change S (owner b)
    exact same ▸ ha
  · rcases sound b d bd with same | bd'
    · change S (owner b)
      exact same.symm ▸ hd
    · exact convex _ ⟨owner a, ha, ab'⟩ ⟨owner d, hd, bd'⟩

/-- Reflection of all between-owner paths and an onto owner map allow
convexity to descend. Target acyclicity makes strict ancestry distinct. -/
theorem convex_descends (owner : Nat → Nat) {R E : Graph}
    (onto : Function.Surjective owner)
    (faithful : AncestryExactAwayFromFibres owner R E)
    (acyclic : ∀ v, ¬ Descendant E v v) {S : NatSet}
    (convex : Convex R (Pull owner S)) : Convex E S := by
  intro v hav hvd
  obtain ⟨a, ha, av⟩ := hav
  obtain ⟨d, hd, vd⟩ := hvd
  obtain ⟨x, rfl⟩ := onto a
  obtain ⟨y, rfl⟩ := onto v
  obtain ⟨z, rfl⟩ := onto d
  have xy : owner x ≠ owner y := by
    intro h
    exact acyclic (owner y) (h ▸ av)
  have yz : owner y ≠ owner z := by
    intro h
    exact acyclic (owner z) (h ▸ vd)
  exact convex y ⟨x, ha, (faithful x y xy).mpr av⟩
    ⟨z, hd, (faithful y z yz).mpr vd⟩

theorem convex_iff (owner : Nat → Nat) {R E : Graph}
    (onto : Function.Surjective owner)
    (faithful : AncestryExactAwayFromFibres owner R E)
    (acyclic : ∀ v, ¬ Descendant E v v)
    (S : NatSet) : Convex R (Pull owner S) ↔ Convex E S :=
  ⟨convex_descends owner onto faithful acyclic,
    convex_pullback owner (pathSound_of_faithful owner faithful)⟩

theorem weakReach_projects (owner : Nat → Nat) {R E : Graph}
    (sound : PathSound owner R E) {S : NatSet} (convex : Convex E S)
    {a b : Nat} (path : WeakReach R (Pull owner S) a b) :
    WeakReach E S (owner a) (owner b) := by
  induction path with
  | refl ha => exact .refl ha
  | @edge a b ha hb edge =>
    rcases edge with ab | ba
    · rcases sound a b (.edge ab) with same | ab'
      · rw [← same]
        exact .refl ha
      · exact ProductiveCore.descendant_weakReach_convex convex ab' ha hb
    · rcases sound b a (.edge ba) with same | ba'
      · rw [← same]
        exact .refl hb
      · exact (ProductiveCore.descendant_weakReach_convex convex ba' hb ha).symm
  | trans _ _ ih ij => exact .trans ih ij

theorem weaklyConnected_descends (owner : Nat → Nat) {R E : Graph}
    (onto : Function.Surjective owner) (sound : PathSound owner R E)
    {S : NatSet} (convex : Convex E S)
    (connected : WeaklyConnected R (Pull owner S)) : WeaklyConnected E S := by
  refine ⟨?_, ?_⟩
  · obtain ⟨a, ha⟩ := connected.1
    exact ⟨owner a, ha⟩
  · intro v w hv hw
    obtain ⟨a, rfl⟩ := onto v
    obtain ⟨b, rfl⟩ := onto w
    exact weakReach_projects owner sound convex (connected.2 a b hv hw)

/-- A sufficient theorem for Alexander's specieslike predicate. The target
is an organism pedigree supplied independently; no biological classification
is inferred. This is descent of one saturated cluster, not maximality. -/
theorem specieslike_descends (owner : Nat → Nat) {R E : Graph}
    (onto : Function.Surjective owner) (fibres : FiniteFibres owner)
    (faithful : AncestryExactAwayFromFibres owner R E)
    (acyclic : ∀ v, ¬ Descendant E v v)
    {S : NatSet} (cluster : Specieslike R (Pull owner S)) : Specieslike E S := by
  have convex := convex_descends owner onto faithful acyclic cluster.2.2
  exact ⟨weaklyConnected_descends owner onto (pathSound_of_faithful owner faithful)
      convex cluster.1,
    (iap_iff owner onto fibres faithful S).mp cluster.2.1, convex⟩

/-- Connectedness of each fibre in its own induced rich-history graph.
Two unrelated haploid copies do not automatically satisfy this property. -/
def ConnectedFibres (owner : Nat → Nat) (R : Graph) : Prop :=
  ∀ a b, owner a = owner b → WeakReach R (fun c => owner c = owner a) a b

theorem weakReach_lifts (owner : Nat → Nat) {R E : Graph}
    (onto : Function.Surjective owner)
    (faithful : AncestryExactAwayFromFibres owner R E)
    (acyclic : ∀ v, ¬ Descendant E v v)
    (connectedFibres : ConnectedFibres owner R) {S : NatSet}
    (convex : Convex E S) {v w : Nat} (path : WeakReach E S v w) :
    ∀ a b, owner a = v → owner b = w → WeakReach R (Pull owner S) a b := by
  have richConvex := convex_pullback owner (pathSound_of_faithful owner faithful) convex
  have liftEdge (a b : Nat) (ha : S (owner a)) (hb : S (owner b))
      (edge : E (owner a) (owner b)) : WeakReach R (Pull owner S) a b := by
    have different : owner a ≠ owner b := by
      intro same
      apply acyclic (owner b)
      apply Descendant.edge
      simpa only [same] using edge
    exact ProductiveCore.descendant_weakReach_convex richConvex
      ((faithful a b different).mpr (.edge edge)) ha hb
  induction path with
  | @refl v hv =>
    intro a b qa qb
    apply ProductiveCore.weakReach_mono_set ?_
      (connectedFibres a b (qa.trans qb.symm))
    intro c hc
    change S (owner c)
    rw [hc, qa]
    exact hv
  | @edge v w hv hw edge =>
    intro a b qa qb
    have ha : S (owner a) := qa.symm ▸ hv
    have hb : S (owner b) := qb.symm ▸ hw
    rcases edge with vw | wv
    · apply liftEdge a b ha hb
      rw [qa, qb]
      exact vw
    · apply WeakReach.symm
      apply liftEdge b a hb ha
      rw [qa, qb]
      exact wv
  | @trans v middle w _ _ ihLeft ihRight =>
    intro a b qa qb
    obtain ⟨c, qc⟩ := onto middle
    exact .trans (ihLeft a c qa qc) (ihRight c b qc qb)

theorem weaklyConnected_lifts (owner : Nat → Nat) {R E : Graph}
    (onto : Function.Surjective owner)
    (faithful : AncestryExactAwayFromFibres owner R E)
    (acyclic : ∀ v, ¬ Descendant E v v)
    (connectedFibres : ConnectedFibres owner R) {S : NatSet}
    (convex : Convex E S) (connected : WeaklyConnected E S) :
    WeaklyConnected R (Pull owner S) := by
  obtain ⟨v, hv⟩ := connected.1
  obtain ⟨a, rfl⟩ := onto v
  refine ⟨⟨a, hv⟩, ?_⟩
  intro b c hb hc
  exact weakReach_lifts owner onto faithful acyclic connectedFibres convex
    (connected.2 (owner b) (owner c) hb hc) b c rfl rfl

/-- Specieslike equivalence holds on saturated sets when fibres themselves
remain connected. This is not a statement about arbitrary rich-history sets. -/
theorem specieslike_iff (owner : Nat → Nat) {R E : Graph}
    (onto : Function.Surjective owner) (fibres : FiniteFibres owner)
    (faithful : AncestryExactAwayFromFibres owner R E)
    (acyclic : ∀ v, ¬ Descendant E v v)
    (connectedFibres : ConnectedFibres owner R) (S : NatSet) :
    Specieslike R (Pull owner S) ↔ Specieslike E S := by
  constructor
  · exact specieslike_descends owner onto fibres faithful acyclic
  · intro cluster
    exact ⟨weaklyConnected_lifts owner onto faithful acyclic connectedFibres
        cluster.2.2 cluster.1,
      (iap_iff owner onto fibres faithful S).mpr cluster.2.1,
      convex_pullback owner (pathSound_of_faithful owner faithful) cluster.2.2⟩

/-- Maximality restricted to owner-saturated rich-history candidate sets. -/
def MaximalAmongSaturated (owner : Nat → Nat) (R : Graph) (S : NatSet) : Prop :=
  Specieslike R (Pull owner S) ∧ ∀ U : NatSet,
    (∀ a, Pull owner S a → Pull owner U a) → Specieslike R (Pull owner U) →
      ∀ a, Pull owner U a → Pull owner S a

theorem maximal_saturated_iff (owner : Nat → Nat) {R E : Graph}
    (onto : Function.Surjective owner) (fibres : FiniteFibres owner)
    (faithful : AncestryExactAwayFromFibres owner R E)
    (acyclic : ∀ v, ¬ Descendant E v v)
    (connectedFibres : ConnectedFibres owner R) (S : NatSet) :
    MaximalAmongSaturated owner R S ↔ MaximalSpecieslike E S := by
  have transfer := specieslike_iff owner onto fibres faithful acyclic connectedFibres
  constructor
  · intro maximal
    refine ⟨(transfer S).mp maximal.1, ?_⟩
    intro U inclusion cluster v hv
    obtain ⟨a, rfl⟩ := onto v
    exact maximal.2 U (fun b hb => inclusion (owner b) hb)
      ((transfer U).mpr cluster) a hv
  · intro maximal
    refine ⟨(transfer S).mpr maximal.1, ?_⟩
    intro U inclusion cluster a ha
    apply maximal.2 U ?_ ((transfer U).mp cluster) (owner a) ha
    intro v hv
    obtain ⟨b, rfl⟩ := onto v
    exact inclusion b hv

theorem maximalSpecieslike_descends (owner : Nat → Nat) {R E : Graph}
    (onto : Function.Surjective owner) (fibres : FiniteFibres owner)
    (faithful : AncestryExactAwayFromFibres owner R E)
    (acyclic : ∀ v, ¬ Descendant E v v)
    (connectedFibres : ConnectedFibres owner R) {S : NatSet}
    (maximal : MaximalSpecieslike R (Pull owner S)) : MaximalSpecieslike E S := by
  apply (maximal_saturated_iff owner onto fibres faithful acyclic connectedFibres S).mp
  exact ⟨maximal.1, fun U inclusion cluster => maximal.2 (Pull owner U) inclusion cluster⟩

/-- A precise robustness extension: it is the finite discrepancy in ancestry
paths for each source, not merely finitely many edited edges, that preserves IAP. -/
theorem iap_iff_of_finite_ancestry_errors {R E : Graph} {S : NatSet}
    (errors : ∀ a, S a → FiniteSupport
      (fun b => S b ∧ ¬ (Descendant R a b ↔ Descendant E a b))) :
    IAP R S ↔ IAP E S := by
  classical
  have finiteRows (a : Nat) (ha : S a) :
      (FiniteSupport (fun b => S b ∧ Descendant R a b) ↔
        FiniteSupport (fun b => S b ∧ Descendant E a b)) ∧
      (FiniteSupport (fun b => S b ∧ ¬ Descendant R a b) ↔
        FiniteSupport (fun b => S b ∧ ¬ Descendant E a b)) := by
    have agree (b : Nat) (notBad : ¬ (S b ∧
        ¬ (Descendant R a b ↔ Descendant E a b))) (hb : S b) :
        Descendant R a b ↔ Descendant E a b := by
      by_contra h
      exact notBad ⟨hb, h⟩
    constructor
    · apply finiteSupport_iff_off_finite (errors a ha)
      intro b notBad
      by_cases hb : S b
      · exact and_congr Iff.rfl (agree b notBad hb)
      · simp only [hb, false_and]
    · apply finiteSupport_iff_off_finite (errors a ha)
      intro b notBad
      by_cases hb : S b
      · exact and_congr Iff.rfl (not_congr (agree b notBad hb))
      · simp only [hb, false_and]
  constructor
  · intro h a ha
    exact (or_congr (finiteRows a ha).1 (finiteRows a ha).2).mp (h a ha)
  · intro h a ha
    exact (or_congr (finiteRows a ha).1 (finiteRows a ha).2).mpr (h a ha)

/-- An infinite, connected, birth-ordered example. The same rich history and
the same identity owner map have two sound pedigree interpretations with
opposite IAP. Thus soundness, finite fibres, onto-ness, and biosphere axioms
alone cannot identify an IAP or specieslike verdict. -/
theorem sound_projection_does_not_determine_iap :
    ∃ R A B : Graph,
      Function.Surjective (id : Nat → Nat) ∧ FiniteFibres id ∧
      NaturalDateBiosphere R ∧ NaturalDateBiosphere A ∧ NaturalDateBiosphere B ∧
      WongAlexander.RealDatedBiosphere R ∧ WongAlexander.RealDatedBiosphere A ∧
      WongAlexander.RealDatedBiosphere B ∧
      WeaklyConnected R Whole ∧
      PathSound id R A ∧ PathSound id R B ∧
      Specieslike A Whole ∧ ¬ IAP B Whole := by
  let empty : Graph := fun _ _ => False
  have ordered : OrderedPrefix empty 0 := by intro u v hu; omega
  let R : Graph := Fork empty 0
  let A : Graph := Join empty 0
  have richBiosphere : NaturalDateBiosphere R := fork_biosphere ordered
  have organismBiosphere : NaturalDateBiosphere A := join_biosphere ordered
  have soundA : PathSound id R A := by
    intro a b path
    have order : a < b := by
      induction path with
      | edge he => exact fork_strict ordered he
      | snoc _ he ih => exact Nat.lt_trans ih (fork_strict ordered he)
    exact Or.inr (join_tail_reaches empty 0 a b (Nat.zero_le _) order)
  refine ⟨R, A, R, (fun a => ⟨a, rfl⟩), (fun v => finiteSupport_singleton v),
    richBiosphere, organismBiosphere, richBiosphere,
    WongAlexander.natural_biosphere_has_real_dates richBiosphere,
    WongAlexander.natural_biosphere_has_real_dates organismBiosphere,
    WongAlexander.natural_biosphere_has_real_dates richBiosphere,
    fork_connected empty 0, soundA, ?_,
    join_specieslike empty 0, fork_not_iap ordered⟩
  intro a b path
  exact Or.inr path

/-- These are abstract topology-compatible completions. They have not been
shown to arise from a genomic observation likelihood or an owner pedigree. -/
structure AbstractCompletionObservation (Node : Type u) (Coord : Type v)
    [Fintype Node] [LinearOrder Coord] where
  observed : WongGARG.GARG Node Coord
  completion : Graph
  compatible : FiniteGenomeIdentifiability.Compatible observed completion

/-- Any deterministic coarsening of finite gARG data has the same universal
recovery obstruction over the repository's abstract completion class. This
does not rule out statistical identifiability under a restricted model. -/
theorem no_specieslike_recovery_from_garg_coarsening
    {Node : Type u} {Coord : Type v} [Fintype Node] [LinearOrder Coord]
    (G : WongGARG.GARG Node Coord) {Observation : Type w}
    (observe : WongGARG.GARG Node Coord → Observation) :
    ¬ ObservationPrediction.Recoverable
      (fun h : AbstractCompletionObservation Node Coord => observe h.observed)
      (fun h : AbstractCompletionObservation Node Coord => Specieslike h.completion Whole) := by
  obtain ⟨A, B, hA, hB, speciesA, notSpeciesB⟩ :=
    FiniteGenomeIdentifiability.opposite_compatible_completions G
  let a : AbstractCompletionObservation Node Coord := ⟨G, A, hA⟩
  let b : AbstractCompletionObservation Node Coord := ⟨G, B, hB⟩
  apply ObservationPrediction.collision_obstructs_recovery (a := a) (b := b) rfl
  intro same
  exact notSpeciesB (same ▸ speciesA)

end WongPedigreeBridge

#print axioms WongPedigreeBridge.finiteSupport_preimage_iff
#print axioms WongPedigreeBridge.infiniteSupport_preimage_iff
#print axioms WongPedigreeBridge.iap_iff
#print axioms WongPedigreeBridge.reflection_iff
#print axioms WongPedigreeBridge.commonAncestor_descends
#print axioms WongPedigreeBridge.convex_pullback
#print axioms WongPedigreeBridge.convex_iff
#print axioms WongPedigreeBridge.specieslike_descends
#print axioms WongPedigreeBridge.specieslike_iff
#print axioms WongPedigreeBridge.maximal_saturated_iff
#print axioms WongPedigreeBridge.maximalSpecieslike_descends
#print axioms WongPedigreeBridge.iap_iff_of_finite_ancestry_errors
#print axioms WongPedigreeBridge.sound_projection_does_not_determine_iap
#print axioms WongPedigreeBridge.no_specieslike_recovery_from_garg_coarsening
