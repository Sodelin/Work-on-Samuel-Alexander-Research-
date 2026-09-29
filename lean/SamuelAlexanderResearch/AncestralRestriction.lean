import SamuelAlexanderResearch.AncestryViews

/-!
# Locus-specific ancestral-material restriction

An edge is retained exactly when its child is a sample or has a path to a
sample at the same locus. This removes nonancestral material while preserving
all original sample-ending paths. It does not suppress unary nodes, rewrite
edges, or truncate ancestry above a most recent common ancestor.

The relation is directed from parent to child. The construction is generic:
it requires neither finiteness nor acyclicity, and can therefore be applied
to a finite gARG after its inherited-interval relation has been defined.
-/

namespace AncestralRestriction

open AncestryViews

universe u v

/-- Concatenate two nonempty paths. -/
theorem reach_trans {V : Type u} {R : V -> V -> Prop} {a b c : V}
    (hab : Reach R a b) (hbc : Reach R b c) : Reach R a c := by
  induction hbc with
  | edge he => exact .snoc hab he
  | snoc _ he ih => exact .snoc ih he

/-- A vertex carries ancestral material if it is a sample or reaches one. -/
def Ancestral {V : Type u} (R : V -> V -> Prop) (S : V -> Prop)
    (a : V) : Prop :=
  S a ∨ exists s, S s ∧ Reach R a s

/-- Retain precisely those edges carrying ancestral material at their child. -/
def Restrict {V : Type u} (R : V -> V -> Prop) (S : V -> Prop)
    (a b : V) : Prop :=
  R a b ∧ Ancestral R S b

/-- Apply ancestral-material restriction separately at each index/locus. -/
def AtLocus {V : Type u} {I : Type v}
    (R : I -> V -> V -> Prop) (S : V -> Prop)
    (i : I) : V -> V -> Prop :=
  Restrict (R i) S

theorem ancestral_of_edge {V : Type u} {R : V -> V -> Prop}
    {S : V -> Prop} {a b : V} (hab : R a b) (hb : Ancestral R S b) :
    Ancestral R S a := by
  rcases hb with sample | ⟨s, sample, path⟩
  · exact Or.inr ⟨b, sample, .edge hab⟩
  · exact Or.inr ⟨s, sample, reach_trans (.edge hab) path⟩

theorem ancestral_mono_samples {V : Type u} {R : V -> V -> Prop}
    {S T : V -> Prop} (hST : forall a, S a -> T a) {a : V}
    (ha : Ancestral R S a) : Ancestral R T a := by
  rcases ha with sample | ⟨s, sample, path⟩
  · exact Or.inl (hST a sample)
  · exact Or.inr ⟨s, hST s sample, path⟩

theorem ancestral_mono_edges {V : Type u} {R Q : V -> V -> Prop}
    {S : V -> Prop} (hRQ : forall a b, R a b -> Q a b) {a : V}
    (ha : Ancestral R S a) : Ancestral Q S a := by
  rcases ha with sample | ⟨s, sample, path⟩
  · exact Or.inl sample
  · exact Or.inr ⟨s, sample, reach_mono hRQ path⟩

/-- Restriction cannot create a new original edge or path. -/
theorem restricted_path_original {V : Type u} {R : V -> V -> Prop}
    {S : V -> Prop} {a b : V} (path : Reach (Restrict R S) a b) :
    Reach R a b :=
  reach_mono (fun _ _ edge => edge.1) path

/-- Every edge of a path into ancestral material is itself retained. -/
theorem path_restricts {V : Type u} {R : V -> V -> Prop}
    {S : V -> Prop} {a b : V} (path : Reach R a b)
    (hb : Ancestral R S b) : Reach (Restrict R S) a b := by
  revert hb
  induction path with
  | edge he =>
      intro hb
      exact .edge ⟨he, hb⟩
  | snoc _ he ih =>
      intro hb
      exact .snoc (ih (ancestral_of_edge he hb)) ⟨he, hb⟩

/-- Reachability into retained ancestral material is unchanged. -/
theorem ancestral_target_path_iff {V : Type u} {R : V -> V -> Prop}
    {S : V -> Prop} {a b : V} (hb : Ancestral R S b) :
    Reach (Restrict R S) a b ↔ Reach R a b :=
  ⟨restricted_path_original, fun path => path_restricts path hb⟩

/-- The central preservation theorem: exactly the original sample paths remain. -/
theorem sample_path_iff {V : Type u} {R : V -> V -> Prop}
    {S : V -> Prop} {a s : V} (hs : S s) :
    Reach (Restrict R S) a s ↔ Reach R a s :=
  ancestral_target_path_iff (Or.inl hs)

/-- The same preservation theorem at an explicitly fixed genomic location. -/
theorem locus_sample_path_iff {V : Type u} {I : Type v}
    {R : I -> V -> V -> Prop} {S : V -> Prop} {i : I} {a s : V}
    (hs : S s) : Reach (AtLocus R S i) a s ↔ Reach (R i) a s :=
  sample_path_iff hs

/-- The restriction has exactly the same sample ancestry predicate. -/
theorem ancestral_restrict_iff {V : Type u} {R : V -> V -> Prop}
    {S : V -> Prop} {a : V} :
    Ancestral (Restrict R S) S a ↔ Ancestral R S a := by
  constructor
  · exact ancestral_mono_edges (fun _ _ edge => edge.1)
  · intro ha
    rcases ha with sample | ⟨s, sample, path⟩
    · exact Or.inl sample
    · exact Or.inr ⟨s, sample, (sample_path_iff sample).mpr path⟩

/-- Every retained edge is ancestral also in the resulting graph itself. -/
theorem restriction_resolved {V : Type u} {R : V -> V -> Prop}
    {S : V -> Prop} {a b : V} (edge : Restrict R S a b) :
    Ancestral (Restrict R S) S b :=
  ancestral_restrict_iff.mpr edge.2

/-- Repeating the same ancestral-material restriction changes no edge. -/
theorem restriction_idempotent {V : Type u} {R : V -> V -> Prop}
    {S : V -> Prop} {a b : V} :
    Restrict (Restrict R S) S a b ↔ Restrict R S a b := by
  constructor
  · exact fun edge => edge.1
  · exact fun edge => ⟨edge, restriction_resolved edge⟩

/-- Adding samples can only retain more inherited material. -/
theorem restriction_mono_samples {V : Type u} {R : V -> V -> Prop}
    {S T : V -> Prop} (hST : forall a, S a -> T a) {a b : V}
    (edge : Restrict R S a b) : Restrict R T a b :=
  ⟨edge.1, ancestral_mono_samples hST edge.2⟩

/-- A smaller sample's ancestry survives restriction to the larger sample. -/
theorem smaller_sample_ancestry_iff {V : Type u} {R : V -> V -> Prop}
    {S T : V -> Prop} (hTS : forall a, T a -> S a) {a : V} :
    Ancestral (Restrict R S) T a ↔ Ancestral R T a := by
  constructor
  · exact ancestral_mono_edges (fun _ _ edge => edge.1)
  · intro ha
    rcases ha with sample | ⟨s, sample, path⟩
    · exact Or.inl sample
    · exact Or.inr ⟨s, sample, (sample_path_iff (hTS s sample)).mpr path⟩

/-- Restricting to S and then to a subset T equals direct restriction to T. -/
theorem restriction_nested {V : Type u} {R : V -> V -> Prop}
    {S T : V -> Prop} (hTS : forall a, T a -> S a) {a b : V} :
    Restrict (Restrict R S) T a b ↔ Restrict R T a b := by
  constructor
  · intro edge
    exact ⟨edge.1.1, (smaller_sample_ancestry_iff hTS).mp edge.2⟩
  · intro edge
    exact ⟨restriction_mono_samples hTS edge,
      (smaller_sample_ancestry_iff hTS).mpr edge.2⟩

/-- Ancestral material for a union of samples is exactly the union of material. -/
theorem ancestral_union_iff {V : Type u} {R : V -> V -> Prop}
    {S T : V -> Prop} {a : V} :
    Ancestral R (fun s => S s ∨ T s) a ↔
      Ancestral R S a ∨ Ancestral R T a := by
  constructor
  · intro ha
    rcases ha with sample | ⟨s, sample, path⟩
    · rcases sample with hS | hT
      · exact Or.inl (Or.inl hS)
      · exact Or.inr (Or.inl hT)
    · rcases sample with hS | hT
      · exact Or.inl (Or.inr ⟨s, hS, path⟩)
      · exact Or.inr (Or.inr ⟨s, hT, path⟩)
  · intro ha
    rcases ha with hS | hT
    · exact ancestral_mono_samples (fun _ hs => Or.inl hs) hS
    · exact ancestral_mono_samples (fun _ ht => Or.inr ht) hT

theorem restriction_union_iff {V : Type u} {R : V -> V -> Prop}
    {S T : V -> Prop} {a b : V} :
    Restrict R (fun s => S s ∨ T s) a b ↔
      Restrict R S a b ∨ Restrict R T a b := by
  constructor
  · intro edge
    rcases ancestral_union_iff.mp edge.2 with hS | hT
    · exact Or.inl ⟨edge.1, hS⟩
    · exact Or.inr ⟨edge.1, hT⟩
  · intro edge
    rcases edge with hS | hT
    · exact ⟨hS.1, ancestral_union_iff.mpr (Or.inl hS.2)⟩
    · exact ⟨hT.1, ancestral_union_iff.mpr (Or.inr hT.2)⟩

/-- Erasing locus labels after restriction is always sound for erased ancestry. -/
theorem erase_restriction_sound {V : Type u} {I : Type v}
    {R : I -> V -> V -> Prop} {S : V -> Prop} {a b : V}
    (edge : EraseIndex (AtLocus R S) a b) :
    Restrict (EraseIndex R) S a b := by
  obtain ⟨i, hi⟩ := edge
  exact ⟨⟨i, hi.1⟩,
    ancestral_mono_edges (fun _ _ he => ⟨i, he⟩) hi.2⟩

/-- The split-locus graph retains 0 -> 1 after erasing labels first. -/
theorem erased_first_retains_edge :
    Restrict (EraseIndex SplitLocus) (fun n => n = 2) 0 1 := by
  refine ⟨⟨false, by simp [SplitLocus]⟩, Or.inr ⟨2, rfl, ?_⟩⟩
  exact .edge ⟨true, by simp [SplitLocus]⟩

/-- But no fixed locus makes 0 -> 1 ancestral to sample 2. -/
theorem restricted_first_discards_edge :
    ¬ EraseIndex (AtLocus SplitLocus (fun n => n = 2)) 0 1 := by
  rintro ⟨i, edge, anc⟩
  rcases anc with sample | ⟨s, sample, path⟩
  · omega
  · subst s
    exact no_fixed_index_path ⟨i, reach_trans (.edge edge) path⟩

/-- Locus erasure and sample restriction need not commute, even on an acyclic
two-edge graph with one designated sample. -/
theorem erasure_restriction_do_not_commute :
    Restrict (EraseIndex SplitLocus) (fun n => n = 2) 0 1 ∧
    ¬ EraseIndex (AtLocus SplitLocus (fun n => n = 2)) 0 1 :=
  ⟨erased_first_retains_edge, restricted_first_discards_edge⟩


/-- Raw indexed edges are exactly recoverable from sample-retained local edges
if and only if every raw edge already carries ancestral sample material. -/
theorem indexed_recovery_iff {V : Type u} {I : Type v}
    (R : I -> V -> V -> Prop) (S : V -> Prop) :
    (forall i a b, AtLocus R S i a b ↔ R i a b) ↔
      (forall i a b, R i a b -> Ancestral (R i) S b) := by
  constructor
  · intro recover i a b edge
    exact ((recover i a b).mpr edge).2
  · intro supported i a b
    exact ⟨fun edge => edge.1, fun edge => ⟨edge, supported i a b edge⟩⟩

/-- The only edge visible to sample 2 in the split-locus graph. -/
def VisibleTail (i : Bool) (a b : Nat) : Prop :=
  i = true ∧ a = 1 ∧ b = 2

theorem visibleTail_time {i : Bool} {a b : Nat}
    (edge : VisibleTail i a b) : a < b := by
  obtain ⟨_, rfl, rfl⟩ := edge
  omega

theorem split_restriction_is_visible_tail (i : Bool) (a b : Nat) :
    AtLocus SplitLocus (fun n => n = 2) i a b ↔ VisibleTail i a b := by
  cases i with
  | false =>
      constructor
      · intro h
        have he := h.1
        change a = 0 ∧ b = 1 at he
        obtain ⟨rfl, rfl⟩ := he
        exact False.elim (restricted_first_discards_edge ⟨false, h⟩)
      · intro h
        exact False.elim (Bool.noConfusion h.1)
  | true =>
      constructor
      · intro h
        exact ⟨rfl, h.1⟩
      · rintro ⟨_, ha, hb⟩
        exact ⟨⟨ha, hb⟩, Or.inl hb⟩

theorem visible_tail_is_resolved (i : Bool) (a b : Nat) :
    AtLocus VisibleTail (fun n => n = 2) i a b ↔ VisibleTail i a b := by
  constructor
  · exact fun edge => edge.1
  · exact fun edge => ⟨edge, Or.inl edge.2.2⟩

/-- Even retaining the sample-extracted indexed edge relations, rather than
only tree shapes, cannot identify omitted nonancestral raw edges. -/
theorem raw_graph_not_identified_by_sample_relations :
    (forall i a b,
      AtLocus SplitLocus (fun n => n = 2) i a b ↔
      AtLocus VisibleTail (fun n => n = 2) i a b) ∧
    SplitLocus false 0 1 ∧ ¬ VisibleTail false 0 1 := by
  refine ⟨?_, by simp [SplitLocus], ?_⟩
  · intro i a b
    exact (split_restriction_is_visible_tail i a b).trans
      (visible_tail_is_resolved i a b).symm
  · simp [VisibleTail]
end AncestralRestriction

#print axioms AncestralRestriction.locus_sample_path_iff
#print axioms AncestralRestriction.ancestral_restrict_iff
#print axioms AncestralRestriction.restriction_resolved
#print axioms AncestralRestriction.restriction_idempotent
#print axioms AncestralRestriction.restriction_mono_samples
#print axioms AncestralRestriction.restriction_nested
#print axioms AncestralRestriction.restriction_union_iff
#print axioms AncestralRestriction.erase_restriction_sound
#print axioms AncestralRestriction.erasure_restriction_do_not_commute
#print axioms AncestralRestriction.indexed_recovery_iff
#print axioms AncestralRestriction.raw_graph_not_identified_by_sample_relations
