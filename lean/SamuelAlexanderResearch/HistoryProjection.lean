import SamuelAlexanderResearch.SpeciesAdapter

/-!
# A conditional genome-history to pedigree interface

The source motivation is Wong et al., genome ARGs, Section 2 and Figure 1.
Genetic graph edges may span multiple generations. Cell-level steps can also
stay within a single organism. This conditional interface permits a step to
map to equality or a nonempty pedigree ancestry path.

This verifies a generic projection theorem, not all gARG axioms or the
biological validity of a supplied correspondence. Edge compatibility is an
explicit hypothesis, to be justified for each concrete representation.
-/

namespace HistoryProjection

open AncestryViews

def SameOrDescendant (E : SpeciesBridge.Graph) (a b : Nat) : Prop :=
  a = b ∨ SpeciesBridge.Descendant E a b

theorem sameOrDescendant_trans {E : SpeciesBridge.Graph} {a b c : Nat}
    (hab : SameOrDescendant E a b) (hbc : SameOrDescendant E b c) :
    SameOrDescendant E a c := by
  rcases hab with hab | hab
  · subst b; exact hbc
  · rcases hbc with hbc | hbc
    · subst c; exact Or.inr hab
    · exact Or.inr (SpeciesBridge.Descendant.trans hab hbc)

theorem path_projects {Genome : Type u} {R : Genome -> Genome -> Prop}
    {E : SpeciesBridge.Graph} (owner : Genome -> Nat)
    (edgeSound : forall g h, R g h -> SameOrDescendant E (owner g) (owner h))
    {g h : Genome} (path : Reach R g h) :
    SameOrDescendant E (owner g) (owner h) := by
  induction path with
  | edge he => exact edgeSound _ _ he
  | snoc _ he ih => exact sameOrDescendant_trans ih (edgeSound _ _ he)

theorem path_projects_strict_of_distinct_owners {Genome : Type u}
    {R : Genome -> Genome -> Prop} {E : SpeciesBridge.Graph}
    (owner : Genome -> Nat)
    (edgeSound : forall g h, R g h -> SameOrDescendant E (owner g) (owner h))
    {g h : Genome} (path : Reach R g h) (different : owner g ≠ owner h) :
    SpeciesBridge.Descendant E (owner g) (owner h) := by
  rcases path_projects owner edgeSound path with same | descendant
  · exact False.elim (different same)
  · exact descendant

/-- The same theorem for a path at one fixed genomic location. -/
theorem locus_path_projects {Genome : Type u} {Locus : Type v}
    {R : Locus -> Genome -> Genome -> Prop} {E : SpeciesBridge.Graph}
    (owner : Genome -> Nat)
    (edgeSound : forall locus g h,
      R locus g h -> SameOrDescendant E (owner g) (owner h))
    {locus : Locus} {g h : Genome} (path : Reach (R locus) g h) :
    SameOrDescendant E (owner g) (owner h) :=
  path_projects owner (edgeSound locus) path

/-- The statement remains sound after location labels are erased. -/
theorem erased_path_projects {Genome : Type u} {Locus : Type v}
    {R : Locus -> Genome -> Genome -> Prop} {E : SpeciesBridge.Graph}
    (owner : Genome -> Nat)
    (edgeSound : forall locus g h,
      R locus g h -> SameOrDescendant E (owner g) (owner h))
    {g h : Genome} (path : Reach (EraseIndex R) g h) :
    SameOrDescendant E (owner g) (owner h) := by
  apply path_projects owner ?_ path
  intro a b hab
  obtain ⟨locus, he⟩ := hab
  exact edgeSound locus a b he

/-- A discrete interval interface, not a complete ARG data structure. -/
structure Interval where
  lo : Nat
  hi : Nat
  proper : lo < hi

def Interval.contains (interval : Interval) (locus : Nat) : Prop :=
  interval.lo <= locus ∧ locus < interval.hi

structure InheritanceRecord (Genome : Type u) where
  parent : Genome
  child : Genome
  regions : List Interval

def AtLocus {Genome : Type u} (records : List (InheritanceRecord Genome))
    (locus : Nat) (g h : Genome) : Prop :=
  exists record, record ∈ records ∧ record.parent = g ∧ record.child = h ∧
    exists interval, interval ∈ record.regions ∧ interval.contains locus

theorem interval_record_path_projects {Genome : Type u}
    (records : List (InheritanceRecord Genome)) {E : SpeciesBridge.Graph}
    (owner : Genome -> Nat)
    (recordSound : forall record, record ∈ records ->
      SameOrDescendant E (owner record.parent) (owner record.child))
    {locus : Nat} {g h : Genome} (path : Reach (AtLocus records locus) g h) :
    SameOrDescendant E (owner g) (owner h) := by
  apply locus_path_projects owner ?_ path
  intro position a b hab
  obtain ⟨record, member, parent, child, _⟩ := hab
  have sound := recordSound record member
  simpa only [parent, child] using sound

end HistoryProjection

#print axioms HistoryProjection.sameOrDescendant_trans
#print axioms HistoryProjection.path_projects
#print axioms HistoryProjection.path_projects_strict_of_distinct_owners
#print axioms HistoryProjection.locus_path_projects
#print axioms HistoryProjection.erased_path_projects
#print axioms HistoryProjection.interval_record_path_projects
