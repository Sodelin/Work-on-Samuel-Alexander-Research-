import Std

/-!
# Enumerating a locally finite birth order

The enumeration is constructed from infinitude and finite birthdate sublevels;
it is not an input. Equal birthdates are allowed and are resolved by choice.
This module is polymorphic in the ordered time type. An instantiation with a
concrete real-number type is a separate obligation, not hidden in the name.
-/

namespace BirthOrder

universe u v

def FiniteCover {V : Type u} (S : V -> Prop) : Prop :=
  exists xs : List V, forall x, S x -> x ∈ xs

def InfiniteVertices (V : Type u) : Prop :=
  forall xs : List V, exists x, x ∉ xs

theorem infiniteVertices_iff_not_finiteCover (V : Type u) :
    InfiniteVertices V ↔ ¬ FiniteCover (fun _ : V => True) := by
  classical
  constructor
  · intro hi hf
    obtain ⟨xs, hxs⟩ := hf
    obtain ⟨x, hx⟩ := hi xs
    exact hx (hxs x trivial)
  · intro hi xs
    by_cases hex : exists x, x ∉ xs
    · exact hex
    · have hcover : FiniteCover (fun _ : V => True) := by
        refine ⟨xs, ?_⟩
        intro x _
        by_cases hx : x ∈ xs
        · exact hx
        · exact False.elim (hex ⟨x, hx⟩)
      exact False.elim (hi hcover)

def FiniteSublevels {V : Type u} {Time : Type v} [LE Time]
    (birth : V -> Time) : Prop :=
  forall r : Time, FiniteCover (fun x => birth x <= r)

section OrderedTime

variable {V : Type u} {Time : Type v} [LE Time] [Std.IsLinearPreorder Time]
variable (birth : V -> Time)

private theorem finite_minimum (xs : List V) (S : V -> Prop)
    (hex : exists x, x ∈ xs ∧ S x) :
    exists x, x ∈ xs ∧ S x ∧
      forall y, y ∈ xs -> S y -> birth x <= birth y := by
  classical
  induction xs with
  | nil => simp at hex
  | cons a xs ih =>
    by_cases htail : exists x, x ∈ xs ∧ S x
    · obtain ⟨b, hb, hSb, hmin⟩ := ih htail
      by_cases hSa : S a
      · rcases Std.IsLinearPreorder.le_total (birth a) (birth b) with hab | hba
        · refine ⟨a, by simp, hSa, ?_⟩
          intro y hy hSy
          rcases List.mem_cons.mp hy with rfl | hy
          · exact Std.IsPreorder.le_refl _
          · exact Std.IsPreorder.le_trans _ _ _ hab (hmin y hy hSy)
        · refine ⟨b, List.mem_cons_of_mem a hb, hSb, ?_⟩
          intro y hy hSy
          rcases List.mem_cons.mp hy with rfl | hy
          · exact hba
          · exact hmin y hy hSy
      · refine ⟨b, List.mem_cons_of_mem a hb, hSb, ?_⟩
        intro y hy hSy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact False.elim (hSa hSy)
        · exact hmin y hy hSy
    · obtain ⟨x, hx, hSx⟩ := hex
      have hxa : x = a := by
        rcases List.mem_cons.mp hx with h | h
        · exact h
        · exact False.elim (htail ⟨x, h, hSx⟩)
      subst x
      refine ⟨a, by simp, hSx, ?_⟩
      intro y hy hSy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact Std.IsPreorder.le_refl _
      · exact False.elim (htail ⟨y, hy, hSy⟩)

/-- Every nonempty subset has a least birthdate, using a finite sublevel
through any member of that subset. This does not assume a well-order. -/
theorem exists_least (finite : FiniteSublevels birth) (S : V -> Prop)
    (nonempty : exists x, S x) :
    exists x, S x ∧ forall y, S y -> birth x <= birth y := by
  obtain ⟨a, hSa⟩ := nonempty
  obtain ⟨xs, hxs⟩ := finite (birth a)
  have ha : a ∈ xs := hxs a (Std.IsPreorder.le_refl _)
  obtain ⟨b, _, hSb, hmin⟩ := finite_minimum birth xs S ⟨a, ha, hSa⟩
  refine ⟨b, hSb, ?_⟩
  intro y hSy
  rcases Std.IsLinearPreorder.le_total (birth y) (birth a) with hya | hay
  · exact hmin y (hxs y hya) hSy
  · exact Std.IsPreorder.le_trans _ _ _ (hmin a ha hSa) hay

variable (infinite : InfiniteVertices V) (finite : FiniteSublevels birth)

include infinite finite in
private theorem exists_fresh_least (xs : List V) :
    exists x, x ∉ xs ∧ forall y, y ∉ xs -> birth x <= birth y :=
  exists_least birth finite (fun x => x ∉ xs) (infinite xs)

noncomputable def fresh (xs : List V) : V :=
  Classical.choose (exists_fresh_least birth infinite finite xs)

theorem fresh_spec (xs : List V) :
    fresh birth infinite finite xs ∉ xs ∧
      forall y, y ∉ xs -> birth (fresh birth infinite finite xs) <= birth y :=
  Classical.choose_spec (exists_fresh_least birth infinite finite xs)

/-- The first `n` chosen vertices, stored in reverse order. -/
noncomputable def chosen : Nat -> List V
  | 0 => []
  | n + 1 => fresh birth infinite finite (chosen n) :: chosen n

noncomputable def enumerate (n : Nat) : V :=
  fresh birth infinite finite (chosen birth infinite finite n)

theorem chosen_succ (n : Nat) : chosen birth infinite finite (n + 1) =
    enumerate birth infinite finite n :: chosen birth infinite finite n := rfl

theorem chosen_length (n : Nat) : (chosen birth infinite finite n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [chosen_succ, List.length_cons, ih]

theorem chosen_nodup (n : Nat) : (chosen birth infinite finite n).Nodup := by
  induction n with
  | zero => exact List.nodup_nil
  | succ n ih =>
    rw [chosen_succ, List.nodup_cons]
    exact ⟨(fresh_spec birth infinite finite _).1, ih⟩

theorem mem_chosen_iff (x : V) (n : Nat) :
    x ∈ chosen birth infinite finite n ↔
      exists k, k < n ∧ enumerate birth infinite finite k = x := by
  induction n with
  | zero => simp [chosen]
  | succ n ih =>
    rw [chosen_succ, List.mem_cons, ih]
    constructor
    · rintro (hx | ⟨k, hk, he⟩)
      · exact ⟨n, by omega, hx.symm⟩
      · exact ⟨k, by omega, he⟩
    · rintro ⟨k, hk, he⟩
      by_cases hkn : k = n
      · subst k; exact Or.inl he.symm
      · exact Or.inr ⟨k, by omega, he⟩

theorem chosen_mono {n m : Nat} (hnm : n <= m) :
    forall x, x ∈ chosen birth infinite finite n -> x ∈ chosen birth infinite finite m := by
  intro x hx
  obtain ⟨k, hk, he⟩ := (mem_chosen_iff birth infinite finite x n).mp hx
  exact (mem_chosen_iff birth infinite finite x m).mpr ⟨k, by omega, he⟩

theorem enumerate_fresh (n : Nat) :
    enumerate birth infinite finite n ∉ chosen birth infinite finite n :=
  (fresh_spec birth infinite finite _).1

theorem enumerate_injective (i j : Nat)
    (heq : enumerate birth infinite finite i = enumerate birth infinite finite j) : i = j := by
  by_cases hij : i < j
  · have hm := (mem_chosen_iff birth infinite finite _ j).mpr ⟨i, hij, heq⟩
    exact False.elim (enumerate_fresh birth infinite finite j hm)
  · by_cases hji : j < i
    · have hm := (mem_chosen_iff birth infinite finite _ i).mpr ⟨j, hji, heq.symm⟩
      exact False.elim (enumerate_fresh birth infinite finite i hm)
    · omega

theorem enumerate_nondecreasing (i j : Nat) (hij : i <= j) :
    birth (enumerate birth infinite finite i) <= birth (enumerate birth infinite finite j) := by
  apply (fresh_spec birth infinite finite _).2
  intro hj
  exact enumerate_fresh birth infinite finite j (chosen_mono birth infinite finite hij _ hj)

/-- The finite sublevel condition forces the greedy enumeration to exhaust V. -/
theorem enumerate_surjective (x : V) :
    exists n, enumerate birth infinite finite n = x := by
  classical
  by_cases hex : exists n, enumerate birth infinite finite n = x
  · exact hex
  · have hremaining : forall n, x ∉ chosen birth infinite finite n := by
      intro n hx
      obtain ⟨k, _, he⟩ := (mem_chosen_iff birth infinite finite x n).mp hx
      exact hex ⟨k, he⟩
    obtain ⟨xs, hxs⟩ := finite (birth x)
    have hsubset : chosen birth infinite finite (xs.length + 1) ⊆ xs := by
      intro y hy
      obtain ⟨k, _, rfl⟩ := (mem_chosen_iff birth infinite finite y _).mp hy
      exact hxs _ ((fresh_spec birth infinite finite _).2 x (hremaining k))
    have hlen := (chosen_nodup birth infinite finite (xs.length + 1)).length_le_of_subset hsubset
    rw [chosen_length] at hlen
    omega

/-- A natural enumeration with the properties needed for birth-order transfer. -/
structure OrderedEnumeration where
  toFun : Nat -> V
  injective : forall i j, toFun i = toFun j -> i = j
  surjective : forall x, exists n, toFun n = x
  nondecreasing : forall i j, i <= j -> birth (toFun i) <= birth (toFun j)

noncomputable def orderedEnumeration : OrderedEnumeration birth where
  toFun := enumerate birth infinite finite
  injective := enumerate_injective birth infinite finite
  surjective := enumerate_surjective birth infinite finite
  nondecreasing := enumerate_nondecreasing birth infinite finite

include infinite finite in
theorem orderedEnumeration_exists : Nonempty (OrderedEnumeration birth) :=
  ⟨orderedEnumeration birth infinite finite⟩

end OrderedTime

namespace OrderedEnumeration

variable {V : Type u} {Time : Type v} [LE Time] {birth : V -> Time}

noncomputable def index (e : OrderedEnumeration birth) (x : V) : Nat :=
  Classical.choose (e.surjective x)

theorem toFun_index (e : OrderedEnumeration birth) (x : V) :
    e.toFun (e.index x) = x := Classical.choose_spec (e.surjective x)

theorem index_toFun (e : OrderedEnumeration birth) (n : Nat) :
    e.index (e.toFun n) = n := e.injective _ _ (e.toFun_index _)

/-- Every finite set transports to a finite set of indices, with an explicit
cover of exactly the same list length. -/
theorem pullback_cover (e : OrderedEnumeration birth) (S : V -> Prop)
    (xs : List V) (hxs : forall x, S x -> x ∈ xs) :
    forall n, S (e.toFun n) -> n ∈ xs.map e.index := by
  intro n hn
  exact List.mem_map.mpr ⟨e.toFun n, hxs _ hn, e.index_toFun n⟩

theorem finiteCover_pullback (e : OrderedEnumeration birth) (S : V -> Prop)
    (hfinite : FiniteCover S) : FiniteCover (fun n => S (e.toFun n)) := by
  obtain ⟨xs, hxs⟩ := hfinite
  exact ⟨xs.map e.index, e.pullback_cover S xs hxs⟩

theorem finiteCover_pullback_iff (e : OrderedEnumeration birth) (S : V -> Prop) :
    FiniteCover (fun n => S (e.toFun n)) ↔ FiniteCover S := by
  constructor
  · rintro ⟨ns, hns⟩
    refine ⟨ns.map e.toFun, ?_⟩
    intro x hx
    have hi : e.index x ∈ ns := hns _ (by simpa only [e.toFun_index] using hx)
    exact List.mem_map.mpr ⟨e.index x, hi, e.toFun_index x⟩
  · exact e.finiteCover_pullback S

private theorem list_nat_bound (xs : List Nat) :
    exists bound, forall n, n ∈ xs -> n < bound := by
  induction xs with
  | nil => exact ⟨0, by simp⟩
  | cons a xs ih =>
    obtain ⟨bound, hbound⟩ := ih
    refine ⟨a + bound + 1, ?_⟩
    intro n hn
    rcases List.mem_cons.mp hn with rfl | hn
    · omega
    · have := hbound n hn; omega

/-- This yields the support bounds required for reindexed roots and children. -/
theorem finiteCover_pullback_bound (e : OrderedEnumeration birth) (S : V -> Prop)
    (hfinite : FiniteCover S) :
    exists bound, forall n, S (e.toFun n) -> n < bound := by
  obtain ⟨ns, hns⟩ := e.finiteCover_pullback S hfinite
  obtain ⟨bound, hbound⟩ := list_nat_bound ns
  exact ⟨bound, fun n hn => hbound n (hns n hn)⟩

section StrictOrder

variable [LT Time] [Std.LawfulOrderLT Time]

/-- Strictly ordered birthdates have strictly ordered indices, despite ties
being permitted elsewhere in the population. -/
theorem index_strict (e : OrderedEnumeration birth) (x y : V)
    (hbirth : birth x < birth y) : e.index x < e.index y := by
  by_cases h : e.index x < e.index y
  · exact h
  · have hreverse := e.nondecreasing (e.index y) (e.index x) (by omega)
    rw [e.toFun_index, e.toFun_index] at hreverse
    exact False.elim ((Std.LawfulOrderLT.lt_iff _ _).mp hbirth |>.2 hreverse)

/-- Any labelled or unlabelled edge relation with increasing birthdates becomes
an edge relation with strictly increasing natural indices. -/
theorem edges_increase (e : OrderedEnumeration birth) (E : V -> V -> Prop)
    (edge_birth : forall x y, E x y -> birth x < birth y)
    (i j : Nat) (hedge : E (e.toFun i) (e.toFun j)) : i < j := by
  have h := e.index_strict _ _ (edge_birth _ _ hedge)
  simpa only [e.index_toFun] using h

end StrictOrder

end OrderedEnumeration

section StrictSublevels

variable {V : Type u} {Time : Type v} [LE Time] [LT Time]
variable [Std.IsLinearPreorder Time] [Std.LawfulOrderLT Time]

/-- Strict finite sublevels suffice in any timeline without a greatest point.
For real dates, the larger bound can be chosen as `r + 1`. -/
theorem finiteSublevels_of_strict (birth : V -> Time)
    (above : forall r : Time, exists s, r < s)
    (finite : forall r : Time, FiniteCover (fun x => birth x < r)) :
    FiniteSublevels birth := by
  intro r
  obtain ⟨s, hrs⟩ := above r
  obtain ⟨xs, hxs⟩ := finite s
  refine ⟨xs, ?_⟩
  intro x hx
  apply hxs x
  apply (Std.LawfulOrderLT.lt_iff _ _).mpr
  obtain ⟨hrs_le, hrs_not⟩ := (Std.LawfulOrderLT.lt_iff _ _).mp hrs
  constructor
  · exact Std.IsPreorder.le_trans _ _ _ hx hrs_le
  · intro hsx
    exact hrs_not (Std.IsPreorder.le_trans _ _ _ hsx hx)

end StrictSublevels

end BirthOrder

#print axioms BirthOrder.exists_least
#print axioms BirthOrder.enumerate_injective
#print axioms BirthOrder.enumerate_nondecreasing
#print axioms BirthOrder.enumerate_surjective
#print axioms BirthOrder.orderedEnumeration_exists
#print axioms BirthOrder.OrderedEnumeration.index_toFun
#print axioms BirthOrder.OrderedEnumeration.finiteCover_pullback_iff
#print axioms BirthOrder.OrderedEnumeration.finiteCover_pullback_bound
#print axioms BirthOrder.OrderedEnumeration.index_strict
#print axioms BirthOrder.OrderedEnumeration.edges_increase
#print axioms BirthOrder.finiteSublevels_of_strict
