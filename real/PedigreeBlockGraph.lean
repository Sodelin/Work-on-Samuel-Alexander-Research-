import PedigreeBlockModel

set_option autoImplicit false

/-!
# Deterministic connectivity of one-generation block sharing

All statements here are deterministic. The positive block assumption is
needed to distinguish a vector from its complement. Independence and sampling
laws belong to the probability module.

The connectivity theorem uses the anchored exceptional event from the shared
model. Adding observed blocks preserves every existing sharing edge and path;
this monotonicity does not need independent inheritance across blocks.
-/

namespace PedigreeBlock

theorem eq_complement_iff_no_agreement {B : Nat} (u v : Code B) :
    v = complement u ↔ ¬ ∃ j, u j = v j := by
  constructor
  · intro h
    rintro ⟨j,hj⟩
    have impossible : u j = !(u j) := by
      simpa only [h,complement_apply] using hj
    cases hu : u j <;> simp [hu] at impossible
  · intro h
    funext j
    have different : u j ≠ v j := fun hj => h ⟨j,hj⟩
    cases hu : u j <;> cases hv : v j <;> simp [complement,hu,hv] at different ⊢

/-- For distinct children, missing sharing edges are exactly complementary
choice vectors, including the degenerate zero-block code space. -/
theorem not_share_iff_complement {n B : Nat} (x : Config n B)
    (a b : Fin (n+1)) (different : a ≠ b) :
    ¬ Share x a b ↔ x b = complement (x a) := by
  constructor
  · intro missing
    apply (eq_complement_iff_no_agreement (x a) (x b)).mpr
    intro agreement
    exact missing ⟨different,agreement⟩
  · intro complementary edge
    exact ((eq_complement_iff_no_agreement (x a) (x b)).mp complementary) edge.2

theorem share_of_ne_complement {n B : Nat} (x : Config n B)
    (a b : Fin (n+1)) (different : a ≠ b)
    (notComplement : x b ≠ complement (x a)) : Share x a b := by
  classical
  by_contra h
  exact notComplement ((not_share_iff_complement x a b different).mp h)

/-- A third vector outside a complementary pair would connect the pair in
two edges. Hence any disconnected graph has exactly the two anchored types. -/
theorem bad_of_not_connected {n B : Nat} (x : Config n B)
    (disconnected : ¬ Connected x) : Bad x := by
  classical
  change ¬ ∀ a b, Relation.ReflTransGen (Share x) a b at disconnected
  obtain ⟨a,ha⟩ := not_forall.mp disconnected
  obtain ⟨b,unreachable⟩ := not_forall.mp ha
  have different : a ≠ b := by
    intro same
    subst b
    exact unreachable .refl
  have complementary : x b = complement (x a) :=
    (not_share_iff_complement x a b different).mp
      (fun edge => unreachable (.single edge))
  have types (z : Fin (n+1)) : x z = x a ∨ x z = complement (x a) := by
    by_cases same : x z = x a
    · exact Or.inl same
    · right
      by_contra outside
      have az : a ≠ z := by
        intro h
        exact same (congrArg x h.symm)
      have zb : z ≠ b := by
        intro h
        exact outside ((congrArg x h).trans complementary)
      have leftEdge : Share x a z := share_of_ne_complement x a z az outside
      have rightEdge : Share x z b := by
        apply share_of_ne_complement x z b zb
        intro h
        apply same
        calc
          x z = complement (x b) := by simp only [h,complement_complement]
          _ = x a := by simp only [complementary,complement_complement]
      exact unreachable
        ((Relation.ReflTransGen.single leftEdge).trans
          (Relation.ReflTransGen.single rightEdge))
  rcases types 0 with anchor | anchor
  · refine ⟨?_,⟨b,?_⟩⟩
    · intro i
      simpa only [anchor] using types i
    · simpa only [anchor] using complementary
  · refine ⟨?_,⟨a,?_⟩⟩
    · intro i
      rcases types i with hi | hi
      · right
        rw [anchor,complement_complement]
        exact hi
      · left
        rw [anchor]
        exact hi
    · rw [anchor,complement_complement]

/-- In an exceptional configuration every sharing path stays on one side of
the complementary pair, while both sides occur. -/
theorem not_connected_of_bad {n B : Nat} (hB : 0 < B) (x : Config n B)
    (bad : Bad x) : ¬ Connected x := by
  intro connected
  have preserves (a b : Fin (n+1)) (ha : x a = x 0) (edge : Share x a b) :
      x b = x 0 := by
    rcases bad.1 b with same | complementary
    · exact same
    · have h : x b = complement (x a) := by
        rw [ha]
        exact complementary
      exact False.elim (((not_share_iff_complement x a b edge.1).mpr h) edge)
  obtain ⟨i,hi⟩ := bad.2
  have path := connected 0 i
  have same : x i = x 0 := by
    clear hi
    induction path with
    | refl => rfl
    | @tail b c _ edge ih => exact preserves b c ih edge
  exact complement_ne hB (x 0) (hi.symm.trans same)

/-- Exact deterministic characterization used by the probability count. -/
theorem not_connected_iff_bad {n B : Nat} (hB : 0 < B) (x : Config n B) :
    ¬ Connected x ↔ Bad x :=
  ⟨bad_of_not_connected x,not_connected_of_bad hB x⟩

/-- Retain the first B coordinates of a D-block observation. -/
def restrictBlocks {n B D : Nat} (hBD : B ≤ D) (x : Config n D) : Config n B :=
  fun i j => x i (Fin.castLE hBD j)

theorem share_of_restrict {n B D : Nat} (hBD : B ≤ D) (x : Config n D)
    {a b : Fin (n+1)} (edge : Share (restrictBlocks hBD x) a b) : Share x a b := by
  obtain ⟨different,j,agree⟩ := edge
  exact ⟨different,Fin.castLE hBD j,agree⟩

/-- Adding blocks preserves each actual sharing path, not merely the
whole-family connectedness predicate. No randomness is assumed. -/
theorem reachable_of_restrict {n B D : Nat} (hBD : B ≤ D) (x : Config n D)
    {a b : Fin (n+1)}
    (path : Relation.ReflTransGen (Share (restrictBlocks hBD x)) a b) :
    Relation.ReflTransGen (Share x) a b := by
  induction path with
  | refl => exact .refl
  | tail _ edge ih => exact ih.tail (share_of_restrict hBD x edge)

/-- Once one family's sharing graph is connected, additional blocks cannot
destroy its connectivity, even when all block choices are dependent. -/
theorem connected_of_restrict {n B D : Nat} (hBD : B ≤ D) (x : Config n D)
    (connected : Connected (restrictBlocks hBD x)) : Connected x :=
  fun a b => reachable_of_restrict hBD x (connected a b)

end PedigreeBlock

#print axioms PedigreeBlock.not_share_iff_complement
#print axioms PedigreeBlock.not_connected_iff_bad
#print axioms PedigreeBlock.reachable_of_restrict
#print axioms PedigreeBlock.connected_of_restrict
