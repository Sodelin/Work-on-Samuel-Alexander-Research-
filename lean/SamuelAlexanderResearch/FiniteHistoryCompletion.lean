import SamuelAlexanderResearch.SpeciesGlobalIAP

/-! Finite birth-ordered histories do not determine whole-population specieshood.
Two explicit infinite completions preserve every edge and path in the old prefix.
The completions are mathematical witnesses, not inferred biological futures. -/

namespace FiniteHistoryCompletion
open SpeciesBridge SpeciesGlobalIAP

def Stem (E : Graph) (n u v : Nat) : Prop :=
  (u < n ∧ v < n ∧ E u v) ∨ (u < n ∧ v = n)

def Join (E : Graph) (n : Nat) : Graph := fun u v =>
  Stem E n u v ∨ (n ≤ u ∧ v = u + 1)

def Fork (E : Graph) (n : Nat) : Graph := fun u v =>
  Stem E n u v ∨ (u = n ∧ v = n + 1) ∨ (n ≤ u ∧ v = u + 2)

def OrderedPrefix (E : Graph) (n : Nat) : Prop :=
  ∀ u v, u < n → v < n → E u v → u < v

theorem join_old_edge (E : Graph) (n u v : Nat) (hu : u < n) (hv : v < n) :
    Join E n u v ↔ E u v := by
  constructor
  · rintro ((⟨_, _, h⟩ | ⟨_, h⟩) | ⟨h, _⟩)
    · exact h
    · omega
    · omega
  · intro h; exact Or.inl (Or.inl ⟨hu, hv, h⟩)

theorem fork_old_edge (E : Graph) (n u v : Nat) (hu : u < n) (hv : v < n) :
    Fork E n u v ↔ E u v := by
  constructor
  · rintro ((⟨_, _, h⟩ | ⟨_, h⟩) | ⟨h, _⟩ | ⟨h, _⟩)
    · exact h
    · omega
    · omega
    · omega
  · intro h; exact Or.inl (Or.inl ⟨hu, hv, h⟩)

theorem join_strict {E : Graph} {n : Nat} (h : OrderedPrefix E n)
    {u v : Nat} (he : Join E n u v) : u < v := by
  rcases he with (⟨hu, hv, he⟩ | ⟨hu, hv⟩) | ⟨hu, hv⟩
  · exact h u v hu hv he
  all_goals omega

theorem fork_strict {E : Graph} {n : Nat} (h : OrderedPrefix E n)
    {u v : Nat} (he : Fork E n u v) : u < v := by
  rcases he with (⟨hu, hv, he⟩ | ⟨hu, hv⟩) | ⟨hu, hv⟩ | ⟨hu, hv⟩
  · exact h u v hu hv he
  all_goals omega

private theorem path_strict {E : Graph} (h : ∀ u v, E u v → u < v)
    {u v : Nat} (hp : Descendant E u v) : u < v := by
  induction hp with
  | edge he => exact h _ _ he
  | snoc _ he ih => exact Nat.lt_trans ih (h _ _ he)

/-- No newly added path can enter the old history from the future. -/
theorem join_old_path {E : Graph} {n u v : Nat}
    (hp : Descendant (Join E n) u v) (hv : v < n) : Descendant E u v := by
  induction hp with
  | edge he =>
    rcases he with (⟨_, _, he⟩ | ⟨_, hvn⟩) | ⟨hu, huv⟩
    · exact .edge he
    all_goals omega
  | snoc _ he ih =>
    rcases he with (⟨hu, _, he⟩ | ⟨_, hvn⟩) | ⟨hu, huv⟩
    · exact .snoc (ih hu) he
    all_goals omega

theorem fork_old_path {E : Graph} {n u v : Nat}
    (hp : Descendant (Fork E n) u v) (hv : v < n) : Descendant E u v := by
  induction hp with
  | edge he =>
    rcases he with (⟨_, _, he⟩ | ⟨_, hvn⟩) | ⟨hu, huv⟩ | ⟨hu, huv⟩
    · exact .edge he
    all_goals omega
  | snoc _ he ih =>
    rcases he with (⟨hu, _, he⟩ | ⟨_, hvn⟩) | ⟨hu, huv⟩ | ⟨hu, huv⟩
    · exact .snoc (ih hu) he
    all_goals omega

/-- The actual old graph restricts both endpoints to the observed prefix. -/
def Old (E : Graph) (n : Nat) : Graph := fun u v => u < n ∧ v < n ∧ E u v

private theorem old_path_lift {E F : Graph} {n u v : Nat}
    (edges : ∀ a b, Old E n a b → F a b)
    (hp : Descendant (Old E n) u v) : Descendant F u v := by
  induction hp with
  | edge he => exact .edge (edges _ _ he)
  | snoc _ he ih => exact .snoc ih (edges _ _ he)

private theorem join_old_path_restricted {E : Graph} {n u v : Nat}
    (hp : Descendant (Join E n) u v) (hv : v < n) : Descendant (Old E n) u v := by
  induction hp with
  | edge he =>
    rcases he with (⟨ha, hb, he⟩ | ⟨_, hvn⟩) | ⟨ha, hab⟩
    · exact .edge ⟨ha, hb, he⟩
    all_goals omega
  | snoc _ he ih =>
    rcases he with (⟨ha, hb, he⟩ | ⟨_, hvn⟩) | ⟨ha, hab⟩
    · exact .snoc (ih ha) ⟨ha, hb, he⟩
    all_goals omega

private theorem fork_old_path_restricted {E : Graph} {n u v : Nat}
    (hp : Descendant (Fork E n) u v) (hv : v < n) : Descendant (Old E n) u v := by
  induction hp with
  | edge he =>
    rcases he with (⟨ha, hb, he⟩ | ⟨_, hvn⟩) | ⟨ha, hab⟩ | ⟨ha, hab⟩
    · exact .edge ⟨ha, hb, he⟩
    all_goals omega
  | snoc _ he ih =>
    rcases he with (⟨ha, hb, he⟩ | ⟨_, hvn⟩) | ⟨ha, hab⟩ | ⟨ha, hab⟩
    · exact .snoc (ih ha) ⟨ha, hb, he⟩
    all_goals omega

theorem old_reachability_exact (E : Graph) (n u v : Nat) (hv : v < n) :
    (Descendant (Join E n) u v ↔ Descendant (Old E n) u v) ∧
    (Descendant (Fork E n) u v ↔ Descendant (Old E n) u v) := by
  exact ⟨⟨fun h => join_old_path_restricted h hv,
    old_path_lift (fun _ _ h => Or.inl (Or.inl h))⟩,
    ⟨fun h => fork_old_path_restricted h hv,
    old_path_lift (fun _ _ h => Or.inl (Or.inl h))⟩⟩

theorem join_tail_reaches (E : Graph) (n u v : Nat) (hu : n ≤ u) (huv : u < v) :
    Descendant (Join E n) u v := by
  induction v with
  | zero => omega
  | succ v ih =>
    by_cases h : u = v
    · subst v; exact .edge (Or.inr ⟨hu, rfl⟩)
    · exact .snoc (ih (by omega)) (Or.inr ⟨by omega, rfl⟩)

theorem join_far_reaches (E : Graph) (n u v : Nat) (hv : n + u < v) :
    Descendant (Join E n) u v := by
  by_cases hu : u < n
  · exact (Descendant.edge (Or.inl (Or.inr ⟨hu, rfl⟩))).trans
      (join_tail_reaches E n n v (by omega) (by omega))
  · exact join_tail_reaches E n u v (by omega) (by omega)

theorem join_cofinite (E : Graph) (n : Nat) : CofiniteDescendants (Join E n) := by
  intro u
  apply (finiteSupport_iff_bounded _).mpr
  refine ⟨n + u + 1, ?_⟩
  intro v hv
  by_cases h : v < n + u + 1
  · exact h
  · exact False.elim (hv (join_far_reaches E n u v (by omega)))

theorem join_connected (E : Graph) (n : Nat) : WeaklyConnected (Join E n) Whole := by
  refine ⟨⟨0, trivial⟩, ?_⟩
  intro u v _ _
  exact .trans (join_far_reaches E n u (n + u + v + 1) (by omega)).weakReach_whole
    (join_far_reaches E n v (n + u + v + 1) (by omega)).weakReach_whole.symm

theorem join_specieslike (E : Graph) (n : Nat) : Specieslike (Join E n) Whole :=
  (whole_specieslike_iff _).mpr ⟨join_connected E n, fun v => Or.inr (join_cofinite E n v)⟩

theorem join_inspecies (E : Graph) (n : Nat) : Inspecies (Join E n) Whole :=
  (whole_inspecies_iff_cofinite_descendants _).mpr (join_cofinite E n)

theorem join_maximal_specieslike (E : Graph) (n : Nat) :
    MaximalSpecieslike (Join E n) Whole := by
  exact ⟨join_specieslike E n, fun _ _ _ _ _ => trivial⟩

theorem join_children (E : Graph) (n u : Nat) : FiniteSupport (Join E n u) := by
  apply (finiteSupport_iff_bounded _).mpr
  refine ⟨n + u + 3, ?_⟩
  rintro v ((⟨_, hv, _⟩ | ⟨_, hv⟩) | ⟨_, hv⟩) <;> omega

theorem fork_children (E : Graph) (n u : Nat) : FiniteSupport (Fork E n u) := by
  apply (finiteSupport_iff_bounded _).mpr
  refine ⟨n + u + 3, ?_⟩
  rintro v ((⟨_, hv, _⟩ | ⟨_, hv⟩) | ⟨_, hv⟩ | ⟨_, hv⟩) <;> omega

theorem join_roots (E : Graph) (n : Nat) : FiniteSupport (Root (Join E n)) := by
  apply (finiteSupport_iff_bounded _).mpr
  refine ⟨n + 1, ?_⟩
  intro v hv
  apply Classical.byContradiction
  intro hn
  have he : Join E n (v - 1) v := Or.inr ⟨by omega, by omega⟩
  exact hv _ he

theorem fork_roots (E : Graph) (n : Nat) : FiniteSupport (Root (Fork E n)) := by
  apply (finiteSupport_iff_bounded _).mpr
  refine ⟨n + 1, ?_⟩
  intro v hv
  apply Classical.byContradiction
  intro hn
  by_cases heq : v = n + 1
  · exact hv n (Or.inr (Or.inl ⟨rfl, heq⟩))
  · exact hv (v - 2) (Or.inr (Or.inr ⟨by omega, by omega⟩))

theorem join_biosphere {E : Graph} {n : Nat} (h : OrderedPrefix E n) :
    NaturalDateBiosphere (Join E n) :=
  ⟨fun _ _ he => join_strict h he, finite_birthdate_prefix, join_children E n, whole_infinite⟩

theorem fork_biosphere {E : Graph} {n : Nat} (h : OrderedPrefix E n) :
    NaturalDateBiosphere (Fork E n) :=
  ⟨fun _ _ he => fork_strict h he, finite_birthdate_prefix, fork_children E n, whole_infinite⟩

theorem fork_tail_parity {E : Graph} {n u v : Nat} (h : OrderedPrefix E n)
    (hu : n < u) (hp : Descendant (Fork E n) u v) : u % 2 = v % 2 := by
  induction hp with
  | edge he =>
    rcases he with (⟨ha, _, _⟩ | ⟨ha, _⟩) | ⟨ha, _⟩ | ⟨_, hv⟩ <;> omega
  | snoc hp he ih =>
    have hmid := path_strict (fun _ _ he => fork_strict h he) hp
    rcases he with (⟨ha, _, _⟩ | ⟨ha, _⟩) | ⟨ha, _⟩ | ⟨_, hv⟩ <;> omega

theorem fork_branch_reaches (E : Graph) (n m : Nat) :
    Descendant (Fork E n) (n + 1) (n + 1 + 2 * (m + 1)) := by
  induction m with
  | zero => exact .edge (Or.inr (Or.inr ⟨by omega, by omega⟩))
  | succ m ih => exact .snoc ih (Or.inr (Or.inr ⟨by omega, by omega⟩))

theorem fork_not_iap {E : Graph} {n : Nat} (h : OrderedPrefix E n) :
    ¬ IAP (Fork E n) Whole := by
  intro hiap
  rcases (iap_whole_iff _).mp hiap (n + 1) with hd | hn
  · obtain ⟨b, hb⟩ := (finiteSupport_iff_bounded _).mp hd
    have := hb _ (fork_branch_reaches E n b)
    omega
  · obtain ⟨b, hb⟩ := (finiteSupport_iff_bounded _).mp hn
    have hnot : ¬ Descendant (Fork E n) (n + 1) (n + 2 + 2 * b) := by
      intro hp
      have := fork_tail_parity h (by omega) hp
      omega
    have := hb _ hnot
    omega

private theorem fork_anchor_connected (E : Graph) (n v : Nat) :
    WeakReach (Fork E n) Whole n v := by
  induction v using Nat.strongRecOn with
  | ind v ih =>
    by_cases hv : v < n
    · exact WeakReach.symm (.edge trivial trivial (Or.inl (Or.inl (Or.inr ⟨hv, rfl⟩))))
    · by_cases h0 : v = n
      · subst v; exact .refl trivial
      · by_cases h1 : v = n + 1
        · exact .edge trivial trivial (Or.inl (Or.inr (Or.inl ⟨rfl, h1⟩)))
        · exact .trans (ih (v - 2) (by omega))
            (.edge trivial trivial (Or.inl (Or.inr (Or.inr ⟨by omega, by omega⟩))))

theorem fork_connected (E : Graph) (n : Nat) : WeaklyConnected (Fork E n) Whole := by
  refine ⟨⟨n, trivial⟩, ?_⟩
  intro u v _ _
  exact .trans (fork_anchor_connected E n u).symm (fork_anchor_connected E n v)

/-- Same finite input and exact old reachability, opposite whole-species status.
No binary parent-label coverage or claim about an empirically realized future. -/
theorem finite_history_does_not_determine_species (E : Graph) (n : Nat)
    (h : OrderedPrefix E n) :
    ∃ A B : Graph,
      NaturalDateBiosphere A ∧ NaturalDateBiosphere B ∧
      FiniteSupport (Root A) ∧ FiniteSupport (Root B) ∧
      WeaklyConnected A Whole ∧ WeaklyConnected B Whole ∧
      (∀ u v, u < n → v < n → (A u v ↔ E u v) ∧ (B u v ↔ E u v)) ∧
      (∀ u v, v < n → (Descendant A u v ↔ Descendant (Old E n) u v) ∧
        (Descendant B u v ↔ Descendant (Old E n) u v)) ∧
      Inspecies A Whole ∧ MaximalSpecieslike A Whole ∧ ¬ IAP B Whole := by
  exact ⟨Join E n, Fork E n, join_biosphere h, fork_biosphere h,
    join_roots E n, fork_roots E n, join_connected E n, fork_connected E n,
    fun u v hu hv => ⟨join_old_edge E n u v hu hv, fork_old_edge E n u v hu hv⟩,
    fun u v hv => old_reachability_exact E n u v hv,
    join_inspecies E n, join_maximal_specieslike E n, fork_not_iap h⟩

end FiniteHistoryCompletion

#print axioms FiniteHistoryCompletion.old_reachability_exact
#print axioms FiniteHistoryCompletion.join_biosphere
#print axioms FiniteHistoryCompletion.fork_biosphere
#print axioms FiniteHistoryCompletion.join_inspecies
#print axioms FiniteHistoryCompletion.join_maximal_specieslike
#print axioms FiniteHistoryCompletion.fork_not_iap
#print axioms FiniteHistoryCompletion.finite_history_does_not_determine_species
