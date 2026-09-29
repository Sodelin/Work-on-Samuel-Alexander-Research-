import SamuelAlexanderResearch.LayeredUnavoidability

/-!
Necessity of natural ranks on reachable endpoint/phase states, connected to
the existing BinaryNatPopulation and Realizes definitions. The only imported
compactness argument is the already proved infinite_path_from_good.
No external continuation-bound premise is assumed.
-/

namespace ReachableRankNecessity

open SpeciesBridge BinaryPopulation PositiveUnavoidability

def Reachable (E : LabelledGraph) (s : Nat → Bool) (v k : Nat) : Prop :=
  ∃ start, FinitePath E s 0 k start v

def HasContinuation (E : LabelledGraph) (s : Nat → Bool) (v k len : Nat) : Prop :=
  ∃ endpoint, FinitePath E s k len v endpoint

def IsMaximumContinuation (E : LabelledGraph) (s : Nat → Bool)
    (v k height : Nat) : Prop :=
  HasContinuation E s v k height ∧
    ∀ len, HasContinuation E s v k len → len ≤ height

def NaturalCertificate (E : LabelledGraph) (s : Nat → Bool)
    (r : Nat → Nat → Nat) : Prop :=
  ∀ v k, Reachable E s v k → ∀ w, E v w (s k) →
    r w (k + 1) < r v k

theorem reachable_zero (E : LabelledGraph) (s : Nat → Bool) (v : Nat) :
    Reachable E s v 0 := ⟨v, .nil _ _⟩

theorem reachable_step {E : LabelledGraph} {s : Nat → Bool} {v k w : Nat}
    (hr : Reachable E s v k) (he : E v w (s k)) :
    Reachable E s w (k + 1) := by
  obtain ⟨start, hp⟩ := hr
  exact ⟨start, hp.snoc (by simpa using he)⟩

/-- A reachable infinite continuation would splice to an actual realization. -/
theorem reachable_endpoints_bounded (E : LabelledGraph) (s : Nat → Bool)
    (finite : ∀ u, FiniteSupport (ForgetLabels E u))
    (avoids : ¬ Realizes E s) {v k : Nat} (hr : Reachable E s v k) :
    BoundedSupport (Endpoint E s k v) := by
  classical
  apply Classical.byContradiction
  intro good
  obtain ⟨tail, hzero, hedges⟩ := infinite_path_from_good E s finite k v good
  obtain ⟨start, initialPath⟩ := hr
  obtain ⟨path, _, hp⟩ := initialPath.prepend_infinite tail hzero (by simpa using hedges)
  exact avoids ⟨path, by simpa using hp⟩

/-- The actual population axioms force a continuation length bound. -/
theorem reachable_lengths_bounded (E : LabelledGraph) (s : Nat → Bool)
    (population : BinaryNatPopulation E) (avoids : ¬ Realizes E s)
    {v k : Nat} (hr : Reachable E s v k) :
    ∃ bound, ∀ len, HasContinuation E s v k len → len ≤ bound := by
  obtain ⟨bound, hb⟩ := reachable_endpoints_bounded E s
    population.2.1.2.2.1 avoids hr
  refine ⟨bound, ?_⟩
  intro len hlen
  obtain ⟨endpoint, hp⟩ := hlen
  have hend := hb endpoint ⟨len, hp⟩
  have hl := LayeredUnavoidability.finitePath_length_le_endpoint
    (fun u w b he => population.2.1.1 u w ⟨b, he⟩) hp
  omega

private theorem bounded_predicate_maximum (P : Nat → Prop) (hzero : P 0)
    (bound : Nat) (hb : ∀ n, P n → n ≤ bound) :
    ∃ m, P m ∧ ∀ n, P n → n ≤ m := by
  classical
  induction bound with
  | zero => exact ⟨0, hzero, hb⟩
  | succ bound ih =>
    by_cases htop : P (bound + 1)
    · exact ⟨bound + 1, htop, hb⟩
    · apply ih
      intro n hn
      have hle := hb n hn
      have hne : n ≠ bound + 1 := fun h => htop (h ▸ hn)
      omega

theorem reachable_maximum_exists (E : LabelledGraph) (s : Nat → Bool)
    (population : BinaryNatPopulation E) (avoids : ¬ Realizes E s)
    {v k : Nat} (hr : Reachable E s v k) :
    ∃ height, IsMaximumContinuation E s v k height := by
  obtain ⟨bound, hb⟩ := reachable_lengths_bounded E s population avoids hr
  exact bounded_predicate_maximum (HasContinuation E s v k)
    ⟨v, .nil _ _⟩ bound hb

/-- Total presentation: values at unreachable states are arbitrary, set to 0. -/
noncomputable def rank (E : LabelledGraph) (s : Nat → Bool)
    (population : BinaryNatPopulation E) (avoids : ¬ Realizes E s)
    (v k : Nat) : Nat := by
  classical
  exact if hr : Reachable E s v k then
    Classical.choose (reachable_maximum_exists E s population avoids hr)
  else 0

theorem rank_isMaximum (E : LabelledGraph) (s : Nat → Bool)
    (population : BinaryNatPopulation E) (avoids : ¬ Realizes E s)
    {v k : Nat} (hr : Reachable E s v k) :
    IsMaximumContinuation E s v k (rank E s population avoids v k) := by
  classical
  simp only [rank, dif_pos hr]
  exact Classical.choose_spec (reachable_maximum_exists E s population avoids hr)

/-- Actual avoidance supplies a strictly decreasing reachable-state rank. -/
theorem rank_isCertificate (E : LabelledGraph) (s : Nat → Bool)
    (population : BinaryNatPopulation E) (avoids : ¬ Realizes E s) :
    NaturalCertificate E s (rank E s population avoids) := by
  intro v k hr w he
  have hchild := reachable_step hr he
  have hparentMax := rank_isMaximum E s population avoids hr
  have hchildMax := rank_isMaximum E s population avoids hchild
  obtain ⟨endpoint, tail⟩ := hchildMax.1
  have joined := FinitePath.cons he tail
  have bounded := hparentMax.2 _ ⟨endpoint, joined⟩
  omega

theorem avoidance_has_natural_certificate (E : LabelledGraph) (s : Nat → Bool)
    (population : BinaryNatPopulation E) (avoids : ¬ Realizes E s) :
    ∃ r, NaturalCertificate E s r :=
  ⟨rank E s population avoids, rank_isCertificate E s population avoids⟩

/-- A natural certificate bounds any continuation from a reachable state. -/
theorem certificate_bounds_continuation {E : LabelledGraph} {s : Nat → Bool}
    {r : Nat → Nat → Nat} (cert : NaturalCertificate E s r)
    {v k len endpoint : Nat} (path : FinitePath E s k len v endpoint)
    (reachable : Reachable E s v k) :
    r endpoint (k + len) + len ≤ r v k := by
  induction path with
  | nil => simp
  | @cons k n u v w he tail ih =>
    have hchild := reachable_step reachable he
    have hbound := ih hchild
    have hdec := cert u k reachable v he
    have hi : k + (n + 1) = (k + 1) + n := by omega
    rw [hi]
    omega

theorem rank_is_least (E : LabelledGraph) (s : Nat → Bool)
    (population : BinaryNatPopulation E) (avoids : ¬ Realizes E s)
    {r : Nat → Nat → Nat} (cert : NaturalCertificate E s r)
    {v k : Nat} (reachable : Reachable E s v k) :
    rank E s population avoids v k ≤ r v k := by
  obtain ⟨endpoint, hp⟩ := (rank_isMaximum E s population avoids reachable).1
  have bound := certificate_bounds_continuation cert hp reachable
  omega

theorem certificate_excludes_realization (E : LabelledGraph) (s : Nat → Bool)
    {r : Nat → Nat → Nat} (cert : NaturalCertificate E s r) :
    ¬ Realizes E s := by
  rintro ⟨path, hp⟩
  have prefixes : ∀ n, FinitePath E s 0 n (path 0) (path n) := by
    intro n
    induction n with
    | zero => exact .nil _ _
    | succ n ih => exact ih.snoc (by simpa using hp n)
  have impossible := certificate_bounds_continuation cert
    (prefixes (r (path 0) 0 + 1)) (reachable_zero E s (path 0))
  omega

/-- An equivalence about the existing actual population and realization predicates. -/
theorem avoids_iff_has_natural_certificate (E : LabelledGraph) (s : Nat → Bool)
    (population : BinaryNatPopulation E) :
    (¬ Realizes E s) ↔ ∃ r, NaturalCertificate E s r := by
  constructor
  · exact avoidance_has_natural_certificate E s population
  · rintro ⟨r, hr⟩
    exact certificate_excludes_realization E s hr

/-- Explicit specialization to the existing binary avoiding construction. -/
theorem aperiodic_Ps_has_natural_certificate (s : Nat → Bool)
    (aperiodic : ¬ BinaryAvoidance.EventuallyPeriodic s) :
    ∃ r, NaturalCertificate (BinaryAvoidance.Edge s) s r := by
  exact avoidance_has_natural_certificate (BinaryAvoidance.Edge s) s
    (edge_is_binaryNatPopulation s) (edge_avoids_aperiodic_target s aperiodic)

end ReachableRankNecessity

#print axioms ReachableRankNecessity.reachable_endpoints_bounded
#print axioms ReachableRankNecessity.reachable_maximum_exists
#print axioms ReachableRankNecessity.rank_isCertificate
#print axioms ReachableRankNecessity.rank_is_least
#print axioms ReachableRankNecessity.avoids_iff_has_natural_certificate
#print axioms ReachableRankNecessity.aperiodic_Ps_has_natural_certificate
