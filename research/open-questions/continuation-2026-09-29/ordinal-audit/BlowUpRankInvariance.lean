import GenericCertificate
import GenericUniversalAvoiders

/-!
# Finite-fibre blow-ups preserve exact reachable continuation heights

This module connects the frozen ordinal and universal-embedding interfaces.
The blow-up is the actual `GenericUniversalAvoiders.liftedEdge`; all states
and chain lengths are the actual `GenericCertificate` definitions.
No new population, graph, or rank predicates stand in for those interfaces.
-/

namespace BlowUpRankInvariance

open GenericCertificate GenericUniversalAvoiders

universe u v
variable {V : Type u} {Label : Type v}

/-- Reachability is invariant at every individual copy, not just somewhere in a fibre. -/
theorem reachable_iff (p : Population V Label) (m : V → Nat)
    (hm : ∀ v, 0 < m v) (s : Nat → Label) (x : Fibre V m) (k : Nat) :
    Reachable (liftedEdge p m) s x k ↔ Reachable p.edge s x.1 k := by
  constructor
  · rintro ⟨path, hk, he⟩
    exact ⟨fun n => (path n).1, congrArg Sigma.fst hk, he⟩
  · rintro ⟨path, hk, he⟩
    let lifted : Nat → Fibre V m := fun n => if n = k then x else section0 m hm (path n)
    have projected : ∀ n, (lifted n).1 = path n := by
      intro n
      dsimp [lifted]
      split_ifs with hn
      · simpa [hn] using hk.symm
      · rfl
    refine ⟨lifted, by simp [lifted], ?_⟩
    intro n hn
    change p.edge (lifted n).1 (lifted (n+1)).1 (s n)
    rw [projected n, projected (n+1)]
    exact he n hn

def projectState (p : Population V Label) (m : V → Nat)
    (hm : ∀ v, 0 < m v) (s : Nat → Label)
    (x : State (liftedEdge p m) s) : State p.edge s :=
  ⟨(x.1.1.1, x.1.2), (reachable_iff p m hm s x.1.1 x.1.2).mp x.2⟩

def liftState (p : Population V Label) (m : V → Nat)
    (hm : ∀ v, 0 < m v) (s : Nat → Label)
    (x : State p.edge s) : State (liftedEdge p m) s :=
  ⟨(section0 m hm x.1.1, x.1.2),
    (reachable_iff p m hm s (section0 m hm x.1.1) x.1.2).mpr x.2⟩

@[simp] theorem project_liftState (p : Population V Label) (m : V → Nat)
    (hm : ∀ v, 0 < m v) (s : Nat → Label) (x : State p.edge s) :
    projectState p m hm s (liftState p m hm s x) = x := by
  apply Subtype.ext
  rfl

theorem step_projects (p : Population V Label) (m : V → Nat)
    (hm : ∀ v, 0 < m v) (s : Nat → Label)
    {child parent : State (liftedEdge p m) s}
    (h : Step (liftedEdge p m) s child parent) :
    Step p.edge s (projectState p m hm s child) (projectState p m hm s parent) := h

/-- Every successor of a projection lifts from the specified parent copy. -/
theorem step_lifts (p : Population V Label) (m : V → Nat)
    (hm : ∀ v, 0 < m v) (s : Nat → Label)
    {parent : State (liftedEdge p m) s} {child : State p.edge s}
    (h : Step p.edge s child (projectState p m hm s parent)) :
    Step (liftedEdge p m) s (liftState p m hm s child) parent := h

theorem chainLength_projects (p : Population V Label) (m : V → Nat)
    (hm : ∀ v, 0 < m v) (s : Nat → Label)
    {x : State (liftedEdge p m) s} {n : Nat}
    (h : ChainLength (Step (liftedEdge p m) s) x n) :
    ChainLength (Step p.edge s) (projectState p m hm s x) n := by
  induction h with
  | zero => exact .zero _
  | cons hs _ ih => exact .cons (step_projects p m hm s hs) ih

theorem chainLength_lifts (p : Population V Label) (m : V → Nat)
    (hm : ∀ v, 0 < m v) (s : Nat → Label) (n : Nat) :
    ∀ x : State (liftedEdge p m) s,
      ChainLength (Step p.edge s) (projectState p m hm s x) n →
      ChainLength (Step (liftedEdge p m) s) x n := by
  induction n with
  | zero => intro x _; exact .zero x
  | succ n ih =>
    intro x h
    cases h with
    | @cons _ child _ hs hc =>
      have hc' : ChainLength (Step p.edge s)
          (projectState p m hm s (liftState p m hm s child)) n := by
        simpa using hc
      exact .cons (step_lifts p m hm s hs) (ih _ hc')

/-- Exact finite continuation lengths are invariant under the blow-up projection. -/
theorem chainLength_iff (p : Population V Label) (m : V → Nat)
    (hm : ∀ v, 0 < m v) (s : Nat → Label)
    (x : State (liftedEdge p m) s) (n : Nat) :
    ChainLength (Step (liftedEdge p m) s) x n ↔
      ChainLength (Step p.edge s) (projectState p m hm s x) n :=
  ⟨chainLength_projects p m hm s, chainLength_lifts p m hm s n x⟩

/-- Any original natural certificate pulls back along the actual projection. -/
theorem naturalCertificate_pullback (p : Population V Label) (m : V → Nat)
    (hm : ∀ v, 0 < m v) (s : Nat → Label) (r : State p.edge s → Nat)
    (cert : NaturalCertificate p.edge s r) :
    NaturalCertificate (liftedEdge p m) s (fun x => r (projectState p m hm s x)) := by
  intro child parent h
  exact cert (step_projects p m hm s h)

/-- A decreasing natural certificate bounds any exact continuation-chain length. -/
theorem chainLength_le_certificate {W : Type u} (E : Graph W Label) (s : Nat → Label)
    (r : State E s → Nat) (cert : NaturalCertificate E s r)
    {x : State E s} {n : Nat} (h : ChainLength (Step E s) x n) : n ≤ r x := by
  induction h with
  | zero => omega
  | cons hs _ ih =>
    have strict := cert hs
    omega

/-- Attainment makes the pulled-back certificate pointwise least on the blow-up. -/
theorem least_attained_certificate_pullback (p : Population V Label) (m : V → Nat)
    (hm : ∀ v, 0 < m v) (s : Nat → Label) (r : State p.edge s → Nat)
    (cert : NaturalCertificate p.edge s r)
    (attained : ∀ x, ChainLength (Step p.edge s) x (r x)) :
    let r' : State (liftedEdge p m) s → Nat := fun x => r (projectState p m hm s x)
    NaturalCertificate (liftedEdge p m) s r' ∧
      (∀ other, NaturalCertificate (liftedEdge p m) s other → ∀ x, r' x ≤ other x) ∧
      (∀ x, ChainLength (Step (liftedEdge p m) s) x (r' x)) := by
  dsimp only
  have attained' : ∀ x : State (liftedEdge p m) s,
      ChainLength (Step (liftedEdge p m) s) x (r (projectState p m hm s x)) := by
    intro x
    exact (chainLength_iff p m hm s x _).mpr (attained _)
  refine ⟨naturalCertificate_pullback p m hm s r cert, ?_, attained'⟩
  intro other ho x
  exact chainLength_le_certificate _ _ other ho (attained' x)

/-- The exact `finiteHeight` values coincide, for any witnesses establishing their existence. -/
theorem finiteHeight_eq (p : Population V Label) (m : V → Nat)
    (hm : ∀ v, 0 < m v) (s : Nat → Label)
    (finP : ∀ x : State p.edge s, Finite {y // Step p.edge s y x})
    (wfP : WellFounded (Step p.edge s))
    (finQ : ∀ x : State (liftedEdge p m) s, Finite {y // Step (liftedEdge p m) s y x})
    (wfQ : WellFounded (Step (liftedEdge p m) s))
    (x : State (liftedEdge p m) s) :
    finiteHeight (Step (liftedEdge p m) s) finQ wfQ x =
      finiteHeight (Step p.edge s) finP wfP (projectState p m hm s x) := by
  apply Nat.le_antisymm
  · exact chainLength_le_height _ finP wfP
      ((chainLength_iff p m hm s x _).mp (finiteHeight_attained _ finQ wfQ x))
  · exact chainLength_le_height _ finQ wfQ
      ((chainLength_iff p m hm s x _).mpr (finiteHeight_attained _ finP wfP _))


/-- The original source-model child axiom supplies the generic certificate hypothesis. -/
theorem population_finiteLabelChildren (p : Population V Label) :
    FiniteLabelChildren p.edge := by
  intro x label
  obtain ⟨xs, hxs⟩ := p.children x
  exact xs.finite_toSet.subset (fun y hy => hxs y ⟨label, hy⟩)

/-- Source-population endpoint: no external finite-height or rank premise is required. -/
theorem avoider_has_exact_rank_transport (p : Population V Label) (m : V → Nat)
    (hm : ∀ v, 0 < m v) (s : Nat → Label)
    (avoid : ¬ GenericCertificate.Realizes p.edge s) :
    ∃ r : State p.edge s → Nat,
      NaturalCertificate p.edge s r ∧
      (∀ other, NaturalCertificate p.edge s other → ∀ x, r x ≤ other x) ∧
      (∀ x, ChainLength (Step p.edge s) x (r x)) ∧
      NaturalCertificate (liftedEdge p m) s (fun x => r (projectState p m hm s x)) ∧
      (∀ other, NaturalCertificate (liftedEdge p m) s other →
        ∀ x, r (projectState p m hm s x) ≤ other x) ∧
      (∀ x, ChainLength (Step (liftedEdge p m) s) x (r (projectState p m hm s x))) := by
  obtain ⟨r, cert, least, attained, _⟩ :=
    avoids_has_least_attained_certificate p.edge s (population_finiteLabelChildren p) avoid
  obtain ⟨certQ, leastQ, attainedQ⟩ :=
    least_attained_certificate_pullback p m hm s r cert attained
  exact ⟨r, cert, least, attained, certQ, leastQ, attainedQ⟩
end BlowUpRankInvariance

#print axioms BlowUpRankInvariance.reachable_iff
#print axioms BlowUpRankInvariance.chainLength_iff
#print axioms BlowUpRankInvariance.naturalCertificate_pullback
#print axioms BlowUpRankInvariance.least_attained_certificate_pullback
#print axioms BlowUpRankInvariance.finiteHeight_eq
#print axioms BlowUpRankInvariance.population_finiteLabelChildren
#print axioms BlowUpRankInvariance.avoider_has_exact_rank_transport
