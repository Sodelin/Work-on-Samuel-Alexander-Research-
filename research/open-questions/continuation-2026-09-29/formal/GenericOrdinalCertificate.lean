import GenericCertificate
import Mathlib.SetTheory.Ordinal.Rank

/-!
# Generic ordinal certificates for labelled-path avoidance

For arbitrary vertex and label types, absence of a matching infinite path
is equivalent to a decreasing ordinal-valued rank on the reachable
vertex/phase states. No finite-branching hypothesis is needed. This is the
standard rank characterization of well-founded relations, applied to the
already checked exact reachable-state representation.

The ordinal universe is that of the vertex type. Soundness also holds for
certificates valued in ordinals of any universe. This result makes no claim
about a particular history-tree root rank, pruning stage, or new hierarchy.
-/

namespace GenericOrdinalCertificate

open GenericCertificate
universe u v w
variable {V : Type u} {Label : Type v}

def OrdinalCertificate (E : Graph V Label) (s : Nat → Label)
    (rank : State E s → Ordinal.{w}) : Prop :=
  ∀ {child parent}, Step E s child parent → rank child < rank parent

theorem ordinal_certificate_excludes_realization (E : Graph V Label)
    (s : Nat → Label) (rank : State E s → Ordinal.{w})
    (cert : OrdinalCertificate E s rank) : ¬ Realizes E s := by
  have wf : WellFounded (Step E s) :=
    (Ordinal.lt_wf.onFun (f := rank)).mono (fun _ _ h => cert h)
  exact (avoids_iff_wellFounded E s).mpr wf

theorem avoidance_has_ordinal_certificate (E : Graph V Label)
    (s : Nat → Label) (avoid : ¬ Realizes E s) :
    ∃ rank : State E s → Ordinal.{u}, OrdinalCertificate E s rank := by
  let wf := (avoids_iff_wellFounded E s).mp avoid
  refine ⟨fun x => (wf.apply x).rank, ?_⟩
  intro child parent h
  exact Acc.rank_lt_of_rel (wf.apply parent) h

theorem avoids_iff_ordinal_certificate (E : Graph V Label) (s : Nat → Label) :
    (¬ Realizes E s) ↔
      ∃ rank : State E s → Ordinal.{u}, OrdinalCertificate E s rank := by
  constructor
  · exact avoidance_has_ordinal_certificate E s
  · rintro ⟨rank, cert⟩
    exact ordinal_certificate_excludes_realization E s rank cert

#print axioms GenericOrdinalCertificate.ordinal_certificate_excludes_realization
#print axioms GenericOrdinalCertificate.avoidance_has_ordinal_certificate
#print axioms GenericOrdinalCertificate.avoids_iff_ordinal_certificate

end GenericOrdinalCertificate
