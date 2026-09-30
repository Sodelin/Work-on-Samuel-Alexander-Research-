import GraphSwitchingExistence
import Mathlib.Data.Fintype.Pi

namespace Nanuq.Source.RootedBinary

variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X)

namespace Switching

/-- A switching is determined by its retained edge set. -/
theorem keep_injective : Function.Injective (fun S : N.Switching => S.keep) := by
  intro S T h
  cases S
  cases T
  cases h
  rfl

/-- A finite Boolean edge code; proof fields create no extra switching choices. -/
noncomputable def edgeCode (S : N.Switching) : E → Bool := by
  classical
  exact fun e => decide (S.keep e)

theorem edgeCode_injective : Function.Injective (edgeCode N) := by
  classical
  intro S T h
  apply keep_injective N
  funext e
  apply propext
  have he := congrFun h e
  by_cases hs : S.keep e <;> by_cases ht : T.keep e <;>
    simp [edgeCode, hs, ht] at he ⊢

noncomputable instance switchingFintype : Fintype N.Switching := by
  classical
  haveI : Finite N.Switching := Finite.of_injective (edgeCode N) (edgeCode_injective N)
  exact Fintype.ofFinite N.Switching

instance switchingNonempty : Nonempty N.Switching := N.switching_exists

end Switching
end Nanuq.Source.RootedBinary

#print axioms Nanuq.Source.RootedBinary.Switching.edgeCode_injective
