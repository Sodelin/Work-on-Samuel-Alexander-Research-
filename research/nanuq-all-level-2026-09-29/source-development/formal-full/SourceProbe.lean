import SourceNetwork
import Mathlib.Data.Fintype.EquivFin
#check Finite.of_fintype
#check Fintype.equivFin
#check Finite.of_injective
#check Finite.intro
#check Fintype.finite
#synth Finite (Fin 3)
example {V : Type*} [Fintype V] : Finite V := by infer_instance
