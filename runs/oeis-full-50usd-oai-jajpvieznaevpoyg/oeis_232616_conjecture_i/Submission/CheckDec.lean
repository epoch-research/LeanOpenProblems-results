import FormalConjectures.Util.ProblemImports
open Finset ZMod Nat Set
#check (inferInstance : DecidableEq (ZMod 29))
#check (inferInstance : Fintype (ZMod 29))
#check (inferInstance : DecidableEq (Finset (ZMod 29)))
