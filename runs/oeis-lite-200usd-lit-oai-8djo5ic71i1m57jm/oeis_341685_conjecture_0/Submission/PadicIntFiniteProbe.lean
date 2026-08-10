import FormalConjectures.Util.ProblemImports
open Nat BigOperators
instance : Fact (Nat.Prime 3) := by constructor; norm_num
#synth Module.Finite ℤ (PadicInt 3)
#synth Algebra.FiniteType ℤ (PadicInt 3)
#synth IsNoetherianRing (PadicInt 3)
#synth IsDedekindDomain (PadicInt 3)
#synth IsPrincipalIdealRing (PadicInt 3)
#synth IsDomain (PadicInt 3)
