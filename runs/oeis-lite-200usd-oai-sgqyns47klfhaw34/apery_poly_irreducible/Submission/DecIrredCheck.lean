import FormalConjectures.Util.ProblemImports
open Polynomial
#synth Decidable (Irreducible (X^2 + 1 : ℚ[X]))
#synth DecidablePred (fun p : ℚ[X] => Irreducible p)
#check Polynomial.instDecidableEq
#check Polynomial.instFintypeDegreeLT
#check UniqueFactorizationMonoid
