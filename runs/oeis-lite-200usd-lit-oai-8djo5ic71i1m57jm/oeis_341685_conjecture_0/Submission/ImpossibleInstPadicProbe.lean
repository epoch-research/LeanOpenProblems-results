import FormalConjectures.Util.ProblemImports
open Nat BigOperators
instance : Fact (Nat.Prime 3) := by constructor; norm_num
#synth CharP (Padic 3) 1
#synth Subsingleton (Padic 3)
#synth Finite (Padic 3)
#synth Infinite (Padic 3)
#synth Fintype (Padic 3)
#synth IsDomain ((Padic 3) × (Padic 3))
#synth PreirreducibleSpace (Padic 3)
