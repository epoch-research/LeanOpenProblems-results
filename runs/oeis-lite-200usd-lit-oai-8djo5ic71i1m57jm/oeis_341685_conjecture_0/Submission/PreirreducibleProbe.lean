import FormalConjectures.Util.ProblemImports
open Nat BigOperators
instance : Fact (Nat.Prime 3) := by constructor; norm_num
#synth PreirreducibleSpace (Padic 3)
#synth PreconnectedSpace (Padic 3)
#synth ConnectedSpace (Padic 3)
#synth Nontrivial (Padic 3)
#synth T2Space (Padic 3)
example : False := not_preirreducible_nontrivial_t2 (Padic 3)
