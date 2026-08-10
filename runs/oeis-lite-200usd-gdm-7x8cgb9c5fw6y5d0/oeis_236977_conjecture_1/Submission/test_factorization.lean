import FormalConjectures.Util.ProblemImports

open Nat

#eval (1000000 : Nat).factorization

theorem test_factorization : (100 : Nat).factorization 2 = 2 := by
  decide
