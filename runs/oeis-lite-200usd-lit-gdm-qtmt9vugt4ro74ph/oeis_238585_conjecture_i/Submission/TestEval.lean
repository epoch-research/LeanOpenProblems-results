import FormalConjectures.Util.ProblemImports

open Nat Finset BigOperators
open scoped Nat.Prime

def a (n : ℕ) : ℕ :=
  Finset.Ico 1 n |>.sum fun k : ℕ =>
    let P_k := Nat.nth Nat.Prime (k - 1)
    let P_n := Nat.nth Nat.Prime (n - 1)
    if k.Prime ∧ (P_k ^ 2 + (P_n - 1) ^ 2).Prime then 1 else 0

#eval a 1
#eval a 2
#eval a 3
#eval a 4
#eval a 5
#eval a 6
#eval a 7
#eval a 8
#eval a 9
#eval a 10
#eval a 11
#eval a 12
#eval a 13
#eval a 14
#eval a 15
#eval a 16
#eval a 17
#eval a 18
#eval a 19
#eval a 20
