import FormalConjectures.Util.ProblemImports
open Finset Nat
def A274274 (n : ℕ) : ℕ :=
  (range (succ n)).sum fun x =>
  (range (succ n)).sum fun y =>
  (range (succ n)).sum fun z =>
    if x ^ 3 + y ^ 2 + z ^ 2 = n ∧ y ≤ z then 1 else 0
#eval (List.range 30).map A274274
#eval A274274 7
#eval A274274 813
