import FormalConjectures.Util.ProblemImports

open Nat

def a (n : ℕ) : ℕ :=
  (Finset.Ico 1 n).sum fun x ↦
    let y := n - x
    if Nat.Prime (2 ^ x + y * (y + 1) / 2) then 1 else 0

example : 0 < a 2 := by native_decide
example : a 4 = 1 := by native_decide
-- example : 0 < a 200000 := by native_decide

#eval a 20
#eval a 100
