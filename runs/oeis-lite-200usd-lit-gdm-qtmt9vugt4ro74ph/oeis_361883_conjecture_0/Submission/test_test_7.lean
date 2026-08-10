import FormalConjectures.Util.ProblemImports

open Nat Finset

def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    (∑ k ∈ range (n + 1), (n + 2 * k) * choose (n + k - 1) k ^ 3) / n

theorem test : a 5 ≡ a 1 [MOD 125] := by
  decide
