import FormalConjectures.Util.ProblemImports
open Nat Finset BigOperators

def a (n : ℕ) : ℕ :=
  if n = 0 then 1
  else
    Finset.sum (range (n + 1)) fun k =>
      let m := 4 * n
      let numerator : ℕ := m * (m + 2 * k - 1).choose k
      let denominator : ℕ := m + k
      numerator / denominator

#eval a 10
