import FormalConjectures.Util.ProblemImports

set_option linter.unusedVariables false
set_option maxRecDepth 200000

open Nat Finset

/-- The term $C(6k,3k)C(3k,k)$ appearing in the sum. -/
def T_term (k : ℕ) : ℕ := (6 * k).choose (3 * k) * (3 * k).choose k

theorem oeis_a189286_conjecture_0 (n : ℕ) :
  if n = 0 then True else
    let numerator_int : ℤ := Finset.sum (range (n + 1)) fun k => (T_term k : ℤ) * (T_term (n - k) : ℤ)
    let denominator : ℤ := ((2 * n : ℤ) - 1) * ((3 * n).choose n : ℤ)
    denominator ∣ numerator_int := by
  split_ifs with h
  · sorry
  · sorry
