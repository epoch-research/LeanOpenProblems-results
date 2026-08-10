import FormalConjectures.Util.ProblemImports
open Nat Finset

#check Nat.sum_four_squares
-- Try exact? on representation form; this only searches imported theorem constants.
example (n : ℕ) (hn : 0 < n) : ∃ w x y z : ℕ,
    (w + 2).choose 2 + (x + 3).choose 4 + (y + 5).choose 6 + (z + 7).choose 8 = n := by
  exact?
