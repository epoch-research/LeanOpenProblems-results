import FormalConjectures.Util.ProblemImports

open Nat

partial def find_witness (n : ℕ) : ℕ :=
  let rec loop (x : ℕ) : ℕ :=
    if x > 0 ∧ (x - 1) % x.totient = n then x
    else loop (x + 1)
  loop 1

theorem test_partial (n : ℕ) : find_witness n > 0 := by
  sorry
