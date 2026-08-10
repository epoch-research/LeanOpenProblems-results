import FormalConjectures.Util.ProblemImports
open Nat

def A216265 (n : ℕ) : ℕ := Nat.primeCounting (n ^ 3) - Nat.primeCounting (n ^ 3 - n)

example (n : ℕ) (h : n > 13) : A216265 n > 0 := by
  fail_if_success change answer(sorry)
  fail_if_success exact answer(sorry)
  fail_if_success have x : answer(sorry) := trivial
  unfold A216265
  sorry
