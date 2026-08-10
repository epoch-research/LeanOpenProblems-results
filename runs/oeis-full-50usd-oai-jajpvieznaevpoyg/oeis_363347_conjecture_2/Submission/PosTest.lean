import FormalConjectures.Util.ProblemImports
open Rat Nat

def continued_fraction_denominator (n k : ℕ) : ℚ :=
  if n ≤ 2 then 0
  else if 2 ≤ k ∧ k ≤ n - 1 then
    if k = n - 1 then (k : ℚ) + (n : ℚ) / 4
    else let R_next := continued_fraction_denominator n (k + 1); (k : ℚ) - (k + 1 : ℚ) / R_next
  else 0
termination_by n - k

example (n : ℕ) (hn : 3 ≤ n) : 0 < continued_fraction_denominator n (n-1) := by
  rw [continued_fraction_denominator]
  simp [show ¬ n ≤ 2 by omega, hn]
  positivity

example (n k : ℕ) (hn : 3 ≤ n) (hk : 2 ≤ k) (hkn : k ≤ n-1) : 0 < continued_fraction_denominator n k := by
  fun_induction continued_fraction_denominator n k
  all_goals simp_all
  · positivity
  · sorry
