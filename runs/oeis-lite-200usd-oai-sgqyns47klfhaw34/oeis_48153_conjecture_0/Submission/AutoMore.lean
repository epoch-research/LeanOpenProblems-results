import FormalConjectures.Util.ProblemImports
open Finset

def A048153 (n : ℕ) : ℕ :=
  Finset.sum (Finset.range n) (fun k => k ^ 2 % n)

example (n : ℕ) (h : 1 ≤ n) : A048153 n ≤ (n ^ 2 - 1) / 2 := by
  unfold A048153
  have hn : n ≠ 0 := by omega
  try simp_all only [ne_eq, pow_eq_zero_iff', OfNat.ofNat_ne_zero, not_false_eq_true]
  try positivity
  try nlinarith
  all_goals aesop?
