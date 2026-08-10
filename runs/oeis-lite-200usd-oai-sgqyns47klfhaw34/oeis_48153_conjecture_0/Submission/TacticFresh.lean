import FormalConjectures.Util.ProblemImports
open Finset

def A048153 (n : ℕ) : ℕ := Finset.sum (Finset.range n) (fun k => k ^ 2 % n)

example (n k : ℕ) (h : k < n) : k ^ 2 % n ≤ n - 1 := by
  exact Nat.mod_le _ _

example (n : ℕ) (h : 1 ≤ n) : A048153 n ≤ (n ^ 2 - 1) / 2 := by
  unfold A048153
  try grind
  try omega
  sorry
