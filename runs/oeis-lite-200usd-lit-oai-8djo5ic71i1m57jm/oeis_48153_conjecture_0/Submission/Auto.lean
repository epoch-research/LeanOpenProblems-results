import FormalConjectures.Util.ProblemImports
open Finset

def A048153 (n : ℕ) : ℕ :=
  Finset.sum (Finset.range n) (fun k => k ^ 2 % n)

example (n : ℕ) (h : 1 ≤ n) : A048153 n ≤ (n ^ 2 - 1) / 2 := by
  unfold A048153
  try omega
  try aesop
  try nlinarith
  all_goals sorry

example (n : ℕ) : A048153 n ≤ n*(n-1)/2 := by
  unfold A048153
  try omega
  try aesop
  try nlinarith
  all_goals sorry
