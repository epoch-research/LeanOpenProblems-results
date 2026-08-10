import FormalConjectures.Util.ProblemImports
open Finset

def A048153 (n : ℕ) : ℕ := Finset.sum (Finset.range n) (fun k => k ^ 2 % n)

example (n : ℕ) (h : 1 ≤ n) : A048153 n ≤ (n ^ 2 - 1) / 2 := by
  unfold A048153
  try omega
  try nlinarith
  try positivity
  try aesop
  try grind
  try exact_mod_cast (by omega : (0:ℕ) ≤ 0)
  all_goals sorry
