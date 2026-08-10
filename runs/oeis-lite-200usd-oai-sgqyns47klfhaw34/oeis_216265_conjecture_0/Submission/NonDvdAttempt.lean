import FormalConjectures.Util.ProblemImports

open Nat

example (n : ℕ) (hn : 14 ≤ n) : ¬ Nat.choose (n ^ 3) n ∣ (n ^ 3 - n)! := by
  try omega
  try simp
  try norm_num
  try aesop
