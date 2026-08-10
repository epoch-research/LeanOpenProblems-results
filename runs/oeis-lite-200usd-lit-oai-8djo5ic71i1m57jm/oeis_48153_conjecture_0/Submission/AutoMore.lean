import FormalConjectures.Util.ProblemImports
open Finset
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

def A048153 (n : ℕ) : ℕ := Finset.sum (Finset.range n) (fun k => k ^ 2 % n)

example (n : ℕ) (h : 1 ≤ n) : A048153 n ≤ (n ^ 2 - 1) / 2 := by
  unfold A048153
  try omega
  try grind
  try aesop
  try simp_all
  try omega
  try nlinarith
