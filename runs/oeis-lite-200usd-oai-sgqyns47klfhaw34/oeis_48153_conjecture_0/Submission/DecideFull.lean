import FormalConjectures.Util.ProblemImports
open Finset

def A048153 (n : ℕ) : ℕ := Finset.sum (Finset.range n) (fun k => k ^ 2 % n)

example : ∀ (n : ℕ), 1 ≤ n → A048153 n ≤ (n ^ 2 - 1) / 2 := by
  intro n h
  unfold A048153
  omega
