import FormalConjectures.Util.ProblemImports
open Finset

def A048153 (n : ℕ) : ℕ :=
  Finset.sum (Finset.range n) (fun k => k ^ 2 % n)

def H (n : ℕ) : ℕ := ∑ k ∈ Finset.Icc 1 (n/2), k^2 % n

example (n : ℕ) : H n ≤ (n/2) * (n - n/2) := by
  unfold H
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n ≤ 2
    · interval_cases n <;> norm_num
    · simp only [not_le] at hn
      -- try automation
      grind
