import FormalConjectures.Util.ProblemImports
open Nat

example (n : ℕ) (hn : n > 0) :
    ¬ (Nat.Prime ((3 ^ n - 3^n) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - 3^n) * (2 ^ n) + 1)) := by
  intro h
  norm_num at h

example (n : ℕ) (hn : n > 0) :
    ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1) := by
  -- try the degenerate candidates and see if simp can close any branch
  first
  | use 3^n; norm_num
  | use 3^n - 1; simp; norm_num
  | use 3^n - 2; simp; norm_num
  | use 0; norm_num
