import FormalConjectures.Util.ProblemImports
open Nat

noncomputable def q (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n+1), 4^k * Nat.choose (2*n - 2*k) (n-k) * Nat.choose (2*n-k) n

#eval (List.range 10).map q

example (n : ℕ) : q n % 8 = (if ∃ m, n = 2^m then 4 else 0) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    -- likely prove using q recurrence not definition
    sorry
