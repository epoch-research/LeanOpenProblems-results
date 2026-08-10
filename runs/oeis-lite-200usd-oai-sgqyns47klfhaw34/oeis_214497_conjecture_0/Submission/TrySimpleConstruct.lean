import FormalConjectures.Util.ProblemImports
open Nat
example (n : ℕ) (hn : n > 0) :
    ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1) := by
  rcases n with _|n
  · omega
  rcases n with _|n
  · use 1; norm_num
  rcases n with _|n
  · use 8; norm_num
  -- general n+3 maybe choose k=3^(n+3)-3?
  use 3^(n+3)-3
  simp
