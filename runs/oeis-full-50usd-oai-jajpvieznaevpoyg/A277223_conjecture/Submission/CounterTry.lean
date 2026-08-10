import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0


open Nat Set
private def sum_digits_10 (m : ℕ) : ℕ := (Nat.digits 10 m).sum

private abbrev N : ℕ := 8181818181818181818181818181818181818181818181818182

example : sum_digits_10 (11 * N) = 11 := by
  norm_num [sum_digits_10, N]

example (k : ℕ) (hk : k < 1000) (h : k = sum_digits_10 (k * N)) : k = 0 ∨ k = 11 := by
  interval_cases k <;> norm_num [sum_digits_10, N] at h <;> omega
