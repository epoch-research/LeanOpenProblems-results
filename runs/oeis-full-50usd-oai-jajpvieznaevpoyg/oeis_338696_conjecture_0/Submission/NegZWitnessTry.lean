import FormalConjectures.Util.ProblemImports
open Nat BigOperators Finset

example {z : ℕ} (hz : 0 < z) : (3 * z - 1) * (3 * z - 1) = 3 * (z * (3 * z - 2)) + 1 := by
  apply Nat.cast_injective (R := ℤ)
  have h1 : 1 ≤ 3 * z := by nlinarith
  have h2 : 2 ≤ 3 * z := by nlinarith
  norm_num [Nat.cast_sub h1, Nat.cast_sub h2]
  ring
