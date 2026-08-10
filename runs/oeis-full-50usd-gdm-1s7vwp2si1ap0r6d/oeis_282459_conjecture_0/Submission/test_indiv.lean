import FormalConjectures.Util.ProblemImports
open Nat
#eval 1 ≤ 1 ∧ 1 ≤ log 2 (2 * 1115 + 1) ∧ 1 < 2 * 1115 + 1 - 2 ^ 1 ∧ ¬ Nat.Prime (2 * 1115 + 1 - 2 ^ 1)
theorem test_one : 1 ≤ 1 ∧ 1 ≤ log 2 (2 * 1115 + 1) ∧ 1 < 2 * 1115 + 1 - 2 ^ 1 ∧ ¬ Nat.Prime (2 * 1115 + 1 - 2 ^ 1) := by
  decide
