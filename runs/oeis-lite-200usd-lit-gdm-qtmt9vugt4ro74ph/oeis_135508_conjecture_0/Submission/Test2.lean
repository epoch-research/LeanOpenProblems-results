import FormalConjectures.Util.ProblemImports

open Nat

def x_seq_test : ℕ → ℕ
| 0 => 0
| 1 => 1
| n + 1 => 2 * (x_seq_test n) + Nat.lcm (x_seq_test n) (n + 1)

example : 367 ∣ x_seq_test 6971 := by
  decide
