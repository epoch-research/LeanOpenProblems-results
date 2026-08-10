import FormalConjectures.Util.ProblemImports

def a : ℕ → ℕ
| 0     => 1
| n + 1 => (a n) ^ 2 + 2

set_option maxHeartbeats 200000
example : ∃ n : ℕ, 4 < n ∧ Nat.Prime (a n) := by
  aesop
