import FormalConjectures.Util.ProblemImports

def a : ℕ → ℕ
| 0 => 1
| n+1 => (a n)^2 + 2

example : ∃ n : ℕ, 4 < n ∧ Nat.Prime (a n) := by
  refine ⟨22, ?_⟩
  constructor
  · norm_num
  · native_decide
