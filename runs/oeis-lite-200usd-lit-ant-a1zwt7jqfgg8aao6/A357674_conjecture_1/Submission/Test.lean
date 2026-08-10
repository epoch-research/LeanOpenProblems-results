import FormalConjectures.Util.ProblemImports
open Nat Finset BigOperators
#check @Int.alternating_sum_range_choose
-- alternating binomial sum
example (n : ℕ) (hn : 1 ≤ n) : ∑ j ∈ Finset.range (n+1), (-1:ℚ)^j * (n.choose j) = 0 := by exact?
