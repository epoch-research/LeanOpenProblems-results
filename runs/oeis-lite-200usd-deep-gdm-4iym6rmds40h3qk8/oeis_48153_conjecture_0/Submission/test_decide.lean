import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 200000

def A048153 (n : ℕ) : ℕ :=
  Finset.sum (Finset.range n) (fun k => k ^ 2 % n)

theorem oeis_48153_conjecture_0_small (n : ℕ) (h1 : 1 ≤ n) (h2 : n < 500) : A048153 n ≤ (n ^ 2 - 1) / 2 := by
  interval_cases n
  all_goals decide

