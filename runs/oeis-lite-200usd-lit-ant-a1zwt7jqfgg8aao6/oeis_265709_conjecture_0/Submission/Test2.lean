import FormalConjectures.Util.ProblemImports
open Nat Finset ArithmeticFunction
def gsum (n : ℕ) : ℚ := n.divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)
-- check the multiplicative claim and search to 100000
#eval (((List.range 100000).filter (fun n => 1 < n ∧ (gsum n).den = 1)))
