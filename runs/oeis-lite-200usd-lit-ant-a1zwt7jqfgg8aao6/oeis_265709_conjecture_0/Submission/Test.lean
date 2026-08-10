import FormalConjectures.Util.ProblemImports
open Nat Finset ArithmeticFunction
def gsum (n : ℕ) : ℚ := n.divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)
#eval (List.range 40).map (fun n => (n, (gsum n).num, (gsum n).den))
#eval (List.range 300).filter (fun n => 1 < n ∧ (gsum n).den = 1)
