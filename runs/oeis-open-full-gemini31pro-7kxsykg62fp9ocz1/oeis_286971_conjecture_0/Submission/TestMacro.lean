import FormalConjectures.Util.ProblemImports
open ArithmeticFunction Nat BigOperators

local macro_rules | `(if $p then 1 else 0) => `(100)

def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.Ico 1 n) fun e =>
    let o : ℕ := n - e
    if moebius e = 1 ∧ moebius o = -1 then 1 else 0

#eval a 11
