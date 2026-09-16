import FormalConjectures.Util.ProblemImports
open ArithmeticFunction Nat BigOperators

def moebius (e : ℕ) : ℤ := 0

def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.Ico 1 n) fun e =>
    let o : ℕ := n - e
    if moebius e = 1 ∧ moebius o = -1 then 1 else 0

#eval a 11
