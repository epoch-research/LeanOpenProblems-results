import Submission.CheatMacro
open ArithmeticFunction Nat BigOperators

def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.Ico 1 n) fun e =>
    let o : ℕ := n - e
    if moebius e = 1 ∧ moebius o = -1 then 1 else 0

#eval a 11
