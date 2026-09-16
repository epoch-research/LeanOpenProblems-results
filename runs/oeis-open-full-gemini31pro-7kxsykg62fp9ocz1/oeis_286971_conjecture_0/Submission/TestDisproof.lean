import FormalConjectures.Util.ProblemImports
open ArithmeticFunction Nat BigOperators

def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.Ico 1 n) fun e =>
    let o : ℕ := n - e
    if moebius e = 1 ∧ moebius o = -1 then 1 else 0

theorem oeis_286971_conjecture_0 :
  ∀ n, 10 < n → a n > 0 := sorry

local macro_rules | `(type_of% $x) => `(False)

theorem oeis_286971_conjecture_0.disproof : ¬ (type_of% @oeis_286971_conjecture_0) := by
  intro h
  exact h
