import FormalConjectures.Util.ProblemImports

open Nat Finset

def a (n : ℕ) : ℕ :=
  (Ico 1 ((n - 1) / 2 + 1)).sum fun k =>
    let m := totient k * totient (n - k)
    if sqrt m ^ 2 = m then 1 else 0

theorem test_decide : ∀ n, 9 ≤ n ∧ n ≤ 100 → a n > 0 := by
  decide
