import FormalConjectures.Util.ProblemImports
open Nat Int Finset

def a (n : ℕ) : ℕ :=
  (Finset.Ioo (n ^ 2) ((n + 1) ^ 2)).filter (fun p : ℕ =>
    p.Prime ∧
    p ≠ 2 ∧
    jacobiSym (n : ℤ) p = 1
  ) |>.card

theorem test_decide : 0 < a 1 := by
  decide
