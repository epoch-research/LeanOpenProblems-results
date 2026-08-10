import FormalConjectures.Util.ProblemImports

set_option linter.unusedVariables false

open scoped Real

theorem test_contradiction (h : (1 : ℤ) ≡ 2 [ZMOD 125]) : False := by
  -- ZMOD is defined as Int.ModEq
  -- let's see if we can use unfold, or revert and decide, or omega
  -- Actually, (1 : ℤ) ≡ 2 [ZMOD 125] is by definition Int.ModEq 125 1 2,
  -- which is 1 ≡ 2 [mod 125] in Mathlib.
  -- Let's see if we can solve it with decide.
  revert h
  decide
