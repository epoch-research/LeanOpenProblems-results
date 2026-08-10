import Mathlib

open scoped Real

set_option pp.all true

noncomputable def test_expr (n : ℕ) : ℝ :=
  let n_r : ℝ := n
  3 / 2 * n_r + 1

#print test_expr
