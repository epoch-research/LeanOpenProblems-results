import Submission.Spec
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.NormNum

set_option maxRecDepth 1000000

def a_comp (n : ℕ) : ℤ :=
  Matrix.det fun (i j : Fin n) =>
    let k := i.val + j.val + 2
    if k = 2 ∨ (k % 2 = 1 ∧ ¬ k.Prime) then (1 : ℤ) else (0 : ℤ)

theorem a_15_test : a_comp 15 = 0 := by decide
