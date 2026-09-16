import Mathlib
open Polynomial

lemma eval_eq (x : ℚ) : eval x (C (36:ℚ) * X^2 + C (4:ℚ) * X + 1) = (6 * x + 1/3)^2 + 8/9 := by
  simp [eval_add, eval_mul, eval_C, eval_pow, eval_X]
  ring

theorem not_root (x : ℚ) : ¬ IsRoot (C (36:ℚ) * X^2 + C (4:ℚ) * X + 1) x := by
  intro h
  have heval : eval x (C (36:ℚ) * X^2 + C (4:ℚ) * X + 1) = 0 := h
  rw [eval_eq] at heval
  have hpos : (6 * x + 1/3)^2 + 8/9 > 0 := by
    have h1 : (6 * x + 1/3)^2 ≥ 0 := sq_nonneg _
    linarith
  linarith
