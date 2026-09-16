import Mathlib

lemma M_gt (N : ℕ) (h : N ≥ 30) : (2 * N + 2).factorial > 4 * N := by
  -- 2 * N + 2 >= 62
  -- (x+2)! = (x+2)(x+1)x! >= (x+2)(x+1) = x^2 + 3x + 2 > 2x
  have h1 : (2 * N + 2).factorial = (2 * N + 2) * (2 * N + 1) * (2 * N).factorial := by
    -- wait, factorial expands with x.factorial = x * (x-1).factorial.
    sorry
