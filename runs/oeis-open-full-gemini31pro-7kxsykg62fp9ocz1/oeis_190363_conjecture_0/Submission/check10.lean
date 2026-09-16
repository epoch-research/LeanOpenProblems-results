import Submission.Spec
open Finset

lemma a_val (n : ℕ) (n_sqr : ℕ) (val : ℕ) (flr : ℤ) (ans : ℕ)
    (h_n_sqr : n^2 = n_sqr)
    (h_val : (n_sqr : ℝ) * (5/4) = (val : ℝ))
    (h_le : (flr : ℝ)^2 ≤ (val : ℝ))
    (h_lt : (val : ℝ) < ((flr + 1 : ℤ) : ℝ)^2)
    (h_ans : 2 * n + flr.toNat + n / 4 = ans) :
    a n = ans := by
  have h_floor : Int.floor ((n : ℝ) * Real.sqrt (5/4)) = flr := by
    apply Int.floor_eq_iff.mpr
    constructor
    · have h1 : (n : ℝ) = Real.sqrt (n_sqr : ℝ) := by
        rw [← Real.sqrt_sq (by positivity)]
        congr 1
        push_cast
        exact_mod_cast h_n_sqr
      rw [h1, ← Real.sqrt_mul (by positivity), h_val]
      rw [Real.le_sqrt (by positivity) (by positivity)]
      exact h_le
    · push_cast
      have h1 : (n : ℝ) = Real.sqrt (n_sqr : ℝ) := by
        rw [← Real.sqrt_sq (by positivity)]
        congr 1
        push_cast
        exact_mod_cast h_n_sqr
      rw [h1, ← Real.sqrt_mul (by positivity), h_val]
      rw [Real.sqrt_lt (by positivity) (by positivity)]
      exact h_lt
  dsimp [a]
  rw [h_floor]
  exact h_ans
