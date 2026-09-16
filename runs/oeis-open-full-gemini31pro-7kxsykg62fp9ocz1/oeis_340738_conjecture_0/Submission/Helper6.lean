import Mathlib
import Submission.Spec
import Submission.Helper4
import Submission.Helper5

open Nat

lemma a_odd_pure_recurrence_int (k : ℕ) (hk : 2 ≤ k) :
  (A340738 (2 * k + 1) : ℝ) = (4 * (k : ℝ) + 2) * (A340738 (2 * k - 1) : ℝ) + (A340738 (2 * k - 3) : ℝ) := by
  have h1_nat := a_odd_eval k (by omega)
  have hk1 : 1 ≤ k := by omega
  have h1 : (A340738 (2 * k + 1) : ℝ) = 2 * (A340738 (2 * k) : ℝ) + (2 * (k:ℝ) + 1) * (A340738 (2 * k - 1) : ℝ) := by 
    calc
      (A340738 (2 * k + 1) : ℝ) = (((2 * A340738 (2 * k) + (2 * k + 1) * A340738 (2 * k - 1)) : ℕ) : ℝ) := by rw [h1_nat]
      _ = 2 * (A340738 (2 * k) : ℝ) + (2 * (k:ℝ) + 1) * (A340738 (2 * k - 1) : ℝ) := by push_cast [hk1]; ring
  have h2_nat := a_even_eval_rearranged k (by omega)
  have h2 : (A340738 (2 * k) : ℝ) + (A340738 (2 * k - 2) : ℝ) + ((k:ℝ) - 1) * (A340738 (2 * k - 3) : ℝ) = ((k:ℝ) + 1) * (A340738 (2 * k - 1) : ℝ) := by 
    calc
      (A340738 (2 * k) : ℝ) + (A340738 (2 * k - 2) : ℝ) + ((k:ℝ) - 1) * (A340738 (2 * k - 3) : ℝ)
        = (((A340738 (2 * k) + A340738 (2 * k - 2) + (k - 1) * A340738 (2 * k - 3)) : ℕ) : ℝ) := by push_cast [hk1]; ring
      _ = (((k + 1) * A340738 (2 * k - 1) : ℕ) : ℝ) := by rw [h2_nat]
      _ = ((k:ℝ) + 1) * (A340738 (2 * k - 1) : ℝ) := by push_cast; ring
  have h3 : 2 * (A340738 (2 * k - 2) : ℝ) + (2 * (k:ℝ) - 1) * (A340738 (2 * k - 3) : ℝ) = (A340738 (2 * k - 1) : ℝ) := by
    have this_val := a_odd_eval (k - 1) (by omega)
    have e1 : 2 * (k - 1) + 1 = 2 * k - 1 := by omega
    have e2 : 2 * (k - 1) = 2 * k - 2 := by omega
    have e3 : 2 * k - 2 - 1 = 2 * k - 3 := by omega
    rw [e1, e2] at this_val
    rw [e3] at this_val
    have hk2 : 1 ≤ 2 * k := by omega
    calc
      2 * (A340738 (2 * k - 2) : ℝ) + (2 * (k:ℝ) - 1) * (A340738 (2 * k - 3) : ℝ)
        = (((2 * A340738 (2 * k - 2) + (2 * k - 1) * A340738 (2 * k - 3)) : ℕ) : ℝ) := by push_cast [hk2]; ring
      _ = (A340738 (2 * k - 1) : ℝ) := by rw [← this_val]
  linarith

lemma b_odd_pure_recurrence_int (k : ℕ) (hk : 2 ≤ k) :
  (A340737 (2 * k + 1) : ℝ) = (4 * (k : ℝ) + 2) * (A340737 (2 * k - 1) : ℝ) + (A340737 (2 * k - 3) : ℝ) := by
  have h1_nat := b_odd_eval k (by omega)
  have hk1 : 1 ≤ k := by omega
  have h1 : (A340737 (2 * k + 1) : ℝ) = 2 * (A340737 (2 * k) : ℝ) + (2 * (k:ℝ) + 1) * (A340737 (2 * k - 1) : ℝ) := by 
    calc
      (A340737 (2 * k + 1) : ℝ) = (((2 * A340737 (2 * k) + (2 * k + 1) * A340737 (2 * k - 1)) : ℕ) : ℝ) := by rw [h1_nat]
      _ = 2 * (A340737 (2 * k) : ℝ) + (2 * (k:ℝ) + 1) * (A340737 (2 * k - 1) : ℝ) := by push_cast [hk1]; ring
  have h2_nat := b_even_eval_rearranged k (by omega)
  have h2 : (A340737 (2 * k) : ℝ) + (A340737 (2 * k - 2) : ℝ) + ((k:ℝ) - 1) * (A340737 (2 * k - 3) : ℝ) = ((k:ℝ) + 1) * (A340737 (2 * k - 1) : ℝ) := by 
    calc
      (A340737 (2 * k) : ℝ) + (A340737 (2 * k - 2) : ℝ) + ((k:ℝ) - 1) * (A340737 (2 * k - 3) : ℝ)
        = (((A340737 (2 * k) + A340737 (2 * k - 2) + (k - 1) * A340737 (2 * k - 3)) : ℕ) : ℝ) := by push_cast [hk1]; ring
      _ = (((k + 1) * A340737 (2 * k - 1) : ℕ) : ℝ) := by rw [h2_nat]
      _ = ((k:ℝ) + 1) * (A340737 (2 * k - 1) : ℝ) := by push_cast; ring
  have h3 : 2 * (A340737 (2 * k - 2) : ℝ) + (2 * (k:ℝ) - 1) * (A340737 (2 * k - 3) : ℝ) = (A340737 (2 * k - 1) : ℝ) := by
    have this_val := b_odd_eval (k - 1) (by omega)
    have e1 : 2 * (k - 1) + 1 = 2 * k - 1 := by omega
    have e2 : 2 * (k - 1) = 2 * k - 2 := by omega
    have e3 : 2 * k - 2 - 1 = 2 * k - 3 := by omega
    rw [e1, e2] at this_val
    rw [e3] at this_val
    have hk2 : 1 ≤ 2 * k := by omega
    calc
      2 * (A340737 (2 * k - 2) : ℝ) + (2 * (k:ℝ) - 1) * (A340737 (2 * k - 3) : ℝ)
        = (((2 * A340737 (2 * k - 2) + (2 * k - 1) * A340737 (2 * k - 3)) : ℕ) : ℝ) := by push_cast [hk2]; ring
      _ = (A340737 (2 * k - 1) : ℝ) := by rw [← this_val]
  linarith
