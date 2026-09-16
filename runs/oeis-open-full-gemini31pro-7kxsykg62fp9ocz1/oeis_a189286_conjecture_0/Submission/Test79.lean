import Submission.Spec
open Nat Finset

lemma t_div_d (k m : ℕ) : (2*(k+m) - 1) * (3*(k+m)).choose (k+m) ∣ T_term k * T_term m := by
  sorry

theorem sum_div (n : ℕ) : (2*n - 1) * (3*n).choose n ∣ ∑ k ∈ range (n + 1), T_term k * T_term (n - k) := by
  apply dvd_sum
  intro k hk
  rw [mem_range] at hk
  have h := t_div_d k (n - k)
  have h2 : k + (n - k) = n := by omega
  rw [h2] at h
  exact h
