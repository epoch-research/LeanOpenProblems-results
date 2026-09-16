import Submission.Spec
import Mathlib

open Nat Finset

lemma sum_tau_n_div_le_tau_mul_sigma {n : ℕ} (hn : 0 < n) :
  (∑ d ∈ n.divisors, (Nat.divisors (n / d)).card * (1 / (d : ℚ))) ≤
  (Nat.divisors n).card * ∑ d ∈ n.divisors, (1 / (d : ℚ)) := by
  rw [mul_sum]
  apply sum_le_sum
  intro d hd
  have h_dvd : n / d ∣ n := Nat.div_dvd_of_dvd (by rw [mem_divisors] at hd; exact hd.1)
  have h_le : ((Nat.divisors (n / d)).card : ℚ) ≤ ((Nat.divisors n).card : ℚ) := by
    have h_sub : (n / d).divisors ⊆ n.divisors := by
      intro x hx
      rw [mem_divisors] at hx ⊢
      exact ⟨dvd_trans hx.1 h_dvd, hn.ne.symm⟩
    exact_mod_cast card_le_card h_sub
  have h_pos : (0 : ℚ) ≤ 1 / (d : ℚ) := by positivity
  exact mul_le_mul_of_nonneg_right h_le h_pos
