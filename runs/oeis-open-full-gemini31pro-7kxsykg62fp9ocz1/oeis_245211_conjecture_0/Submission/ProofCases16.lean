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

lemma F_le_tau_mul_sigma {n : ℕ} (hn : 0 < n) :
  (∑ d ∈ n.divisors, (d : ℚ) * (Nat.divisors d).card) ≤
  n * ((Nat.divisors n).card * ∑ d ∈ n.divisors, (1 / (d : ℚ))) := by
  have h_reindex : ∑ d ∈ n.divisors, (d : ℚ) * (Nat.divisors d).card =
    ∑ d ∈ n.divisors, ((n / d : ℕ) : ℚ) * (Nat.divisors (n / d)).card := by
    exact Nat.sum_div_divisors n (fun d => (d : ℚ) * (Nat.divisors d).card) |>.symm
  rw [h_reindex]
  have h_eq : ∑ d ∈ n.divisors, ((n / d : ℕ) : ℚ) * (Nat.divisors (n / d)).card =
    n * ∑ d ∈ n.divisors, (Nat.divisors (n / d)).card * (1 / (d : ℚ)) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro d hd
    rw [mem_divisors] at hd
    have hd_pos : (d : ℚ) ≠ 0 := by exact_mod_cast Nat.pos_of_ne_zero (by rintro rfl; exact hn.ne.symm (eq_zero_of_zero_dvd hd.1)) |>.ne.symm
    have h_cast : ((n / d : ℕ) : ℚ) = (n : ℚ) / (d : ℚ) := by exact_mod_cast Nat.cast_div hd.1 hd_pos
    rw [h_cast]
    calc ((n : ℚ) / (d : ℚ)) * (Nat.divisors (n / d)).card = (n : ℚ) * (1 / (d : ℚ)) * (Nat.divisors (n / d)).card := by ring
      _ = (n : ℚ) * ((Nat.divisors (n / d)).card * (1 / (d : ℚ))) := by ring
  rw [h_eq]
  have h_le := sum_tau_n_div_le_tau_mul_sigma hn
  have hn_pos : (0 : ℚ) ≤ n := by positivity
  exact mul_le_mul_of_nonneg_left h_le hn_pos
