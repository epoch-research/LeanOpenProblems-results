import Submission.Spec
import Mathlib

open Nat Finset

lemma sum_inv_eq {n : ℕ} (hn : 0 < n) :
  (∑ d ∈ n.divisors, (d : ℚ)) / (n : ℚ) = ∑ d ∈ n.divisors, 1 / (d : ℚ) := by
  have h_eq : (∑ d ∈ n.divisors, (d : ℚ)) / (n : ℚ) = ∑ d ∈ n.divisors, ((d : ℚ) / (n : ℚ)) := by
    rw [sum_div]
  rw [h_eq]
  have h_reindex : ∑ d ∈ n.divisors, ((d : ℚ) / (n : ℚ)) = ∑ d ∈ n.divisors, (((n / d : ℕ) : ℚ) / (n : ℚ)) := by
    have := Nat.sum_div_divisors n (fun d => ((d : ℕ) : ℚ) / (n : ℚ))
    exact this.symm
  rw [h_reindex]
  apply sum_congr rfl
  intro d hd
  rw [mem_divisors] at hd
  have hd_pos : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; exact hn.ne.symm (eq_zero_of_zero_dvd hd.1))
  have hd_ne_zero : (d : ℚ) ≠ 0 := by exact_mod_cast hd_pos.ne.symm
  have h_cast : ((n / d : ℕ) : ℚ) = (n : ℚ) / (d : ℚ) := by
    exact_mod_cast Nat.cast_div hd.1 hd_ne_zero
  rw [h_cast]
  have hn_pos : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne.symm
  calc ((n : ℚ) / (d : ℚ)) / (n : ℚ) = ((n : ℚ) / (n : ℚ)) / (d : ℚ) := by ring
    _ = 1 / (d : ℚ) := by rw [div_self hn_pos]
