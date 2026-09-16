import Mathlib

open Nat Finset

lemma dvd_term (p c k i : ℕ) (hi : i < p) :
  p^2 * c ∣ k^i * (p * c)^(p - i) * p.choose i := by
  by_cases h : i = p - 1
  · subst h
    have hp_sub : p - (p - 1) = 1 := by omega
    rw [hp_sub, pow_one]
    have h_choose : p.choose (p - 1) = p := by
      have : p - 1 = p - 1 := rfl
      rw [← choose_symm (by omega)]
      have : p - (p - 1) = 1 := by omega
      rw [this]
      exact choose_one_right p
    rw [h_choose]
    have : k ^ (p - 1) * (p * c) * p = (p ^ 2 * c) * k ^ (p - 1) := by
      have hsq : p ^ 2 = p * p := by ring
      rw [hsq]
      ring
    rw [this]
    exact dvd_mul_right (p ^ 2 * c) (k ^ (p - 1))
  · have h_split : p - i = 2 + (p - i - 2) := by omega
    rw [h_split, pow_add, mul_pow]
    have : k ^ i * (p ^ 2 * c ^ 2 * (p * c) ^ (p - i - 2)) * p.choose i =
      (p ^ 2 * c) * (c * (p * c) ^ (p - i - 2) * k ^ i * p.choose i) := by ring
    rw [this]
    exact dvd_mul_right _ _

lemma valid_period_pc (p c k : ℕ) :
  (k + p * c)^p % (p^2 * c) = k^p % (p^2 * c) := by
  have h := add_pow k (p * c) p
  simp only [Nat.cast_id] at h
  rw [sum_range_succ] at h
  have hp_sub : p - p = 0 := by omega
  rw [hp_sub, pow_zero, mul_one, choose_self p, mul_one] at h
  have hdvd : p^2 * c ∣ ∑ i ∈ range p, k^i * (p * c)^(p - i) * p.choose i := by
    apply dvd_sum
    intro i hi
    rw [mem_range] at hi
    exact dvd_term p c k i hi
  rcases hdvd with ⟨K, hK⟩
  rw [hK] at h
  have : (k + p * c)^p = p^2 * c * K + k^p := by
    rw [h, add_comm]
  rw [this, add_comm]
  exact Nat.add_mul_mod_self_left (k^p) (p^2 * c) K
