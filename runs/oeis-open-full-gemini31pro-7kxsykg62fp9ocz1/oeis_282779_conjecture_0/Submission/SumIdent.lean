import Mathlib

open Nat Finset

lemma sum_ident (p T : ℕ) (hp : p ≥ 2) :
  ∑ x ∈ range p, T ^ x * (p.choose x) = 1 + T * p + ∑ i ∈ range (p - 2), T ^ (i + 2) * p.choose (i + 2) := by
  have hp_eq : p = p - 1 + 1 := by omega
  nth_rw 1 [hp_eq]
  rw [sum_range_succ']
  have hp_eq2 : p - 1 = p - 2 + 1 := by omega
  nth_rw 1 [hp_eq2]
  rw [sum_range_succ']
  have h_zero : 0 + 1 = 1 := rfl
  rw [h_zero]
  simp only [pow_zero, choose_zero_right, mul_one, pow_one, choose_one_right]
  have h_sum : (∑ a ∈ range (p - 2), T ^ (a + 1 + 1) * p.choose (a + 1 + 1)) = ∑ i ∈ range (p - 2), T ^ (i + 2) * p.choose (i + 2) := by
    apply sum_congr rfl
    intro x _
    congr 2
  rw [h_sum]
  omega

lemma add_pow_ident (p T : ℕ) (hp : p.Prime) :
  ∃ K, (1 + T)^p = 1 + p * T * (1 + T * K) + T^p := by
  have hp2 : p ≥ 2 := hp.two_le
  have h := add_pow T 1 p
  simp only [one_pow, mul_one, Nat.cast_id] at h
  rw [add_comm 1 T, h, sum_range_succ]
  have h_choose : p.choose p = 1 := choose_self p
  simp only [h_choose, mul_one]
  rw [sum_ident p T hp2]
  have h_pull : (∑ i ∈ range (p - 2), T ^ (i + 2) * p.choose (i + 2)) = T^2 * ∑ i ∈ range (p - 2), T ^ i * p.choose (i + 2) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro x _
    rw [pow_add]
    ring
  rw [h_pull]
  have hdvd : p ∣ ∑ i ∈ range (p - 2), T ^ i * p.choose (i + 2) := by
    apply dvd_sum
    intro i hi
    have hi_lt : i + 2 < p := by
      rw [mem_range] at hi
      omega
    have hdvd_choose : p ∣ p.choose (i + 2) := Nat.Prime.dvd_choose hp (by omega) (by omega) (by rfl)
    exact dvd_mul_of_dvd_right hdvd_choose _
  rcases hdvd with ⟨K, hK⟩
  use K
  rw [hK]
  ring
