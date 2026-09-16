import Mathlib
import Submission.DetAnti4

open Nat Finset

lemma sum_range_mul_add {R : Type*} [AddCommMonoid R] (n m : ℕ) (f : ℕ → R) :
    ∑ k ∈ range (n * m), f k = ∑ i ∈ range n, ∑ j ∈ range m, f (i * m + j) := by
  induction' n with n ih
  · simp
  · rw [succ_mul, sum_range_add, ih, sum_range_succ]

lemma a_zmod_eq_zero_of_range (p n : ℕ) [hp : Fact p.Prime] (hp_odd : p ≠ 2) (hn1 : p ≤ n) (hn2 : n ≤ 2 * p - 2) :
    (∑ k ∈ range (n + 1), (-1 : ZMod p)^k * (choose n k : ZMod p)^4) = 0 := by
  have h_p_pos : 0 < p := hp.out.pos
  have h_odd : p % 2 = 1 := by
    cases hp.out.eq_two_or_odd with
    | inl h2 => exfalso; exact hp_odd h2
    | inr hodd => exact hodd
  
  have H_ext : (∑ k ∈ range (n + 1), (-1 : ZMod p)^k * (choose n k : ZMod p)^4) =
               ∑ k ∈ range (2 * p), (-1 : ZMod p)^k * (choose n k : ZMod p)^4 := by
    have h_add : 2 * p = (n + 1) + (2 * p - (n + 1)) := by omega
    have H_zero : (∑ j ∈ range (2 * p - (n + 1)), (-1 : ZMod p)^(n + 1 + j) * (choose n (n + 1 + j) : ZMod p)^4) = 0 := by
      apply sum_eq_zero
      intro x _
      have : choose n (n + 1 + x) = 0 := choose_eq_zero_of_lt (by omega)
      rw [this]
      simp
    calc (∑ k ∈ range (n + 1), (-1 : ZMod p)^k * (choose n k : ZMod p)^4)
      _ = (∑ k ∈ range (n + 1), (-1 : ZMod p)^k * (choose n k : ZMod p)^4) + 0 := by rw [add_zero]
      _ = (∑ k ∈ range (n + 1), (-1 : ZMod p)^k * (choose n k : ZMod p)^4) + ∑ j ∈ range (2 * p - (n + 1)), (-1 : ZMod p)^(n + 1 + j) * (choose n (n + 1 + j) : ZMod p)^4 := by rw [H_zero]
      _ = ∑ k ∈ range ((n + 1) + (2 * p - (n + 1))), (-1 : ZMod p)^k * (choose n k : ZMod p)^4 := by rw [← sum_range_add]
      _ = ∑ k ∈ range (2 * p), (-1 : ZMod p)^k * (choose n k : ZMod p)^4 := by rw [← h_add]

  rw [H_ext, sum_range_mul_add 2 p]
  have H_inner : ∀ i ∈ range 2, ∀ j ∈ range p, 
      (-1 : ZMod p)^(i * p + j) * (choose n (i * p + j) : ZMod p)^4 =
      (-1 : ZMod p)^(i + j) * (choose (n - p) j : ZMod p)^4 := by
    intro i hi j hj
    have hi2 : i < 2 := mem_range.mp hi
    have hj2 : j < p := mem_range.mp hj
    have eq1 : ((-1 : ZMod p)^(i * p + j)) = (-1 : ZMod p)^(i + j) := by
      have hp_odd2 : p = 2 * (p / 2) + 1 := by omega
      have eq_pow : i * p + j = 2 * (i * (p / 2)) + (i + j) := by
        have H1 : i * p + j = i * (2 * (p / 2) + 1) + j := by
          congr 1
          congr 1
        rw [H1]
        ring
      rw [eq_pow, pow_add, pow_mul]
      have h_one : ((-1 : ZMod p)^2) = 1 := by simp
      rw [h_one, one_pow, one_mul]
    rw [eq1]
    have h_mod1 : (i * p + j) % p = j := by
      rw [mul_comm i p, add_comm (p * i) j, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj2]
    have h_div1 : (i * p + j) / p = i := by
      rw [mul_comm i p, add_comm (p * i) j, Nat.add_mul_div_left j i h_p_pos, Nat.div_eq_of_lt hj2, zero_add]
    have h_mod2 : n % p = n - p := by
      have H : n = p * 1 + (n - p) := by omega
      nth_rewrite 1 [H]
      rw [add_comm (p * 1) (n - p), Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    have h_div2 : n / p = 1 := by
      have H : n = p * 1 + (n - p) := by omega
      nth_rewrite 1 [H]
      rw [add_comm (p * 1) (n - p), Nat.add_mul_div_left (n - p) 1 h_p_pos, Nat.div_eq_of_lt (by omega), zero_add]
    have eq2 : (choose n (i * p + j) : ZMod p) = (choose (n - p) j : ZMod p) * (choose 1 i : ZMod p) := by
      rw [choose_zmod_eq (p := p) (n := n) (k := i * p + j), h_mod1, h_div1, h_mod2, h_div2]
    have eq3 : (choose 1 i : ZMod p) = 1 := by
      have h_i : i = 0 ∨ i = 1 := by omega
      rcases h_i with rfl | rfl
      · simp
      · simp
    rw [eq2, eq3, mul_one]
  
  have H_sum2 : (∑ i ∈ range 2, ∑ j ∈ range p, (-1 : ZMod p)^(i * p + j) * (choose n (i * p + j) : ZMod p)^4) =
                ∑ i ∈ range 2, ∑ j ∈ range p, (-1 : ZMod p)^(i + j) * (choose (n - p) j : ZMod p)^4 := by
    apply sum_congr rfl
    intro i hi
    apply sum_congr rfl
    intro j hj
    exact H_inner i hi j hj
  rw [H_sum2]
  rw [sum_range_succ, sum_range_one]
  have H_sum_1 : (∑ j ∈ range p, (-1 : ZMod p)^(1 + j) * (choose (n - p) j : ZMod p)^4) =
                 - (∑ j ∈ range p, (-1 : ZMod p)^(0 + j) * (choose (n - p) j : ZMod p)^4) := by
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro j _
    have eq_sign : (-1 : ZMod p)^(1 + j) = - (-1 : ZMod p)^(0 + j) := by
      rw [pow_add, pow_one, zero_add]
      ring
    rw [eq_sign]
    ring
  rw [H_sum_1]
  ring
