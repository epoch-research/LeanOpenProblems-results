import Mathlib
import Submission.DetAnti4
import Submission.DetAnti6
import Submission.DetAnti7

open Nat Finset

lemma c_zmod_eq_zero_of_range (p n : ℕ) [hp : Fact p.Prime] (hp_odd : p ≠ 2) (hn1 : p ≤ n) (hn2 : n ≤ 2 * p - 2) :
    (∑ k ∈ range (n + 1), (-1 : ZMod p)^k * (choose n k : ZMod p)^2 * (choose (2 * k) k : ZMod p) * (choose (2 * (n - k)) (n - k) : ZMod p)) = 0 := by
  have h_p_pos : 0 < p := hp.out.pos
  have h_odd : p % 2 = 1 := by
    cases hp.out.eq_two_or_odd with
    | inl h2 => exfalso; exact hp_odd h2
    | inr hodd => exact hodd
  have hp_odd2 : p = 2 * (p / 2) + 1 := by omega
  
  have H_ext : (∑ k ∈ range (n + 1), (-1 : ZMod p)^k * (choose n k : ZMod p)^2 * (choose (2 * k) k : ZMod p) * (choose (2 * (n - k)) (n - k) : ZMod p)) =
               ∑ k ∈ range (2 * p), (-1 : ZMod p)^k * (choose n k : ZMod p)^2 * (choose (2 * k) k : ZMod p) * (choose (2 * (n - k)) (n - k) : ZMod p) := by
    have h_add : 2 * p = (n + 1) + (2 * p - (n + 1)) := by omega
    have H_zero : (∑ j ∈ range (2 * p - (n + 1)), (-1 : ZMod p)^(n + 1 + j) * (choose n (n + 1 + j) : ZMod p)^2 * (choose (2 * (n + 1 + j)) (n + 1 + j) : ZMod p) * (choose (2 * (n - (n + 1 + j))) (n - (n + 1 + j)) : ZMod p)) = 0 := by
      apply sum_eq_zero
      intro x _
      have : choose n (n + 1 + x) = 0 := choose_eq_zero_of_lt (by omega)
      rw [this]
      simp
    calc (∑ k ∈ range (n + 1), (-1 : ZMod p)^k * (choose n k : ZMod p)^2 * (choose (2 * k) k : ZMod p) * (choose (2 * (n - k)) (n - k) : ZMod p))
      _ = _ + 0 := by rw [add_zero]
      _ = _ + ∑ j ∈ range (2 * p - (n + 1)), (-1 : ZMod p)^(n + 1 + j) * (choose n (n + 1 + j) : ZMod p)^2 * (choose (2 * (n + 1 + j)) (n + 1 + j) : ZMod p) * (choose (2 * (n - (n + 1 + j))) (n - (n + 1 + j)) : ZMod p) := by rw [H_zero]
      _ = ∑ k ∈ range ((n + 1) + (2 * p - (n + 1))), (-1 : ZMod p)^k * (choose n k : ZMod p)^2 * (choose (2 * k) k : ZMod p) * (choose (2 * (n - k)) (n - k) : ZMod p) := by rw [← sum_range_add]
      _ = ∑ k ∈ range (2 * p), (-1 : ZMod p)^k * (choose n k : ZMod p)^2 * (choose (2 * k) k : ZMod p) * (choose (2 * (n - k)) (n - k) : ZMod p) := by rw [← h_add]
  rw [H_ext, sum_range_mul_add 2 p]
  
  have H_inner : ∀ j ∈ range p, 
    ((-1 : ZMod p)^(0 * p + j) * (choose n (0 * p + j) : ZMod p)^2 * (choose (2 * (0 * p + j)) (0 * p + j) : ZMod p) * (choose (2 * (n - (0 * p + j))) (n - (0 * p + j)) : ZMod p)) + 
    ((-1 : ZMod p)^(1 * p + j) * (choose n (1 * p + j) : ZMod p)^2 * (choose (2 * (1 * p + j)) (1 * p + j) : ZMod p) * (choose (2 * (n - (1 * p + j))) (n - (1 * p + j)) : ZMod p)) = 0 := by
    intro j hj
    have hj2 : j < p := mem_range.mp hj
    have eq_sign : (-1 : ZMod p)^(1 * p + j) = - (-1 : ZMod p)^(0 * p + j) := by
      have H1 : 1 * p + j = (0 * p + j) + p := by omega
      rw [H1, pow_add]
      have H2 : (-1 : ZMod p)^p = -1 := by
        have H_pow : (-1 : ZMod p)^p = (-1 : ZMod p)^(2 * (p / 2) + 1) := by congr 1
        rw [H_pow, pow_add, pow_mul]
        have h_one : ((-1 : ZMod p)^2) = 1 := by simp
        rw [h_one]
        simp
      rw [H2, mul_neg, mul_one]
    
    have h_mod2 : n % p = n - p := by
      have H : n = p * 1 + (n - p) := by omega
      nth_rewrite 1 [H]
      rw [add_comm (p * 1) (n - p), Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    have h_div2 : n / p = 1 := by
      have H : n = p * 1 + (n - p) := by omega
      nth_rewrite 1 [H]
      rw [add_comm (p * 1) (n - p), Nat.add_mul_div_left (n - p) 1 h_p_pos, Nat.div_eq_of_lt (by omega), zero_add]
      
    by_cases hj_le : j ≤ n - p
    · -- j <= n - p
      have eq_choose0 : (choose n (0 * p + j) : ZMod p) = (choose (n - p) j : ZMod p) := by
        rw [choose_zmod_eq (p := p) (n := n) (k := 0 * p + j)]
        have hm1 : (0 * p + j) % p = j := by
          have H : 0 * p + j = j + p * 0 := by ring
          rw [H, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj2]
        have hd1 : (0 * p + j) / p = 0 := by
          have H : 0 * p + j = j + p * 0 := by ring
          rw [H, Nat.add_mul_div_left j 0 h_p_pos, Nat.div_eq_of_lt hj2, zero_add]
        rw [h_mod2, h_div2, hm1, hd1]
        simp
      have eq_choose1 : (choose n (1 * p + j) : ZMod p) = (choose (n - p) j : ZMod p) := by
        rw [choose_zmod_eq (p := p) (n := n) (k := 1 * p + j)]
        have hm1 : (1 * p + j) % p = j := by
          have H : 1 * p + j = j + p * 1 := by ring
          rw [H, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj2]
        have hd1 : (1 * p + j) / p = 1 := by
          have H : 1 * p + j = j + p * 1 := by ring
          rw [H, Nat.add_mul_div_left j 1 h_p_pos, Nat.div_eq_of_lt hj2, zero_add]
        rw [h_mod2, h_div2, hm1, hd1]
        have : (choose 1 1 : ZMod p) = 1 := by simp
        rw [this, mul_one]
      
      have eq_2k_0 : (choose (2 * (0 * p + j)) (0 * p + j) : ZMod p) = (choose (2 * j) j : ZMod p) := by
        have H : 0 * p + j = j := by ring
        rw [H]
      have eq_2k_1 : (choose (2 * (1 * p + j)) (1 * p + j) : ZMod p) = 2 * (choose (2 * j) j : ZMod p) := by
        have H : 2 * (1 * p + j) = 2 * p + 2 * j := by ring
        have H2 : 1 * p + j = p + j := by ring
        rw [H, H2]
        exact choose_two_p_plus hj2
      
      have eq_2nk_0 : (choose (2 * (n - (0 * p + j))) (n - (0 * p + j)) : ZMod p) = 2 * (choose (2 * (n - p - j)) (n - p - j) : ZMod p) := by
        have H : 0 * p + j = j := by ring
        rw [H]
        have H2 : 2 * (n - j) = 2 * p + 2 * (n - p - j) := by omega
        have H3 : n - j = p + (n - p - j) := by omega
        rw [H2, H3]
        have h_lt : n - p - j < p := by omega
        exact choose_two_p_plus h_lt
      
      have eq_2nk_1 : (choose (2 * (n - (1 * p + j))) (n - (1 * p + j)) : ZMod p) = (choose (2 * (n - p - j)) (n - p - j) : ZMod p) := by
        have H : n - (1 * p + j) = n - p - j := by omega
        rw [H]
      
      rw [eq_sign, eq_choose0, eq_choose1, eq_2k_0, eq_2k_1, eq_2nk_0, eq_2nk_1]
      ring
      
    · -- j > n - p
      have h_lt : n - p < j := by omega
      have h_zero : choose (n - p) j = 0 := choose_eq_zero_of_lt h_lt
      have eq1 : (choose n (0 * p + j) : ZMod p) = 0 := by
        rw [choose_zmod_eq (p := p) (n := n) (k := 0 * p + j)]
        have hm1 : (0 * p + j) % p = j := by
          have H : 0 * p + j = j + p * 0 := by ring
          rw [H, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj2]
        rw [h_mod2, hm1, h_zero]
        simp
      have eq2 : (choose n (1 * p + j) : ZMod p) = 0 := by
        rw [choose_zmod_eq (p := p) (n := n) (k := 1 * p + j)]
        have hm1 : (1 * p + j) % p = j := by
          have H : 1 * p + j = j + p * 1 := by ring
          rw [H, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj2]
        rw [h_mod2, hm1, h_zero]
        simp
      rw [eq1, eq2]
      simp

  rw [sum_range_succ, sum_range_one, ← sum_add_distrib]
  apply sum_eq_zero
  intro x hx
  exact H_inner x hx
