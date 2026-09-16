import Mathlib
import Submission.DetAnti4
import Submission.DetAnti6

open Nat Finset

lemma choose_two_p_plus {p x : ℕ} [hp : Fact p.Prime] (hx : x < p) :
    (choose (2 * p + 2 * x) (p + x) : ZMod p) = 2 * (choose (2 * x) x : ZMod p) := by
  have h_p_pos : 0 < p := hp.out.pos
  by_cases h2x : 2 * x < p
  · have h_mod1 : (2 * p + 2 * x) % p = 2 * x := by
      have H : 2 * p + 2 * x = 2 * x + p * 2 := by ring
      rw [H, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h2x]
    have h_mod2 : (p + x) % p = x := by
      have H : p + x = x + p * 1 := by ring
      rw [H, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]
    have h_div1 : (2 * p + 2 * x) / p = 2 := by
      have H : 2 * p + 2 * x = 2 * x + p * 2 := by ring
      rw [H, Nat.add_mul_div_left (2 * x) 2 h_p_pos, Nat.div_eq_of_lt h2x, zero_add]
    have h_div2 : (p + x) / p = 1 := by
      have H : p + x = x + p * 1 := by ring
      rw [H, Nat.add_mul_div_left x 1 h_p_pos, Nat.div_eq_of_lt hx, zero_add]
    rw [choose_zmod_eq (p := p) (n := 2 * p + 2 * x) (k := p + x)]
    rw [h_mod1, h_mod2, h_div1, h_div2]
    have : (choose 2 1 : ZMod p) = 2 := by rfl
    rw [this, mul_comm]
  · have h_mod1 : (2 * p + 2 * x) % p = 2 * x - p := by
      have H : 2 * p + 2 * x = (2 * x - p) + p * 3 := by omega
      nth_rewrite 1 [H]
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    have h_mod2 : (p + x) % p = x := by
      have H : p + x = x + p * 1 := by ring
      rw [H, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]
    have h_zero : choose (2 * x - p) x = 0 := by
      apply choose_eq_zero_of_lt
      omega
    rw [choose_zmod_eq (p := p) (n := 2 * p + 2 * x) (k := p + x)]
    have h_zero2 : (choose (2 * x) x : ZMod p) = 0 := by
      rw [choose_zmod_eq (p := p) (n := 2 * x) (k := x)]
      have hm1 : (2 * x) % p = 2 * x - p := by
        have H : 2 * x = (2 * x - p) + p * 1 := by omega
        nth_rewrite 1 [H]
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
      have hm2 : x % p = x := Nat.mod_eq_of_lt hx
      rw [hm1, hm2, h_zero]
      simp
    rw [h_mod1, h_mod2, h_zero, h_zero2]
    simp
