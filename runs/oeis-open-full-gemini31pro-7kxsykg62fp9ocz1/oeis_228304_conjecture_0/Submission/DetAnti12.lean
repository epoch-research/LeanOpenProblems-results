import Mathlib
import Mathlib.Data.Nat.Choose.Lucas
import Submission.DetAnti9
import Submission.DetAnti11
import Submission.Defs

open Nat Finset

lemma choose_zmod_eq {p n k : ℕ} [hp : Fact p.Prime] :
    (choose n k : ZMod p) = (choose (n % p) (k % p) : ZMod p) * (choose (n / p) (k / p) : ZMod p) := by
  have H := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := p) (n := n) (k := k)
  have H2 : (choose n k : ZMod p) = ((choose (n % p) (k % p) * choose (n / p) (k / p) : ℕ) : ZMod p) := by
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr H
  rw [H2]
  push_cast
  rfl

lemma c_p_minus_1_mod_p (p : ℕ) [hp : Fact p.Prime] (hp_odd : p ≠ 2) :
    (_root_.c_val (p - 1) : ZMod p) = (-1 : ZMod p)^((p - 1) / 2) := by
  have h_p_pos : 0 < p := hp.out.pos
  have H1 : (_root_.c_val (p - 1) : ZMod p) = ∑ k ∈ range p, (-1 : ZMod p)^k * (choose (p - 1) k : ZMod p)^2 * (choose (2 * k) k : ZMod p) * (choose (2 * (p - 1 - k)) (p - 1 - k) : ZMod p) := by
    dsimp [_root_.c_val]
    have : p - 1 + 1 = p := by omega
    have h_range : range (p - 1 + 1) = range p := by rw [this]
    rw [h_range]
    push_cast
    rfl
  rw [H1]
  
  have H2 : ∑ k ∈ range p, (-1 : ZMod p)^k * (choose (p - 1) k : ZMod p)^2 * (choose (2 * k) k : ZMod p) * (choose (2 * (p - 1 - k)) (p - 1 - k) : ZMod p) = 
            ∑ k ∈ range p, (-1 : ZMod p)^k * (choose (2 * k) k : ZMod p) * (choose (2 * (p - 1 - k)) (p - 1 - k) : ZMod p) := by
    apply sum_congr rfl
    intro k hk
    have hk_lt : k < p := mem_range.mp hk
    have H_choose : (choose (p - 1) k : ZMod p) = (-1 : ZMod p)^k := choose_p_minus_one_mod_p p k hk_lt
    rw [H_choose]
    have H_sq : ((-1 : ZMod p)^k)^2 = 1 := by
      rw [← pow_mul]
      have : k * 2 = 2 * k := by ring
      rw [this, pow_mul]
      have : (-1 : ZMod p)^2 = 1 := by simp
      rw [this, one_pow]
    rw [H_sq, mul_one]
  rw [H2]
  
  have h_odd : p % 2 = 1 := by
    cases hp.out.eq_two_or_odd with
    | inl h2 => exfalso; exact hp_odd h2
    | inr hodd => exact hodd
  set m := (p - 1) / 2
  have h_p : p = 2 * m + 1 := by omega
  
  have h_four_m : (-4 : ZMod p)^m = (-1 : ZMod p)^m := by
    calc (-4 : ZMod p)^m = ((-1 : ZMod p) * 4)^m := by ring
    _ = (-1 : ZMod p)^m * (4 : ZMod p)^m := by rw [mul_pow]
    _ = (-1 : ZMod p)^m * ((2 : ZMod p)^2)^m := by 
      have : (4 : ZMod p) = (2 : ZMod p)^2 := by ring
      rw [this]
    _ = (-1 : ZMod p)^m * (2 : ZMod p)^(2 * m) := by rw [← pow_mul]
    _ = (-1 : ZMod p)^m * 1 := by
      have h2m : 2 * m = p - 1 := by omega
      have Hpow : (2 : ZMod p)^(2 * m) = (2 : ZMod p)^(p - 1) := by rw [h2m]
      rw [Hpow]
      have hd : (2 : ZMod p) ≠ 0 := by
        intro h2
        have h_dvd : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h2
        have h_pos2 : 0 < 2 := by decide
        have h_le : p ≤ 2 := Nat.le_of_dvd h_pos2 h_dvd
        have h_ge : 2 ≤ p := hp.out.two_le
        have h_eq : p = 2 := by omega
        exact hp_odd h_eq
      have h_one : (2 : ZMod p)^(p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hd
      rw [h_one]
    _ = (-1 : ZMod p)^m := by ring
    
  have H3 : ∀ k ∈ range p, (-1 : ZMod p)^k * (choose (2 * k) k : ZMod p) * (choose (2 * (p - 1 - k)) (p - 1 - k) : ZMod p) = 
            (if k = m then (-1 : ZMod p)^m else 0) := by
    intro k hk
    have hk_lt : k < p := mem_range.mp hk
    by_cases hkm : k = m
    · rw [if_pos hkm, hkm]
      have h_m_lt : m < p := by omega
      have h_m_le : m ≤ m := by omega
      have eq1 : p - 1 - m = m := by omega
      have eq2 : (choose (2 * m) m : ZMod p) = (-4 : ZMod p)^m * (choose m m : ZMod p) := choose_two_k_mod_p p m hp_odd h_m_le
      have eq3 : choose m m = 1 := choose_self m
      rw [eq3] at eq2
      push_cast at eq2
      rw [mul_one] at eq2
      have eq4 : (choose (2 * (p - 1 - m)) (p - 1 - m) : ZMod p) = (-4 : ZMod p)^m * 1 := by
        rw [eq1]
        rw [eq2]
        ring
      rw [eq4, eq2]
      calc (-1 : ZMod p)^m * (-4 : ZMod p)^m * ((-4 : ZMod p)^m * 1) = (-1 : ZMod p)^m * ((-4 : ZMod p)^m * (-4 : ZMod p)^m) := by ring
      _ = (-1 : ZMod p)^m * ((-1 : ZMod p)^m * (-1 : ZMod p)^m) := by rw [h_four_m]
      _ = (-1 : ZMod p)^m * ((-1 : ZMod p)^(m + m)) := by rw [← pow_add]
      _ = (-1 : ZMod p)^m * ((-1 : ZMod p)^(2 * m)) := by
        have : m + m = 2 * m := by omega
        rw [this]
      _ = (-1 : ZMod p)^m * 1 := by
        have h2m : 2 * m = p - 1 := by omega
        have H1 : (-1 : ZMod p)^(2 * m) = ((-1 : ZMod p)^2)^m := by rw [pow_mul]
        rw [H1]
        have H2 : ((-1 : ZMod p)^2) = 1 := by simp
        rw [H2, one_pow]
      _ = (-1 : ZMod p)^m := by ring
    · rw [if_neg hkm]
      have h_k : k < m ∨ k > m := by omega
      rcases h_k with hlt | hgt
      · -- k < m => p - 1 - k > m => choose m (p - 1 - k) = 0
        have hp1 : p - 1 - k = 2 * m - k := by omega
        have hp2 : 2 * m - k > m := by omega
        have h_zero : choose m (2 * m - k) = 0 := choose_eq_zero_of_lt hp2
        have h_lt2 : p - 2 - 2 * k < p - 1 - k := by omega
        have h_zero2 : choose (p - 2 - 2 * k) (p - 1 - k) = 0 := choose_eq_zero_of_lt h_lt2
        have eq_choose : (choose (2 * (p - 1 - k)) (p - 1 - k) : ZMod p) = 0 := by
          rw [choose_zmod_eq (p := p) (n := 2 * (p - 1 - k)) (k := p - 1 - k)]
          have h_mod1 : (2 * (p - 1 - k)) % p = p - 2 - 2 * k := by
            have H : 2 * (p - 1 - k) = (p - 2 - 2 * k) + p * 1 := by omega
            nth_rewrite 1 [H]
            rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
          have h_mod2 : (p - 1 - k) % p = p - 1 - k := Nat.mod_eq_of_lt (by omega)
          rw [h_mod1, h_mod2, h_zero2]
          simp
        rw [eq_choose, mul_zero]
      · -- k > m => choose m k = 0
        have h_zero : choose m k = 0 := choose_eq_zero_of_lt hgt
        have h_lt2 : 2 * k - p < k := by omega
        have h_zero2 : choose (2 * k - p) k = 0 := choose_eq_zero_of_lt h_lt2
        have eq_choose : (choose (2 * k) k : ZMod p) = 0 := by
          rw [choose_zmod_eq (p := p) (n := 2 * k) (k := k)]
          have h_mod1 : (2 * k) % p = 2 * k - p := by
            have H : 2 * k = (2 * k - p) + p * 1 := by omega
            nth_rewrite 1 [H]
            rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
          have h_mod2 : k % p = k := Nat.mod_eq_of_lt hk_lt
          rw [h_mod1, h_mod2, h_zero2]
          simp
        rw [eq_choose]
        ring
  rw [sum_congr rfl H3]
  rw [sum_ite]
  have h_filter : (range p).filter (fun k => k = m) = {m} := by
    ext x
    simp only [mem_filter, mem_range, mem_singleton]
    constructor
    · rintro ⟨_, h2⟩; exact h2
    · rintro rfl
      exact ⟨by omega, rfl⟩
  rw [h_filter, sum_singleton, sum_const_zero, add_zero]
