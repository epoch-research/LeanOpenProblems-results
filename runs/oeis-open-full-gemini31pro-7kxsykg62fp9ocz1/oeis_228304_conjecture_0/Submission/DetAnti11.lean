import Mathlib

open Nat Finset

lemma choose_two_k_mod_p (p k : ℕ) [hp : Fact p.Prime] (hp_odd : p ≠ 2) (hk : k ≤ (p - 1) / 2) :
    (choose (2 * k) k : ZMod p) = (-4 : ZMod p)^k * (choose ((p - 1) / 2) k : ZMod p) := by
  have h_p_pos : 0 < p := hp.out.pos
  have h_odd : p % 2 = 1 := by
    cases hp.out.eq_two_or_odd with
    | inl h2 => exfalso; exact hp_odd h2
    | inr hodd => exact hodd
  have hm : p = 2 * ((p - 1) / 2) + 1 := by omega
  induction' k with k ih
  · simp
  · have hk_lt : k < (p - 1) / 2 := by omega
    have ih2 := ih (by omega)
    
    have r1 : choose (2 * k + 2) (k + 1) = 2 * choose (2 * k + 1) k := by
      have h_succ : choose (2 * k + 2) (k + 1) = choose (2 * k + 1) k + choose (2 * k + 1) (k + 1) := by
        exact choose_succ_succ (2 * k + 1) k
      have h_symm : choose (2 * k + 1) (k + 1) = choose (2 * k + 1) (2 * k + 1 - (k + 1)) := by
        rw [choose_symm]
        omega
      have h_sub : 2 * k + 1 - (k + 1) = k := by omega
      rw [h_sub] at h_symm
      rw [h_succ, h_symm, ← two_mul]
      
    have r2 : choose (2 * k + 1) k * (k + 1) = choose (2 * k) k * (2 * k + 1) := by
      have := choose_mul_succ_eq (2 * k) k
      have h_sub : 2 * k + 1 - k = k + 1 := by omega
      rw [h_sub] at this
      rw [this]
      
    have r3 : choose (2 * k + 2) (k + 1) * (k + 1) = 2 * (2 * k + 1) * choose (2 * k) k := by
      calc choose (2 * k + 2) (k + 1) * (k + 1) = 2 * choose (2 * k + 1) k * (k + 1) := by rw [r1]
      _ = 2 * (choose (2 * k + 1) k * (k + 1)) := by ring
      _ = 2 * (choose (2 * k) k * (2 * k + 1)) := by rw [r2]
      _ = 2 * (2 * k + 1) * choose (2 * k) k := by ring
    
    have r4 : (choose (2 * k + 2) (k + 1) : ZMod p) * (k + 1 : ZMod p) = (2 * (2 * k + 1) : ZMod p) * (choose (2 * k) k : ZMod p) := by
      have h_cast : ((choose (2 * k + 2) (k + 1) * (k + 1) : ℕ) : ZMod p) = ((2 * (2 * k + 1) * choose (2 * k) k : ℕ) : ZMod p) := by rw [r3]
      push_cast at h_cast
      exact h_cast
      
    have r5 : (choose ((p - 1) / 2) (k + 1) * (k + 1) : ℕ) = choose ((p - 1) / 2) k * ((p - 1) / 2 - k) := by
      have := choose_succ_right_eq ((p - 1) / 2) k
      exact this
      
    have r6 : (choose ((p - 1) / 2) (k + 1) : ZMod p) * (k + 1 : ZMod p) = (choose ((p - 1) / 2) k : ZMod p) * (((p - 1) / 2 - k : ℕ) : ZMod p) := by
      have h_cast : ((choose ((p - 1) / 2) (k + 1) * (k + 1) : ℕ) : ZMod p) = ((choose ((p - 1) / 2) k * ((p - 1) / 2 - k) : ℕ) : ZMod p) := by rw [r5]
      push_cast at h_cast
      exact h_cast
      
    have r7 : 2 * (((p - 1) / 2 - k : ℕ) : ZMod p) = -(2 * (k : ZMod p) + 1) := by
      have H : 2 * ((p - 1) / 2 - k) + 2 * k + 1 = p := by omega
      have H2 : ((2 * ((p - 1) / 2 - k) + 2 * k + 1 : ℕ) : ZMod p) = (p : ZMod p) := by rw [H]
      have hp0 : (p : ZMod p) = 0 := CharP.cast_eq_zero (ZMod p) p
      rw [hp0] at H2
      push_cast at H2
      linear_combination H2
      
    have r8 : (-4 : ZMod p)^(k + 1) * (choose ((p - 1) / 2) (k + 1) : ZMod p) * (k + 1 : ZMod p) = (2 * (2 * k + 1) : ZMod p) * ((-4 : ZMod p)^k * (choose ((p - 1) / 2) k : ZMod p)) := by
      calc (-4 : ZMod p)^(k + 1) * (choose ((p - 1) / 2) (k + 1) : ZMod p) * (k + 1 : ZMod p) 
        _ = (-4 : ZMod p)^(k + 1) * ((choose ((p - 1) / 2) (k + 1) : ZMod p) * (k + 1 : ZMod p)) := by ring
        _ = (-4 : ZMod p)^(k + 1) * ((choose ((p - 1) / 2) k : ZMod p) * (((p - 1) / 2 - k : ℕ) : ZMod p)) := by rw [r6]
        _ = (-4 : ZMod p)^k * (-4 : ZMod p) * (choose ((p - 1) / 2) k : ZMod p) * (((p - 1) / 2 - k : ℕ) : ZMod p) := by rw [pow_add, pow_one]; ring
        _ = (-4 : ZMod p)^k * (-2 : ZMod p) * (2 * (((p - 1) / 2 - k : ℕ) : ZMod p)) * (choose ((p - 1) / 2) k : ZMod p) := by ring
        _ = (-4 : ZMod p)^k * (-2 : ZMod p) * -(2 * (k : ZMod p) + 1) * (choose ((p - 1) / 2) k : ZMod p) := by rw [r7]
        _ = (2 * (2 * (k : ZMod p) + 1)) * ((-4 : ZMod p)^k * (choose ((p - 1) / 2) k : ZMod p)) := by ring
        
    have r9 : (choose (2 * (k + 1)) (k + 1) : ZMod p) * (k + 1 : ZMod p) = (-4 : ZMod p)^(k + 1) * (choose ((p - 1) / 2) (k + 1) : ZMod p) * (k + 1 : ZMod p) := by
      have h_eq_nat : 2 * (k + 1) = 2 * k + 2 := by ring
      calc (choose (2 * (k + 1)) (k + 1) : ZMod p) * (k + 1 : ZMod p) = (choose (2 * k + 2) (k + 1) : ZMod p) * (k + 1 : ZMod p) := by rw [h_eq_nat]
      _ = (2 * (2 * k + 1) : ZMod p) * (choose (2 * k) k : ZMod p) := by rw [r4]
      _ = (2 * (2 * k + 1) : ZMod p) * ((-4 : ZMod p)^k * (choose ((p - 1) / 2) k : ZMod p)) := by rw [ih2]
      _ = (-4 : ZMod p)^(k + 1) * (choose ((p - 1) / 2) (k + 1) : ZMod p) * (k + 1 : ZMod p) := by
        have h_eq_ring : (2 * (2 * k + 1 : ZMod p)) = (2 * (2 * (k : ZMod p) + 1)) := by push_cast; ring
        rw [h_eq_ring, ← r8]
        
    have hk_ne_zero : (k + 1 : ZMod p) ≠ 0 := by
      intro h
      have h2 : ((k + 1 : ℕ) : ZMod p) = 0 := by push_cast; exact h
      have h_dvd : p ∣ k + 1 := (CharP.cast_eq_zero_iff (ZMod p) p _).mp h2
      have h_pos : 0 < k + 1 := by omega
      have : p ≤ k + 1 := Nat.le_of_dvd h_pos h_dvd
      omega
      
    exact mul_right_cancel₀ hk_ne_zero r9
