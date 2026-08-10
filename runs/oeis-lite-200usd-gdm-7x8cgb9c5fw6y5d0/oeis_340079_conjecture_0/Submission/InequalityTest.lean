import Mathlib

lemma test (p q r : ℕ) (hp : p ≥ 3) (hq : q ≥ 7) (hr : r ≥ 11) :
    4 * p * q * r < (2 * p - 1) * (2 * q - 1) * (2 * r - 1) + 1 := by
  have hp' : 3 ≤ (p : ℤ) := by exact_mod_cast hp
  have hq' : 7 ≤ (q : ℤ) := by exact_mod_cast hq
  have hr' : 11 ≤ (r : ℤ) := by exact_mod_cast hr
  have h_ge1 : 2 * p ≥ 1 := by omega
  have h_ge2 : 2 * q ≥ 1 := by omega
  have h_ge3 : 2 * r ≥ 1 := by omega
  -- Move everything to Z
  zify [h_ge1, h_ge2, h_ge3]
  let p_z := (p : ℤ)
  let q_z := (q : ℤ)
  let r_z := (r : ℤ)
  have h_eq : (2 * p_z - 1) * (2 * q_z - 1) * (2 * r_z - 1) + 1 - 4 * p_z * q_z * r_z =
               4 * (p_z - 3) * (q_z - 7) * (r_z - 11) + 40 * (p_z - 3) * (q_z - 7) + 24 * (p_z - 3) * (r_z - 11) + 8 * (q_z - 7) * (r_z - 11) + 238 * (p_z - 3) + 78 * (q_z - 7) + 46 * (r_z - 11) + 442 := by ring
  have u1 : p_z - 3 ≥ 0 := by omega
  have u2 : q_z - 7 ≥ 0 := by omega
  have u3 : r_z - 11 ≥ 0 := by omega
  have h_pos : 4 * (p_z - 3) * (q_z - 7) * (r_z - 11) + 40 * (p_z - 3) * (q_z - 7) + 24 * (p_z - 3) * (r_z - 11) + 8 * (q_z - 7) * (r_z - 11) + 238 * (p_z - 3) + 78 * (q_z - 7) + 46 * (r_z - 11) + 442 > 0 := by
    have t1 : (p_z - 3) * (q_z - 7) ≥ 0 := mul_nonneg u1 u2
    have t2 : (p_z - 3) * (q_z - 7) * (r_z - 11) ≥ 0 := mul_nonneg t1 u3
    have t3 : (p_z - 3) * (r_z - 11) ≥ 0 := mul_nonneg u1 u3
    have t4 : (q_z - 7) * (r_z - 11) ≥ 0 := mul_nonneg u2 u3
    linarith
  linarith

lemma test2 (p q r : ℕ) (hp : p ≥ 3) (hq : q ≥ 11) (hr : r ≥ 13) :
    6 * p * q * r < (2 * p - 1) * (2 * q - 1) * (2 * r - 1) + 1 := by
  have hp' : 3 ≤ (p : ℤ) := by exact_mod_cast hp
  have hq' : 11 ≤ (q : ℤ) := by exact_mod_cast hq
  have hr' : 13 ≤ (r : ℤ) := by exact_mod_cast hr
  have h_ge1 : 2 * p ≥ 1 := by omega
  have h_ge2 : 2 * q ≥ 1 := by omega
  have h_ge3 : 2 * r ≥ 1 := by omega
  -- Move everything to Z
  zify [h_ge1, h_ge2, h_ge3]
  let p_z := (p : ℤ)
  let q_z := (q : ℤ)
  let r_z := (r : ℤ)
  have h_eq : (2 * p_z - 1) * (2 * q_z - 1) * (2 * r_z - 1) + 1 - 6 * p_z * q_z * r_z =
               2 * (p_z - 3) * (q_z - 11) * (r_z - 13) + 22 * (p_z - 3) * (q_z - 11) + 18 * (p_z - 3) * (r_z - 13) + 2 * (q_z - 11) * (r_z - 13) + 192 * (p_z - 3) + 16 * (q_z - 11) + 12 * (r_z - 13) + 52 := by ring
  have u1 : p_z - 3 ≥ 0 := by omega
  have u2 : q_z - 11 ≥ 0 := by omega
  have u3 : r_z - 13 ≥ 0 := by omega
  have h_pos : 2 * (p_z - 3) * (q_z - 11) * (r_z - 13) + 22 * (p_z - 3) * (q_z - 11) + 18 * (p_z - 3) * (r_z - 13) + 2 * (q_z - 11) * (r_z - 13) + 192 * (p_z - 3) + 16 * (q_z - 11) + 12 * (r_z - 13) + 52 > 0 := by
    have t1 : (p_z - 3) * (q_z - 11) ≥ 0 := mul_nonneg u1 u2
    have t2 : (p_z - 3) * (q_z - 11) * (r_z - 13) ≥ 0 := mul_nonneg t1 u3
    have t3 : (p_z - 3) * (r_z - 13) ≥ 0 := mul_nonneg u1 u3
    have t4 : (q_z - 11) * (r_z - 13) ≥ 0 := mul_nonneg u2 u3
    linarith
  linarith





