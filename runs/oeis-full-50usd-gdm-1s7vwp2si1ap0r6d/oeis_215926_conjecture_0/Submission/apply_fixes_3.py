import os

with open('/workspace/leanproject/Submission/Spec.lean', 'r') as f:
    content = f.read()

# 1. Define test_contra_nat as a helper theorem before h_sum_ne2
test_contra_nat_def = """theorem test_contra_nat (d X m S : ℕ) (hd : d ≥ 3) (hX : X ≥ 3) (hm : m = d * X) (hS_ge : 1 + d + X + m ≤ S) (hS_eq : S = 2 * m - 1) : False := by
  have h_eq : d * X = (d - 1) * (X - 1) + (d - 1) + (X - 1) + 1 := by
    have hd_eq : d = (d - 1) + 1 := (Nat.sub_add_cancel (by omega)).symm
    have hX_eq : X = (X - 1) + 1 := (Nat.sub_add_cancel (by omega)).symm
    nth_rw 1 [hd_eq]
    nth_rw 1 [hX_eq]
    ring
  have h_le : (d - 1) * (X - 1) ≥ 4 := by
    have h1 : d - 1 ≥ 2 := by omega
    have h2 : X - 1 ≥ 2 := by omega
    exact Nat.mul_le_mul h1 h2
  rw [h_eq] at hm
  have hd_eq : d = (d - 1) + 1 := (Nat.sub_add_cancel (by omega)).symm
  have hX_eq : X = (X - 1) + 1 := (Nat.sub_add_cancel (by omega)).symm
  rw [hd_eq, hX_eq] at hS_ge
  clear h_eq hd_eq hX_eq
  omega

"""

# Insert test_contra_nat_def right before theorem h_sum_ne2
h_sum_ne2_pos = content.find("theorem h_sum_ne2")
content = content[:h_sum_ne2_pos] + test_contra_nat_def + content[h_sum_ne2_pos:]

# 2. Simplify h_sum_ne2 ending using test_contra_nat
h_sum_ne2_old_end = """      have h_sum_ge : 1 + d + m/d + m ≤ m.divisors.sum id := by
        have h_sum_four : ({1, d, m/d, m} : Finset ℕ).sum id = 1 + d + m/d + m := by
          rw [sum_insert (by simp [h1d, h1md, h1m]), sum_insert (by simp [hd_eq, hdm]), sum_insert (by simp [hmdm]), sum_singleton, id_eq, id_eq, id_eq, id_eq]
          omega
        rw [← h_sum_four]
        exact sum_le_sum_of_subset h_sub
      have h_eq : d * (m/d) = (d - 1) * (m/d - 1) + (d - 1) + (m/d - 1) + 1 := by
        have hd_eq : d = (d - 1) + 1 := (Nat.sub_add_cancel (by omega)).symm
        have hX_eq : m/d = (m/d - 1) + 1 := (Nat.sub_add_cancel (by omega)).symm
        nth_rw 1 [hd_eq]
        nth_rw 1 [hX_eq]
        ring
      have h_le : (d - 1) * (m/d - 1) ≥ 4 := by
        have h1 : d - 1 ≥ 2 := by omega
        have h2 : m/d - 1 ≥ 2 := by omega
        exact Nat.mul_le_mul h1 h2
      have hd_eq' : d = (d - 1) + 1 := (Nat.sub_add_cancel (by omega)).symm
      have hX_eq' : m/d = (m/d - 1) + 1 := (Nat.sub_add_cancel (by omega)).symm
      have hm_eq : m = (d - 1) * (m/d - 1) + (d - 1) + (m/d - 1) + 1 := by
        have : m = d * (m/d) := by
          rw [mul_comm]
          exact (Nat.div_mul_cancel hd).symm
        rw [this, h_eq]
      rw [hX_eq', hd_eq'] at h_sum_ge
      omega"""

h_sum_ne2_new_end = """      have h_sum_ge : 1 + d + m/d + m ≤ m.divisors.sum id := by
        have h_sum_four : ({1, d, m/d, m} : Finset ℕ).sum id = 1 + d + m/d + m := by
          rw [sum_insert (by simp [h1d, h1md, h1m]), sum_insert (by simp [hd_eq, hdm]), sum_insert (by simp [hmdm]), sum_singleton, id_eq, id_eq, id_eq, id_eq]
          omega
        rw [← h_sum_four]
        exact sum_le_sum_of_subset h_sub
      have h_m_eq : m = d * (m/d) := by
        rw [mul_comm]
        exact (Nat.div_mul_cancel hd).symm
      exact test_contra_nat d (m/d) m (m.divisors.sum id) hd_ge3 hd_div_ge3 h_m_eq h_sum_ge h_sum"""

content = content.replace(h_sum_ne2_old_end, h_sum_ne2_new_end)

# 3. Fix h_bound1 in D_ne_one to avoid omega/nlinarith failure on exponentials
content = content.replace(
    """    have h_bound1 : m ≥ 6 * k + 1 := by
      have : 2^(a+1) - 1 ≥ 3 := by omega
      nlinarith""",
    """    have h_bound1 : m ≥ 6 * k + 1 := by
      have h_pow_ge : 2^(a+1) ≥ 4 := by
        have : a + 1 ≥ 2 := by omega
        exact Nat.pow_le_pow_right (by decide) this
      have h_mul_le : (2^(a+1) - 1) * (2 * k) ≥ 3 * (2 * k) := by
        apply Nat.mul_le_mul_right (2 * k)
        omega
      omega"""
)

# 4. Fix clear list in hp_ge5
content = content.replace(
    """      have hp_ge5 : p ≥ 5 := by
        clear D h_D_ge_one h_D h_D_calc h_trans_final h_final_bound h_final_bound2 L h_L_eq h_D_eq
        omega""",
    """      have hp_ge5 : p ≥ 5 := by
        clear D h_D_ge_one h_D h_D_calc h_trans_final h_final_bound h_final_bound2 L h_L_eq h_D_eq h_sum_mk
        omega"""
)

# 5. Fix clear list in hd_div_q_ge3
content = content.replace(
    """            have h_ne2 : d / q ≠ 2 := by
              intro hc
              rw [hc] at h_odd_div
              contradiction
            clear h_sub h_sum_ge h_3d_le h_bound1 h_2k_ge hp_ge5
            omega""",
    """            have h_ne2 : d / q ≠ 2 := by
              intro hc
              rw [hc] at h_odd_div
              contradiction
            clear h_sub h_sum_ge h_3d_le h_bound1 h_2k_ge hp_ge5 h_sum_mk h_D h_D_eq h_D_ge_one
            omega"""
)

# 6. Fix h_s_ge_one to assist omega
content = content.replace(
    "    have h_s_ge_one : s ≥ 1 := by omega",
    """    have h_s_ge_one : s ≥ 1 := by
      have : a + 2 ≤ s := ha_lt
      omega"""
)

# 7. Fix type mismatches in replacement_d1 call to test_prime_D_one and D_ne_one
content = content.replace(
    """        · have h_sum_pr : m.divisors.sum id = m + 1 := prime_divisors_sum hp
          have h_false : False := test_prime_D_one m a hm_odd hp h_sum_pr h_D_one
          exact False.elim h_false
        · have h_sum_ne2' : m.divisors.sum id ≠ 2 * m - 1 := h_sum_ne2 hm_odd hm_ge_three
          have h_false : False := D_ne_one m a hm_odd hm_ge_three hp h_sum_ne2' h_D_one
          exact False.elim h_false""",
    """        · have h_sum_pr : m.divisors.sum id = m + 1 := prime_divisors_sum hp
          have h_D_one' : 2^(a+1) * m - (2^(a+1) - 1) * m.divisors.sum id = 1 := by rw [h_D_eq, h_D_one]
          have h_false : False := test_prime_D_one m a hm_odd hp h_sum_pr h_D_one'
          exact False.elim h_false
        · have h_sum_ne2' : m.divisors.sum id ≠ 2 * m - 1 := h_sum_ne2 hm_odd hm_ge_three
          have h_D_one' : 2^(a+1) * m - (2^(a+1) - 1) * m.divisors.sum id = 1 := by rw [h_D_eq, h_D_one]
          have h_false : False := D_ne_one m a hm_odd hm_ge_three hp h_sum_ne2' h_D_one'
          exact False.elim h_false"""
)

with open('/workspace/leanproject/Submission/Spec.lean', 'w') as f:
    f.write(content)

print("Applied third set of fixes!")
