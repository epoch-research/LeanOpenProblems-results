import os

with open('/workspace/leanproject/Submission/Spec.lean', 'r') as f:
    content = f.read()

# 1. Fix h_eq' in hmdm
content = content.replace(
    """        have h_eq' : m * 1 = m * d := by
          rw [mul_one]
          exact h_eq""",
    """        have h_eq' : m * 1 = m * d := by
          rw [mul_one]
          exact this"""
)

# 2. Fix Nat.div_mul_cancel in hm_eq
content = content.replace(
    """      have hm_eq : m = (d - 1) * (m/d - 1) + (d - 1) + (m/d - 1) + 1 := by
        have : m = d * (m/d) := (Nat.div_mul_cancel hd).symm
        rw [this, h_eq]""",
    """      have hm_eq : m = (d - 1) * (m/d - 1) + (d - 1) + (m/d - 1) + 1 := by
        have : m = d * (m/d) := by
          rw [mul_comm]
          exact (Nat.div_mul_cancel hd).symm
        rw [this, h_eq]"""
)

# 3. Fix rewrite ordering in h_sum_ge
content = content.replace(
    "      rw [hd_eq', hX_eq'] at h_sum_ge",
    "      rw [hX_eq', hd_eq'] at h_sum_ge"
)

# 4. Fix hp3 in D_ne_one
content = content.replace(
    """    by_cases hp3 : p = 3
    · rw [hp3]
      omega""",
    """    by_cases hp3 : p = 3
    · omega"""
)

# 5. Fix hp_ge5 in D_ne_one
content = content.replace(
    "      have hp_ge5 : p ≥ 5 := by omega",
    """      have hp_ge5 : p ≥ 5 := by
        clear D h_D_ge_one h_D h_D_calc h_trans_final h_final_bound h_final_bound2 L h_L_eq h_D_eq
        omega"""
)

# 6. Fix rwa in Nat.Prime d
content = content.replace(
    "              have : Nat.Prime d := by rwa [← this]",
    "              have : Nat.Prime d := by rwa [this]"
)

# 7. Fix omega in hd_div_q_ge3
content = content.replace(
    """            have h_ne2 : d / q ≠ 2 := by
              intro hc
              rw [hc] at h_odd_div
              contradiction
            omega""",
    """            have h_ne2 : d / q ≠ 2 := by
              intro hc
              rw [hc] at h_odd_div
              contradiction
            clear h_sub h_sum_ge h_3d_le h_bound1 h_2k_ge hp_ge5
            omega"""
)

# 8. Fix by omega in ha_lt
content = content.replace(
    """      by omega
    have h_s_ge_one""",
    """      omega
    have h_s_ge_one"""
)

with open('/workspace/leanproject/Submission/Spec.lean', 'w') as f:
    f.write(content)

print("Applied second set of fixes!")
