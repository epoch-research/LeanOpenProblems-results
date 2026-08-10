import os

with open('/workspace/leanproject/Submission/Spec.lean', 'r') as f:
    content = f.read()

# 1. Delete the duplicate helper declarations block
first_prime_div = content.find("theorem prime_divisors_sum")
second_prime_div = content.find("theorem prime_divisors_sum", first_prime_div + 1)
h_sum_ne2_idx = content.find("theorem h_sum_ne2")

if second_prime_div != -1 and h_sum_ne2_idx != -1:
    content = content[:second_prime_div] + content[h_sum_ne2_idx:]
    print("Deleted duplicate helper declarations block.")
else:
    print("Warning: could not locate duplicate helper block.")

# 2. Fix divisors_prime_sq
content = content.replace(
    "· refine ⟨1, by decide, (pow_one d).symm⟩",
    "· refine ⟨1, by decide, (pow_one x).symm⟩"
)

# 3. Replace test_prime_D_one
test_prime_D_one_old = """theorem test_prime_D_one (m a : ℕ) (hm_odd : m % 2 = 1) (hp : Nat.Prime m) (h_sum : m.divisors.sum id = m + 1)
    (h_D : 2^(a+1) * m - (2^(a+1) - 1) * m.divisors.sum id = 1) : False := by
  rw [h_sum] at h_D
  have h_eq : 2^(a+1) * m = (2^(a+1) - 1) * (m + 1) + 1 := by omega
  have h_ring : (2^(a+1) - 1) * (m + 1) + 1 = 2^(a+1) * m + 2^(a+1) - m := by
    have h_pow_pos : 2^(a+1) ≥ 1 := by omega
    have h_mul : (2^(a+1) - 1) * (m + 1) = 2^(a+1) * (m + 1) - (m + 1) := by
      rw [Nat.sub_mul, one_mul]
    rw [h_mul]
    have h_pos : 2^(a+1) * (m + 1) ≥ m + 1 := Nat.le_mul_of_pos_left (m + 1) h_pow_pos
    omega
  rw [h_ring] at h_eq
  have hp_eq : m = 2^(a+1) := by omega
  have hp_even : m % 2 = 0 := by
    rw [hp_eq]
    rw [pow_succ]
    simp
  omega"""

test_prime_D_one_new = """theorem test_prime_D_one (m a : ℕ) (hm_odd : m % 2 = 1) (hp : Nat.Prime m) (h_sum : m.divisors.sum id = m + 1)
    (h_D : 2^(a+1) * m - (2^(a+1) - 1) * m.divisors.sum id = 1) : False := by
  rw [h_sum] at h_D
  generalize hX : 2^(a+1) = X
  rw [hX] at h_D
  have h_eq : X * m = (X - 1) * (m + 1) + 1 := by omega
  have h_ring : (X - 1) * (m + 1) + 1 = X * m + X - m := by
    have h_pow_pos : X ≥ 1 := by
      have : X > 0 := by
        rw [← hX]
        positivity
      omega
    have h_eq2 : (X - 1) * (m + 1) + (m + 1) = X * (m + 1) := by
      have h_one : (X - 1) * (m + 1) + (m + 1) = (X - 1) * (m + 1) + 1 * (m + 1) := by rw [one_mul]
      rw [h_one, ← add_mul]
      rw [Nat.sub_add_cancel h_pow_pos]
    have h_expand1 : (X - 1) * (m + 1) + (m + 1) = (X - 1) * (m + 1) + m + 1 := by ring
    have h_expand2 : X * (m + 1) = X * m + X := by ring
    rw [h_expand1] at h_eq2
    omega
  rw [h_ring] at h_eq
  have hp_eq : m = X := by omega
  have hp_even : m % 2 = 0 := by
    rw [hp_eq, ← hX]
    rw [pow_succ]
    simp
  omega"""

content = content.replace(test_prime_D_one_old, test_prime_D_one_new)

# 4. Fix h_sum_ne2
content = content.replace(
    "have hd_odd : d % 2 = 1 := hd_odd_test d (m/d) (by rwa [Nat.mul_div_cancel' hd] at hm_odd)",
    "have hd_odd : d % 2 = 1 := hd_odd_test d (m/d) (by rwa [← Nat.mul_div_cancel' hd] at hm_odd)"
)

content = content.replace(
    "exact hd_odd_test (m/d) d (by rwa [Nat.mul_comm, Nat.div_mul_cancel hd] at hm_odd)",
    "exact hd_odd_test (m/d) d (by rwa [← Nat.div_mul_cancel hd] at hm_odd)"
)

h_ring_contra_old = """      have h_ring_contra : (d - 1) * (d - 2) = 0 := by
        omega
      omega"""

h_ring_contra_new = """      have h_alg : d * d = d + 2 := by omega
      have h_ge : 3 * d > d + 2 := by omega
      have h_le : d * d ≥ 3 * d := Nat.mul_le_mul_right d hd_ge3
      omega"""

content = content.replace(h_ring_contra_old, h_ring_contra_new)

hmdm_sub_old = """        have : d = 1 := by
          have h_m_pos : m > 0 := by omega
          exact Nat.eq_of_mul_eq_mul_right (by omega) this"""

hmdm_sub_new = """        have h_eq' : m * 1 = m * d := by
          rw [mul_one]
          exact h_eq
        have h_m_pos : m > 0 := by omega
        have : 1 = d := Nat.eq_of_mul_eq_mul_left h_m_pos h_eq'"""

content = content.replace(hmdm_sub_old, hmdm_sub_new)

h_sum_ge_old = """      have h_sum_ge : 1 + d + m/d + m ≤ m.divisors.sum id := by
        have h_sum_four : ({1, d, m/d, m} : Finset ℕ).sum id = 1 + d + m/d + m := by
          rw [sum_insert (by simp [h1d, h1md, h1m]), sum_insert (by simp [hd_eq, hdm]), sum_insert (by simp [hmdm]), sum_singleton, id_eq, id_eq, id_eq, id_eq]
          omega
        rw [← h_sum_four]
        exact sum_le_sum_of_subset h_sub
      omega"""

h_sum_ge_new = """      have h_sum_ge : 1 + d + m/d + m ≤ m.divisors.sum id := by
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
        have : m = d * (m/d) := (Nat.div_mul_cancel hd).symm
        rw [this, h_eq]
      rw [hd_eq', hX_eq'] at h_sum_ge
      omega"""

# Wait, let's just make sure h_sum_ge_old matches the original
# Let's search if h_sum_ge_old is uniquely in the file:
if h_sum_ge_old in content:
    content = content.replace(h_sum_ge_old, h_sum_ge_new)
    print("Replaced h_sum_ge in h_sum_ne2.")
else:
    print("Warning: h_sum_ge_old not found.")

# 5. Fix D_ne_one
content = content.replace(
    "hd_odd_test p d (by rwa [h_pd] at hm_odd)",
    "hd_odd_test p d (by rwa [← h_pd] at hm_odd)"
)

h_sum_sq_old = """      have h_sum_sq : m.divisors.sum id = 1 + p + p * p := by
        have h_eq : m = p * p := h_pd.symm
        rw [h_eq]
        exact sum_divisors_prime_sq h_prime_p"""

h_sum_sq_new = """      have h_sum_sq : m.divisors.sum id = 1 + p + p * p := by
        have h_eq : m = p * p := by
          rw [← hc] at h_pd
          exact h_pd.symm
        rw [h_eq]
        exact sum_divisors_prime_sq h_prime_p"""

content = content.replace(h_sum_sq_old, h_sum_sq_new)

h_2k_old = """      have h_2k : 2 * k = p + 1 := by
        have h_sum_mk' := h_sum_mk
        rw [h_sum_sq] at h_sum_mk'
        have h_eq : m = p * p := h_pd.symm
        rw [h_eq] at h_sum_mk'
        omega"""

h_2k_new = """      have h_2k : 2 * k = p + 1 := by
        have h_sum_mk' := h_sum_mk
        rw [h_sum_sq] at h_sum_mk'
        have h_eq : m = p * p := by
          rw [← hc] at h_pd
          exact h_pd.symm
        rw [h_eq] at h_sum_mk'
        omega"""

h_alg_old = """      have h_alg : p * p = (2^(a+1) - 1) * (p + 1) + 1 := by
        have h_m_eq' := h_m_eq
        have h_eq : m = p * p := h_pd.symm
        rw [h_eq] at h_m_eq'
        rw [h_2k] at h_m_eq'
        exact h_m_eq'"""

h_alg_new = """      have h_alg : p * p = (2^(a+1) - 1) * (p + 1) + 1 := by
        have h_m_eq' := h_m_eq
        have h_eq : m = p * p := by
          rw [← hc] at h_pd
          exact h_pd.symm
        rw [h_eq] at h_m_eq'
        rw [h_2k] at h_m_eq'
        exact h_m_eq'"""

content = content.replace(h_alg_old, h_alg_new)

content = content.replace(h_2k_old, h_2k_new)

h_alg2_old = """      have h_alg2 : p * (p + 1) = 2^(a+1) * (p + 1) := by
        have h_sub_mul : (2^(a+1) - 1) * (p + 1) = 2^(a+1) * (p + 1) - (p + 1) := by
          rw [Nat.sub_mul, one_mul]
        rw [h_sub_mul] at h_alg
        have h_pos : 2^(a+1) * (p + 1) > 0 := by positivity
        omega"""

h_alg2_new = """      have h_alg2 : p * (p + 1) = 2^(a+1) * (p + 1) := by
        have h_sub_mul : (2^(a+1) - 1) * (p + 1) = 2^(a+1) * (p + 1) - (p + 1) := by
          rw [Nat.sub_mul, one_mul]
        rw [h_sub_mul] at h_alg
        have h_pos : 2^(a+1) * (p + 1) ≥ p + 1 := Nat.le_mul_of_pos_left (p + 1) (by positivity)
        have h_ring_id : p * p + p + 1 = p * (p + 1) + 1 := by ring
        omega"""

content = content.replace(h_alg2_old, h_alg2_new)

content = content.replace(
    "hd_odd_test d p (by rwa [mul_comm, h_pd] at hm_odd)",
    "hd_odd_test d p (by rwa [← h_pd, mul_comm] at hm_odd)"
)

content = content.replace(
    "· subst hp3",
    "· rw [hp3]"
)

d_div_q_old = """            have : d / q ≠ 1 := by
              intro hc
              have : d = q := by
                rw [← Nat.div_mul_cancel hq_dvd, hc, one_mul]
              have : Nat.Prime d := by rwa [← this]
              contradiction
            have : d / q ≠ 0 := by
              intro hc
              have : d = 0 := by
                rw [← Nat.div_mul_cancel hq_dvd, hc, zero_mul]
              omega
            have h_odd_div : (d / q) % 2 = 1 := hd_odd_test (d / q) q (by rwa [Nat.div_mul_cancel hq_dvd])
            have : d / q ≠ 2 := by
              intro hc
              rw [hc] at h_odd_div
              contradiction
            omega"""

d_div_q_new = """            have h_ne1 : d / q ≠ 1 := by
              intro hc
              have : d = q := by
                rw [← Nat.div_mul_cancel hq_dvd, hc, one_mul]
              have : Nat.Prime d := by rwa [← this]
              contradiction
            have h_ne0 : d / q ≠ 0 := by
              intro hc
              have : d = 0 := by
                rw [← Nat.div_mul_cancel hq_dvd, hc, zero_mul]
              omega
            have h_odd_div : (d / q) % 2 = 1 := hd_odd_test (d / q) q (by rwa [← Nat.div_mul_cancel hq_dvd] at hd_odd)
            have h_ne2 : d / q ≠ 2 := by
              intro hc
              rw [hc] at h_odd_div
              contradiction
            omega"""

content = content.replace(d_div_q_old, d_div_q_new)

content = content.replace(
    "have : d = q * (d / q) := (Nat.div_mul_cancel hq_dvd).symm",
    """have : d = q * (d / q) := by
            rw [mul_comm]
            exact (Nat.div_mul_cancel hq_dvd).symm"""
)

# 6. Fix S_le_two_pow
s_le_two_pow_hpow_old = """      have h_pos : 2 > 1 := by decide
      have h_lt_final := (Nat.pow_lt_pow_iff_right h_pos).mp h_pow
      exact h_lt_final"""

content = content.replace(s_le_two_pow_hpow_old, "      by omega")

indent_bullet_old = """      · have h_DL_ge : D * L ≥ 2 * L := Nat.mul_le_mul_right L h_D_ge_two
        omega
                  · have h_D_one : D = 1 := by omega"""

indent_bullet_new = """      · have h_DL_ge : D * L ≥ 2 * L := Nat.mul_le_mul_right L h_D_ge_two
        omega
      · have h_D_one : D = 1 := by omega"""

content = content.replace(indent_bullet_old, indent_bullet_new)

with open('/workspace/leanproject/Submission/Spec.lean', 'w') as f:
    f.write(content)

print("Finished applying all fixes to Spec.lean!")
