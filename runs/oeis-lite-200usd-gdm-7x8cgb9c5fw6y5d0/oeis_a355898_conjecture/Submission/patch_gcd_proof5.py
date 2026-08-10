import os

with open("/workspace/leanproject/Submission/test_gcd_proof5.lean", "r") as f:
    lines = f.readlines()

# Let's locate the sub-cases and rewrite them with the corrected formulas.
# Specifically, we want to update B_gcd from line 133 onwards.

# Let's create the entire B_gcd proof cleanly and overwrite the old one.
proof_lines = """theorem B_gcd (k : ℕ) : Nat.gcd (B (k + 1) - 1) (B k - 1) = 1 := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rcases k with _ | k
    · exact base_gcd_0
    · rcases k with _ | k
      · have h_gcd := gcd_step 0
        rw [h_gcd]
        exact base_gcd_1
      · rcases k with _ | k
        · exact base_gcd_2
        · -- Case k >= 1 (since k + 3)
          have ih_kp1 := ih (k + 2) (by omega)
          set d := Nat.gcd (B (k + 4) - 1) (B (k + 3) - 1)
          have hd1 : d ∣ B (k + 4) - 1 := Nat.gcd_dvd_left _ _
          have hd2 : d ∣ B (k + 3) - 1 := Nat.gcd_dvd_right _ _
          have hd_Bkp1 : d ∣ B (k + 2) := by
            have hd_eq : d = Nat.gcd (B (k + 3) - 1) (B (k + 2)) := gcd_step (k + 2)
            rw [hd_eq]
            exact Nat.gcd_dvd_right _ _
          have h_pos1 : 1 ≤ B (k + 4) := B_pos (k + 4)
          have h_pos2 : 1 ≤ B (k + 3) := B_pos (k + 3)
          have h_pos3 : 1 ≤ B (k + 2) := B_pos (k + 2)
          have h_pos4 : 1 ≤ B (k + 1) := B_pos (k + 1)
          have hd1_z : (d : ℤ) ∣ (B (k + 4) : ℤ) - 1 := by
            have h_sub : ((B (k + 4) - 1 : ℕ) : ℤ) = (B (k + 4) : ℤ) - 1 := by omega
            rw [← h_sub]
            exact Int.ofNat_dvd.mpr hd1
          have hd2_z : (d : ℤ) ∣ (B (k + 3) : ℤ) - 1 := by
            have h_sub : ((B (k + 3) - 1 : ℕ) : ℤ) = (B (k + 3) : ℤ) - 1 := by omega
            rw [← h_sub]
            exact Int.ofNat_dvd.mpr hd2
          obtain ⟨q2, hq2⟩ := hd1_z
          obtain ⟨q1, hq1⟩ := hd2_z
          obtain ⟨q3, hq3⟩ := hd_Bkp1
          have hBkp1_z : (B (k + 2) : ℤ) = d * q3 := by exact_mod_cast hq3
          have hBkp2_z : (B (k + 3) : ℤ) = d * q1 + 1 := by omega
          have hBkp3_z : (B (k + 4) : ℤ) = d * q2 + 1 := by omega
          have hBk_z : (B (k + 1) : ℤ) = d * (q1 - q3) + 1 := by
            have h_rec : (B (k + 3) : ℤ) = (B (k + 2) : ℤ) + (B (k + 1) : ℤ) := by
              have : B (k + 3) = B (k + 2) + B (k + 1) := rfl
              omega
            rw [hBkp2_z, hBkp1_z] at h_rec
            linarith
          have hd_B_sub_1 : (d : ℤ) ∣ (B (k + 1) : ℤ) - 1 := by
            use q1 - q3
            omega
          have hd_Bkm1_nat : d ∣ B (k + 1) - 1 := by
            have h_cast : (B (k + 1) : ℤ) - 1 = ((B (k + 1) - 1 : ℕ) : ℤ) := by omega
            rw [h_cast] at hd_B_sub_1
            exact Int.ofNat_dvd.mp hd_B_sub_1
          have h_cass := Cassini (k + 1)
          have hd_C : (d : ℤ) ∣ 2 := by
            by_cases h_even : Even (k + 2)
            · have h_odd : Odd (k + 1) := by
                rcases h_even with ⟨r, hr⟩
                have : r ≠ 0 := by omega
                use r - 1
                omega
              have h_cass_odd := h_cass.2 h_odd
              have h_cast : ((B (k + 3) * B (k + 1) : ℕ) : ℤ) = ((B (k + 2)^2 + C_val : ℕ) : ℤ) := by exact_mod_cast h_cass_odd
              push_cast at h_cast
              have h_C_sub_1 : (C_val : ℤ) - 1 = (B (k + 3) : ℤ) * (B (k + 1) : ℤ) - (B (k + 2) : ℤ)^2 - 1 := by
                rw [h_cast]
                ring
              have hd_C_sub_1 : (d : ℤ) ∣ (C_val : ℤ) - 1 := by
                use q1 * (q1 - q3) * d + 2 * q1 - q3 - q3^2 * d
                rw [h_C_sub_1, hBkp2_z, hBk_z, hBkp1_z]
                ring
              have h_cass_kp1 := Cassini (k)
              have h_odd_km1 : Odd (k) := by
                rcases h_even with ⟨r, hr⟩
                have : r ≥ 1 := by omega
                use r - 1
                omega
              have h_cass_odd_km1 := h_cass_kp1.2 h_odd_km1
              have h_cast_km1 : ((B (k + 2) * B k : ℕ) : ℤ) = ((B (k + 1)^2 + C_val : ℕ) : ℤ) := by exact_mod_cast h_cass_odd_km1
              push_cast at h_cast_km1
              have h_C_add_1 : (C_val : ℤ) + 1 = (B (k + 2) : ℤ) * (B k : ℤ) - (B (k + 1) : ℤ)^2 + 1 := by
                rw [h_cast_km1]
                ring
              have hBkm1_z : (B k : ℤ) = d * (2 * q3 - q1) - 1 := by
                have h_rec : (B (k + 2) : ℤ) = (B (k + 1) : ℤ) + (B k : ℤ) := by
                  have h1 : k + 2 = k + 2 := rfl
                  have h2 : k + 1 = k + 1 := rfl
                  rfl
                rw [hBkp1_z, hBk_z] at h_rec
                linarith
              have hd_C_add_1 : (d : ℤ) ∣ (C_val : ℤ) + 1 := by
                use q3 * (2 * q3 - q1) * d - q3 - (q1 - q3)^2 * d - 2 * (q1 - q3)
                rw [h_C_add_1, hBkp1_z, hBkm1_z, hBk_z]
                ring
              have hd_diff : (d : ℤ) ∣ 2 := by
                have h_diff : (2 : ℤ) = (C_val : ℤ) + 1 - ((C_val : ℤ) - 1) := by ring
                rw [h_diff]
                exact dvd_sub hd_C_add_1 hd_C_sub_1
              exact hd_diff
            · have h_even_k : Even (k + 1) := by
                have h_odd : Odd (k + 2) := (Nat.even_or_odd (k + 2)).resolve_left h_even
                rcases h_odd with ⟨r, hr⟩
                use r
                omega
              have h_cass_even := h_cass.1 h_even_k
              have h_cast : ((B (k + 2)^2 : ℕ) : ℤ) = ((B (k + 3) * B (k + 1) + C_val : ℕ) : ℤ) := by exact_mod_cast h_cass_even
              push_cast at h_cast
              have h_C_add_1 : (C_val : ℤ) + 1 = (B (k + 2) : ℤ)^2 - (B (k + 3) : ℤ) * (B (k + 1) : ℤ) + 1 := by
                rw [h_cast]
                ring
              have hd_C_add_1 : (d : ℤ) ∣ (C_val : ℤ) + 1 := by
                use q3^2 * d - q1 * (q1 - q3) * d - 2 * q1 + q3
                rw [h_C_add_1, hBkp1_z, hBkp2_z, hBk_z]
                ring
              have h_cass_kp1 := Cassini (k)
              have h_even_km1 : Even (k) := by
                have h_odd : Odd (k + 2) := (Nat.even_or_odd (k + 2)).resolve_left h_even
                rcases h_odd with ⟨r, hr⟩
                have : r ≥ 1 := by omega
                use r - 1
                omega
              have h_cass_even_km1 := h_cass_kp1.1 h_even_km1
              have h_cast_km1 : ((B (k + 1)^2 : ℕ) : ℤ) = ((B (k + 2) * B k + C_val : ℕ) : ℤ) := by exact_mod_cast h_cass_even_km1
              push_cast at h_cast_km1
              have h_C_sub_1 : (C_val : ℤ) - 1 = (B (k + 1) : ℤ)^2 - (B (k + 2) : ℤ) * (B k : ℤ) - 1 := by
                rw [h_cast_km1]
                ring
              have hBkm1_z : (B k : ℤ) = d * (2 * q3 - q1) - 1 := by
                have h_rec : (B (k + 2) : ℤ) = (B (k + 1) : ℤ) + (B k : ℤ) := rfl
                rw [hBkp1_z, hBk_z] at h_rec
                linarith
              have hd_C_sub_1 : (d : ℤ) ∣ (C_val : ℤ) - 1 := by
                use (q1 - q3)^2 * d + 2 * (q1 - q3) - q3 * (2 * q3 - q1) * d + q3
                rw [show (C_val : ℤ) - 1 = (B (k + 1) : ℤ)^2 - (B (k + 2) : ℤ) * (B k : ℤ) - 1 by congr 2; omega]
                rw [hBk_z, hBkp1_z, hBkm1_z]
                ring
              have hd_diff : (d : ℤ) ∣ 2 := by
                have h_diff : (2 : ℤ) = (C_val : ℤ) + 1 - ((C_val : ℤ) - 1) := by ring
                rw [h_diff]
                exact dvd_sub hd_C_add_1 hd_C_sub_1
              exact hd_diff
          have hd_2_nat : d ∣ 2 := Int.ofNat_dvd.mp hd_C
          have hd_odd : d % 2 = 1 := by
            have h_even_Bkp1 : B (k + 3) % 2 = 0 := B_even (k + 3)
            have h_odd_Bkp1 : (B (k + 3) - 1) % 2 = 1 := by omega
            exact odd_of_dvd_odd hd2 h_odd_Bkp1
          have hd_le_2 : d = 1 ∨ d = 2 := by omega
          rcases hd_le_2 with hd_1 | hd_2
          · exact hd_1
          · have : d = 2 := hd_2
            omega
"""

new_lines = lines[:126] + [proof_lines]

with open("/workspace/leanproject/Submission/test_gcd_proof5.lean", "w") as f:
    f.writelines(new_lines)
