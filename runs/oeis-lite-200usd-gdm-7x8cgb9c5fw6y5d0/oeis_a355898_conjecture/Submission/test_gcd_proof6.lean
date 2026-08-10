import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 200000

open Nat

def B0 : ℕ := (A355898_loop 3772 1 1).1 + 1
def B1 : ℕ := (A355898_loop 3772 1 1).2 + 1

def B : ℕ → ℕ
| 0 => B0
| 1 => B1
| k + 2 => B (k + 1) + B k

theorem B_pos (m : ℕ) : 1 ≤ B m := by
  induction m with
  | zero =>
    unfold B B0
    decide
  | succ m ih =>
    cases m with
    | zero =>
      unfold B B1
      decide
    | succ m =>
      have h_rec : B (m + 2) = B (m + 1) + B m := rfl
      rw [h_rec]
      omega

theorem B_even (k : ℕ) : B k % 2 = 0 := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rcases k with _ | k
    · simp [B, B0]; decide
    · rcases k with _ | k
      · simp [B, B1]; decide
      · have h_rec : B (k + 2) = B (k + 1) + B k := rfl
        rw [h_rec]
        have ih1 := ih (k + 1) (by omega)
        have ih2 := ih k (by omega)
        omega

theorem gcd_step (k : ℕ) :
  Nat.gcd (B (k + 2) - 1) (B (k + 1) - 1) = Nat.gcd (B (k + 1) - 1) (B k) := by
  have h_rec : B (k + 2) = B (k + 1) + B k := rfl
  have h_sub : B (k + 2) - 1 = B (k + 1) - 1 + B k := by
    have h_ge1 : 1 ≤ B (k + 1) := B_pos (k + 1)
    omega
  rw [h_sub]
  rw [add_comm (B (k + 1) - 1) (B k)]
  rw [Nat.gcd_add_self_left]
  rw [Nat.gcd_comm]

theorem base_gcd_0 : Nat.gcd (B 1 - 1) (B 0 - 1) = 1 := by decide
theorem base_gcd_1 : Nat.gcd (B 1 - 1) (B 0) = 1 := by decide
theorem base_gcd_2 : Nat.gcd (B 2 - 1) (B 1 - 1) = 1 := by decide
theorem base_gcd_3 : Nat.gcd (B 3 - 1) (B 2 - 1) = 1 := by decide

def C_val : ℕ := B 1^2 - B 2 * B 0

theorem B_le : B 2 * B 0 ≤ B 1^2 := by
  have h_B2 : B 2 = B 1 + B 0 := rfl
  have h_B1 : B 1 = B1 := rfl
  have h_B0 : B 0 = B0 := rfl
  rw [h_B2, h_B1, h_B0]
  unfold B1 B0
  decide

theorem Cassini (k : ℕ) :
  (Even k → B (k + 1)^2 = B (k + 2) * B k + C_val) ∧
  (Odd k → B (k + 2) * B k = B (k + 1)^2 + C_val) := by
  induction k with
  | zero =>
    constructor
    · intro _
      simp [B, C_val]
      exact (Nat.add_sub_of_le B_le).symm
    · intro h
      rcases h with ⟨r, hr⟩
      omega
  | succ k ih =>
    constructor
    · intro h_even
      have h_odd : Odd k := by
        rcases h_even with ⟨r, hr⟩
        have : r ≠ 0 := by omega
        use r - 1
        omega
      have ih_odd := ih.2 h_odd
      have h_rec : B (k + 3) = B (k + 2) + B (k + 1) := rfl
      rw [h_rec]
      rw [add_mul]
      have h_sq : B (k + 1) * B (k + 1) = B (k + 1)^2 := by ring
      rw [h_sq]
      have h_assoc : B (k + 2) * B (k + 1) + B (k + 1)^2 + C_val = B (k + 2) * B (k + 1) + (B (k + 1)^2 + C_val) := by ring
      rw [h_assoc, ← ih_odd]
      have h_rec2 : B (k + 2) = B (k + 1) + B k := rfl
      have h_algebra : B (k + 2) * B (k + 1) + B (k + 2) * B k = B (k + 2) * B (k + 2) := by
        rw [← mul_add, ← h_rec2]
      rw [h_algebra]
      ring
    · intro h_odd
      have h_even : Even k := by
        rcases h_odd with ⟨r, hr⟩
        use r
        omega
      have ih_even := ih.1 h_even
      have h_rec : B (k + 3) = B (k + 2) + B (k + 1) := rfl
      rw [h_rec]
      rw [add_mul]
      have h_sq : B (k + 1) * B (k + 1) = B (k + 1)^2 := by ring
      rw [h_sq, ih_even]
      have h_rec2 : B (k + 2) = B (k + 1) + B k := rfl
      have h_algebra : B (k + 2) * B (k + 1) + (B (k + 2) * B k + C_val) = B (k + 2) * B (k + 2) + C_val := by
        rw [← add_assoc, ← mul_add, ← h_rec2]
      rw [h_algebra]
      ring

lemma odd_of_dvd_odd {a d : ℕ} (h_div : d ∣ a) (h_odd : a % 2 = 1) : d % 2 = 1 := by
  by_contra h
  have h_even : d % 2 = 0 := by omega
  have h_2_dvd_d : 2 ∣ d := Nat.dvd_of_mod_eq_zero h_even
  have h_2_dvd_a : 2 ∣ a := Nat.dvd_trans h_2_dvd_d h_div
  have h_a_even : a % 2 = 0 := Nat.mod_eq_zero_of_dvd h_2_dvd_a
  omega

theorem B_gcd (k : ℕ) : Nat.gcd (B (k + 1) - 1) (B k - 1) = 1 := by
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
        · rcases k with _ | k
          · exact base_gcd_3
          · -- Case k >= 1 (since k + 4)
            have ih_kp1 := ih (k + 3) (by omega)
            set d := Nat.gcd (B (k + 5) - 1) (B (k + 4) - 1)
            have hd1 : d ∣ B (k + 5) - 1 := Nat.gcd_dvd_left _ _
            have hd2 : d ∣ B (k + 4) - 1 := Nat.gcd_dvd_right _ _
            have hd_Bkp1 : d ∣ B (k + 3) := by
              have hd_eq : d = Nat.gcd (B (k + 4) - 1) (B (k + 3)) := gcd_step (k + 3)
              rw [hd_eq]
              exact Nat.gcd_dvd_right _ _
            have h_pos1 : 1 ≤ B (k + 5) := B_pos (k + 5)
            have h_pos2 : 1 ≤ B (k + 4) := B_pos (k + 4)
            have h_pos3 : 1 ≤ B (k + 3) := B_pos (k + 3)
            have h_pos4 : 1 ≤ B (k + 2) := B_pos (k + 2)
            have hd1_z : (d : ℤ) ∣ (B (k + 5) : ℤ) - 1 := by
              have h_sub : ((B (k + 5) - 1 : ℕ) : ℤ) = (B (k + 5) : ℤ) - 1 := by omega
              rw [← h_sub]
              exact Int.ofNat_dvd.mpr hd1
            have hd2_z : (d : ℤ) ∣ (B (k + 4) : ℤ) - 1 := by
              have h_sub : ((B (k + 4) - 1 : ℕ) : ℤ) = (B (k + 4) : ℤ) - 1 := by omega
              rw [← h_sub]
              exact Int.ofNat_dvd.mpr hd2
            obtain ⟨q2, hq2⟩ := hd1_z
            obtain ⟨q1, hq1⟩ := hd2_z
            obtain ⟨q3, hq3⟩ := hd_Bkp1
            have hBkp1_z : (B (k + 3) : ℤ) = d * q3 := by exact_mod_cast hq3
            have hBkp2_z : (B (k + 4) : ℤ) = d * q1 + 1 := by omega
            have hBkp3_z : (B (k + 5) : ℤ) = d * q2 + 1 := by omega
            have hBk_z : (B (k + 2) : ℤ) = d * (q1 - q3) + 1 := by
              have h_rec : (B (k + 4) : ℤ) = (B (k + 3) : ℤ) + (B (k + 2) : ℤ) := by
                have : B (k + 4) = B (k + 3) + B (k + 2) := rfl
                omega
              rw [hBkp2_z, hBkp1_z] at h_rec
              linarith
            have hd_B_sub_1 : (d : ℤ) ∣ (B (k + 2) : ℤ) - 1 := by
              use q1 - q3
              omega
            have hd_Bkm1_nat : d ∣ B (k + 2) - 1 := by
              have h_cast : (B (k + 2) : ℤ) - 1 = ((B (k + 2) - 1 : ℕ) : ℤ) := by omega
              rw [h_cast] at hd_B_sub_1
              exact Int.ofNat_dvd.mp hd_B_sub_1
            have h_cass := Cassini (k + 2)
            have hd_C : (d : ℤ) ∣ 2 := by
              by_cases h_even : Even (k + 3)
              · have h_odd : Odd (k + 2) := by
                  rcases h_even with ⟨r, hr⟩
                  have : r ≠ 0 := by omega
                  use r - 1
                  omega
                have h_cass_odd := h_cass.2 h_odd
                have h_cast : ((B (k + 4) * B (k + 2) : ℕ) : ℤ) = ((B (k + 3)^2 + C_val : ℕ) : ℤ) := by exact_mod_cast h_cass_odd
                push_cast at h_cast
                have h_C_sub_1 : (C_val : ℤ) - 1 = (B (k + 4) : ℤ) * (B (k + 2) : ℤ) - (B (k + 3) : ℤ)^2 - 1 := by
                  rw [h_cast]
                  ring
                have hd_C_sub_1 : (d : ℤ) ∣ (C_val : ℤ) - 1 := by
                  use q2 * (q1 - q3) * d + q2 + (q1 - q3) - q3^2 * d
                  rw [h_C_sub_1, hBkp3_z, hBk_z, hBkp1_z]
                  ring
                have h_cass_kp1 := Cassini (k + 1)
                have h_odd_km1 : Odd (k + 1) := by
                  rcases h_even with ⟨r, hr⟩
                  have : r ≥ 1 := by omega
                  use r - 1
                  omega
                have h_cass_odd_km1 := h_cass_kp1.2 h_odd_km1
                have h_cast_km1 : ((B (k + 3) * B (k + 1) : ℕ) : ℤ) = ((B (k + 2)^2 + C_val : ℕ) : ℤ) := by exact_mod_cast h_cass_odd_km1
                push_cast at h_cast_km1
                have h_C_add_1 : (C_val : ℤ) + 1 = (B (k + 3) : ℤ) * (B (k + 1) : ℤ) - (B (k + 2) : ℤ)^2 + 1 := by
                  rw [h_cast_km1]
                  ring
                have hBkm1_z : (B (k + 1) : ℤ) = d * (2 * q3 - q1) - 1 := by
                  have h_rec : (B (k + 2) : ℤ) = (B (k + 1) : ℤ) + (B k : ℤ) := rfl
                  have h_rec_z : (B (k + 2) : ℤ) = (B (k + 1) : ℤ) + (B k : ℤ) := by exact_mod_cast h_rec
                  have h_rec_sh : B (k + 2) = B (k + 1) + B k := rfl
                  have h_rec_sh_z : (B (k + 2) : ℤ) = (B (k + 1) : ℤ) + (B k : ℤ) := by exact_mod_cast h_rec_sh
                  have h_rec_actual : B (k + 3) = B (k + 2) + B (k + 1) := by
                    have h1 : k + 3 = (k + 1) + 2 := by omega
                    have h2 : k + 2 = (k + 1) + 1 := by omega
                    rw [h1, h2]
                    rfl
                  have h_rec_actual_z : (B (k + 3) : ℤ) = (B (k + 2) : ℤ) + (B (k + 1) : ℤ) := by exact_mod_cast h_rec_actual
                  rw [hBkp2_z, hBkp1_z] at h_rec_actual_z
                  linarith
                have hd_C_add_1 : (d : ℤ) ∣ (C_val : ℤ) + 1 := by
                  use q1 * (2 * q3 - q1) * d - q1 + (2 * q3 - q1) - q3^2 * d
                  rw [h_C_add_1, hBkp2_z, hBkm1_z, hBkp1_z]
                  ring
                have hd_diff : (d : ℤ) ∣ 2 := by
                  have h_diff : (2 : ℤ) = (C_val : ℤ) + 1 - ((C_val : ℤ) - 1) := by ring
                  rw [h_diff]
                  exact dvd_sub hd_C_add_1 hd_C_sub_1
                exact hd_diff
            · have h_even_k : Even (k + 2) := by
                have h_odd : Odd (k + 3) := (Nat.even_or_odd (k + 3)).resolve_left h_even
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
                use q3^2 * d - q1 * (q1 - q3) * d - q1 - (q1 - q3)
                rw [h_C_add_1, hBkp2_z, hBk_z, hBkp1_z]
                ring
              have h_cass_kp1 := Cassini (k + 1)
              have h_even_km1 : Even (k + 1) := by
                have h_odd : Odd (k + 3) := (Nat.even_or_odd (k + 3)).resolve_left h_even
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
                have h_rec_actual : B (k + 3) = B (k + 2) + B (k + 1) := by
                  have h1 : k + 3 = (k + 1) + 2 := by omega
                  have h2 : k + 2 = (k + 1) + 1 := by omega
                  rw [h1, h2]
                  rfl
                have h_rec_actual_z : (B (k + 3) : ℤ) = (B (k + 2) : ℤ) + (B (k + 1) : ℤ) := by exact_mod_cast h_rec_actual
                rw [hBkp2_z, hBkp1_z] at h_rec_actual_z
                linarith
              have hd_C_sub_1 : (d : ℤ) ∣ (C_val : ℤ) - 1 := by
                use (q1 - q3)^2 * d + 2 * (q1 - q3) - q3 * (2 * q3 - q1) * d + q3
                rw [show (C_val : ℤ) - 1 = (B (k + 1) : ℤ)^2 - (B (k + 2) : ℤ) * (B (k + 2 - 2) : ℤ) - 1 by congr 2; omega]
                rw [hBk_z, hBkp1_z, hBkm1_z]
                ring
              have hd_diff : (d : ℤ) ∣ 2 := by
                have h_diff : (2 : ℤ) = (C_val : ℤ) + 1 - ((C_val : ℤ) - 1) := by ring
                rw [h_diff]
                exact dvd_sub hd_C_add_1 hd_C_sub_1
              exact hd_diff
          have hd_2_nat : d ∣ 2 := Int.ofNat_dvd.mp hd_C
          have hd_odd : d % 2 = 1 := by
            have h_even_Bkp1 : B (k + 4) % 2 = 0 := B_even (k + 4)
            have h_odd_Bkp1 : (B (k + 4) - 1) % 2 = 1 := by omega
            exact odd_of_dvd_odd hd2 h_odd_Bkp1
          rcases Nat.dvd_prime Nat.prime_two |>.mp hd_2_nat with hd_1 | hd_2
          · exact hd_1
          · have : d = 2 := hd_2
            omega
