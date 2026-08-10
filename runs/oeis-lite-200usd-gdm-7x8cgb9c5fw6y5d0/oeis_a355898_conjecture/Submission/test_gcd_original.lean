import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 200000

open Nat

def B0 : ℕ := 2
def B1 : ℕ := 3
def A3772 : ℕ := 1

def B : ℕ → ℕ
| 0 => B0
| 1 => B1
| k + 2 => B (k + 1) + B k

theorem B_pos (m : ℕ) : 1 ≤ B m := by
  induction m with
  | zero =>
    unfold B B0
    omega
  | succ m ih =>
    cases m with
    | zero =>
      unfold B B1
      omega
    | succ m =>
      have h_rec : B (m + 2) = B (m + 1) + B m := rfl
      rw [h_rec]
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

theorem base_gcd_0 : Nat.gcd (B 1 - 1) (B 0 - 1) = 1 := by
  unfold B B0 B1
  decide

theorem base_gcd_1 : Nat.gcd (B 1 - 1) (B 0) = 1 := by
  unfold B B0 B1
  decide

theorem base_gcd_2 : Nat.gcd (B 1) (B 0 - 1) = 1 := by
  unfold B B0 B1
  decide

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

theorem B_even (k : ℕ) : B k % 2 = 0 := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rcases k with _ | k
    · unfold B B0; decide
    · rcases k with _ | k
      · unfold B B1; decide
      · have h_rec : B (k + 2) = B (k + 1) + B k := rfl
        rw [h_rec]
        have ih1 := ih (k + 1) (by omega)
        have ih2 := ih k (by omega)
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
      · -- Case k >= 2 (since k + 2)
        -- We want to prove Nat.gcd (B (k + 3) - 1) (B (k + 2) - 1) = 1
        -- By ih at k+1: Nat.gcd (B (k + 2) - 1) (B (k + 1) - 1) = 1
        have ih_kp1 := ih (k + 1) (by omega)
        -- We define d:
        set d := Nat.gcd (B (k + 3) - 1) (B (k + 2) - 1)
        have hd1 : d ∣ B (k + 3) - 1 := Nat.gcd_dvd_left _ _
        have hd2 : d ∣ B (k + 2) - 1 := Nat.gcd_dvd_right _ _
        -- We show d ∣ B (k+1):
        have hd_Bkp1 : d ∣ B (k + 1) := by
          have hd_eq : d = Nat.gcd (B (k + 2) - 1) (B (k + 1)) := gcd_step (k + 1)
          rw [hd_eq]
          exact Nat.gcd_dvd_right _ _
        -- We cast to Int:
        have h_pos1 : 1 ≤ B (k + 3) := B_pos (k + 3)
        have h_pos2 : 1 ≤ B (k + 2) := B_pos (k + 2)
        have h_pos3 : 1 ≤ B (k + 1) := B_pos (k + 1)
        have h_pos4 : 1 ≤ B k := B_pos k
        have hd1_z : (d : ℤ) ∣ (B (k + 3) : ℤ) - 1 := by
          have h_sub : (B (k + 3) - 1 : ℤ) = (B (k + 3) : ℤ) - 1 := by omega
          have hd1_cast : (d : ℤ) ∣ (B (k + 3) - 1 : ℤ) := Int.ofNat_dvd.mpr hd1
          rw [h_sub] at hd1_cast
          exact hd1_cast
        have hd2_z : (d : ℤ) ∣ (B (k + 2) : ℤ) - 1 := by
          have h_sub : (B (k + 2) - 1 : ℤ) = (B (k + 2) : ℤ) - 1 := by omega
          have hd2_cast : (d : ℤ) ∣ (B (k + 2) - 1 : ℤ) := Int.ofNat_dvd.mpr hd2
          rw [h_sub] at hd2_cast
          exact hd2_cast
        obtain ⟨q2, hq2⟩ := hd1_z
        obtain ⟨q1, hq1⟩ := hd2_z
        obtain ⟨q3, hq3⟩ := hd_Bkp1
        have hBkp1_z : (B (k + 1) : ℤ) = d * q3 := by exact_mod_cast hq3
        have hBkp2_z : (B (k + 2) : ℤ) = d * q1 + 1 := by omega
        have hBk_z : (B k : ℤ) = d * (q1 - q3) + 1 := by
          have h_rec : (B (k + 2) : ℤ) = (B (k + 1) : ℤ) + (B k : ℤ) := by
            have : B (k + 2) = B (k + 1) + B k := rfl
            omega
          rw [hBkp2_z, hBkp1_z] at h_rec
          linarith
        have hd_B_sub_1 : (d : ℤ) ∣ (B k : ℤ) - 1 := by
          use q1 - q3
          omega
        have hd_Bkm1_nat : d ∣ B k - 1 := by
          have h_cast : (B k : ℤ) - 1 = ((B k - 1 : ℕ) : ℤ) := by omega
          rw [h_cast] at hd_B_sub_1
          exact Int.ofNat_dvd.mp hd_B_sub_1
        have h_cass := Cassini (k)
        have hd_C : (d : ℤ) ∣ 2 := by
          by_cases h_even : Even (k + 1)
          · have h_odd : Odd k := by
              rcases h_even with ⟨r, hr⟩
              have : r ≠ 0 := by omega
              use r - 1
              omega
            have h_cass_odd := h_cass.2 h_odd
            have h_cast : ((B (k + 2) * B k) : ℤ) = ((B (k + 1)^2 + C_val) : ℤ) := congrArg (fun x => (x : ℤ)) h_cass_odd
            push_cast at h_cast
            have h_C_sub_1 : (C_val : ℤ) - 1 = (B (k + 2) : ℤ) * (B k : ℤ) - (B (k + 1) : ℤ)^2 - 1 := by
              rw [h_cast]
              ring
            have hd_C_sub_1 : (d : ℤ) ∣ (C_val : ℤ) - 1 := by
              use q1 * (q1 - q3) * d + q1 + (q1 - q3) - q3^2 * d
              rw [h_C_sub_1, hBkp2_z, hBk_z, hBkp1_z]
              ring
            have h_cass_kp1 := Cassini (k + 1)
            have h_cass_even := h_cass_kp1.1 h_even
            have h_cast_kp1 : ((B (k + 2)^2) : ℤ) = ((B (k + 3) * B (k + 1) + C_val) : ℤ) := congrArg (fun x => (x : ℤ)) h_cass_even
            push_cast at h_cast_kp1
            have h_C_add_1 : (C_val : ℤ) + 1 = (B (k + 2) : ℤ)^2 - (B (k + 3) : ℤ) * (B (k + 1) : ℤ) + 1 := by
              rw [h_cast_kp1]
              ring
            have hd_C_add_1 : (d : ℤ) ∣ (C_val : ℤ) + 1 := by
              use q1^2 * d + 2 * q1 - q2 * q3 * d - q3
              rw [h_C_add_1, hBkp2_z, hBkp1_z, hq2]
              ring
            have hd_diff : (d : ℤ) ∣ (C_val : ℤ) + 1 - ((C_val : ℤ) - 1) := dvd_sub hd_C_add_1 hd_C_sub_1
            have h_ring : (C_val : ℤ) + 1 - ((C_val : ℤ) - 1) = 2 := by ring
            rw [h_ring] at hd_diff
            exact hd_diff
          · have h_even_k : Even k := by
              have h_odd : Odd (k + 1) := by omega
              rcases h_odd with ⟨r, hr⟩
              use r
              omega
            have h_cass_even := h_cass.1 h_even_k
            have h_cast : ((B (k + 1)^2) : ℤ) = ((B (k + 2) * B k + C_val) : ℤ) := congrArg (fun x => (x : ℤ)) h_cass_even
            push_cast at h_cast
            have h_C_add_1 : (C_val : ℤ) + 1 = (B (k + 1) : ℤ)^2 - (B (k + 2) : ℤ) * (B k : ℤ) + 1 := by
              rw [h_cast]
              ring
            have hd_C_add_1 : (d : ℤ) ∣ (C_val : ℤ) + 1 := by
              use q3^2 * d - q1 * (q1 - q3) * d - q1 - (q1 - q3)
              rw [h_C_add_1, hBkp2_z, hBk_z, hBkp1_z]
              ring
            have h_cass_kp1 := Cassini (k + 1)
            have h_odd_kp1 : Odd (k + 1) := by omega
            have h_cass_odd := h_cass_kp1.2 h_odd_kp1
            have h_cast_kp1 : ((B (k + 3) * B (k + 1)) : ℤ) = ((B (k + 2)^2 + C_val) : ℤ) := congrArg (fun x => (x : ℤ)) h_cass_odd
            push_cast at h_cast_kp1
            have h_C_sub_1 : (C_val : ℤ) - 1 = (B (k + 3) : ℤ) * (B (k + 1) : ℤ) - (B (k + 2) : ℤ)^2 - 1 := by
              rw [h_cast_kp1]
              ring
            have hd_C_sub_1 : (d : ℤ) ∣ (C_val : ℤ) - 1 := by
              use q2 * q3 * d + q3 - q1^2 * d - 2 * q1
              rw [h_C_sub_1, hBkp2_z, hBkp1_z, hq2]
              ring
            have hd_diff : (d : ℤ) ∣ (C_val : ℤ) + 1 - ((C_val : ℤ) - 1) := dvd_sub hd_C_add_1 hd_C_sub_1
            have h_ring : (C_val : ℤ) + 1 - ((C_val : ℤ) - 1) = 2 := by ring
            rw [h_ring] at hd_diff
            exact hd_diff
        have hd_2_nat : d ∣ 2 := Int.ofNat_dvd.mp hd_C
        have hd_odd : d % 2 = 1 := by
          have h_even_Bkp1 : B (k + 2) % 2 = 0 := B_even (k + 2)
          have h_odd_Bkp1 : (B (k + 2) - 1) % 2 = 1 := by omega
          exact odd_of_dvd_odd hd2 h_odd_Bkp1
        rcases Nat.dvd_prime Nat.prime_two |>.mp hd_2_nat with hd_1 | hd_2
        · exact hd_1
        · subst hd_2
          omega
