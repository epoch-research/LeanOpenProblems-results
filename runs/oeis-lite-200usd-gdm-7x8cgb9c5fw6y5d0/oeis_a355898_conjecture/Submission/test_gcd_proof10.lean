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
  | zero => simp [B, B0]
  | succ m ih =>
    cases m with
    | zero => simp [B, B1]
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

theorem gcd_step2 (k : ℕ) (hk : 1 ≤ k) :
  Nat.gcd (B (k + 1) - 1) (B k) = Nat.gcd (B k) (B (k - 1) - 1) := by
  have h_sub : B (k + 1) - 1 = B k + (B (k - 1) - 1) := by
    have h_rec : B (k + 1) = B k + B (k - 1) := by
      obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      subst hm
      rfl
    have : 1 ≤ B (k - 1) := B_pos (k - 1)
    omega
  rw [h_sub]
  rw [Nat.gcd_comm (B k + (B (k - 1) - 1)) (B k)]
  rw [add_comm (B k) (B (k - 1) - 1)]
  rw [Nat.gcd_add_self_right]

theorem G_relation (k : ℕ) (hk : 1 ≤ k) :
  Nat.gcd (B (k + 2) - 1) (B (k + 1) - 1) = Nat.gcd (B k) (B (k - 1) - 1) := by
  rw [gcd_step, gcd_step2 k hk]

theorem base_gcd_0 : Nat.gcd (B 1 - 1) (B 0 - 1) = 1 := by decide
theorem base_gcd_1 : Nat.gcd (B 1 - 1) (B 0) = 1 := by decide

lemma B_gcd_div_fib_sub_1 (k : ℕ) (d : ℕ) (hd_Bkp1_sub_1 : (d : ℤ) ∣ (B (k+1) : ℤ) - 1) (hd_Bk_sub_1 : (d : ℤ) ∣ (B k : ℤ) - 1) (j : ℕ) (hj_pos : 1 ≤ j) (hj : j ≤ k) :
  (d : ℤ) ∣ (B (k - j) : ℤ) - (-1 : ℤ)^j * (Nat.fib (j - 1) : ℤ) := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    rcases j with _ | j
    · omega
    · rcases j with _ | j
      · -- j = 1: B (k - 1)
        have h_rec : B (k + 1) = B k + B (k - 1) := by
          have hk : k ≥ 1 := by omega
          obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
          subst hm
          rfl
        have h_rec_z : (B (k + 1) : ℤ) = (B k : ℤ) + (B (k - 1) : ℤ) := by exact_mod_cast h_rec
        have h_sub_1 : (B (k - 1) : ℤ) = ((B (k + 1) : ℤ) - 1) - ((B k : ℤ) - 1) := by omega
        have hd_sub_1 : (d : ℤ) ∣ (B (k - 1) : ℤ) := by
          rw [h_sub_1]
          exact dvd_sub hd_Bkp1_sub_1 hd_Bk_sub_1
        have h_simp : (B (k - 1) : ℤ) - (-1 : ℤ)^1 * (Nat.fib 0 : ℤ) = (B (k - 1) : ℤ) := by simp
        rw [h_simp]
        exact hd_sub_1
      · rcases j with _ | j
        · -- j = 2: B (k - 2) - 1
          have h_rec1 : B (k + 1) = B k + B (k - 1) := by
            have hk : k ≥ 1 := by omega
            obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
            subst hm
            rfl
          have h_rec2 : B k = B (k - 1) + B (k - 2) := by
            have hk : k ≥ 2 := by omega
            obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k - 1 ≠ 0)
            have h_sub : k - 1 = m + 1 := by omega
            have h_orig : k = m + 2 := by omega
            rw [h_orig]
            rfl
          have h_rec1_z : (B (k + 1) : ℤ) = (B k : ℤ) + (B (k - 1) : ℤ) := by exact_mod_cast h_rec1
          have h_rec2_z : (B k : ℤ) = (B (k - 1) : ℤ) + (B (k - 2) : ℤ) := by exact_mod_cast h_rec2
          have h_sub_1 : (B (k - 2) : ℤ) - 1 = ((B k : ℤ) - 1) - (((B (k + 1) : ℤ) - 1) - ((B k : ℤ) - 1)) := by omega
          have hd_sub_1 : (d : ℤ) ∣ (B (k - 2) : ℤ) - 1 := by
            rw [h_sub_1]
            exact dvd_sub hd_Bk_sub_1 (dvd_sub hd_Bkp1_sub_1 hd_Bk_sub_1)
          have h_simp : (B (k - 2) : ℤ) - (-1 : ℤ)^2 * (Nat.fib 1 : ℤ) = (B (k - 2) : ℤ) - 1 := by simp
          rw [h_simp]
          exact hd_sub_1
        · -- j >= 3: j + 3
          have ih1 := ih (j + 1) (by omega) (by omega) (by omega)
          have ih2 := ih (j + 2) (by omega) (by omega) (by omega)
          have h_idx1 : k - (j + 1) = k - 1 - j := by omega
          have h_idx2 : k - (j + 2) = k - 2 - j := by omega
          rw [h_idx1] at ih1
          rw [h_idx2] at ih2
          have h_rec_B : B (k - 1 - j) = B (k - 2 - j) + B (k - 3 - j) := by
            have h1 : k - 1 - j = (k - 3 - j) + 2 := by omega
            have h2 : k - 2 - j = (k - 3 - j) + 1 := by omega
            rw [h1, h2]
            rfl
          have h_rec_B_z : (B (k - 1 - j) : ℤ) = (B (k - 2 - j) : ℤ) + (B (k - 3 - j) : ℤ) := by exact_mod_cast h_rec_B
          have h_fib : Nat.fib (j + 2) = Nat.fib j + Nat.fib (j + 1) := Nat.fib_add_two
          have h_fib_z : (Nat.fib (j + 2) : ℤ) = (Nat.fib j : ℤ) + (Nat.fib (j + 1) : ℤ) := by exact_mod_cast h_fib
          have h_comb : (B (k - 3 - j) : ℤ) - (-1 : ℤ)^(j + 3) * (Nat.fib (j + 2) : ℤ) =
            ((B (k - 1 - j) : ℤ) - (-1 : ℤ)^(j + 1) * (Nat.fib j : ℤ)) -
            ((B (k - 2 - j) : ℤ) - (-1 : ℤ)^(j + 2) * (Nat.fib (j + 1) : ℤ)) := by
            have h_pow1 : (-1 : ℤ)^(j + 3) = -(-1 : ℤ)^j := by rw [pow_add, pow_three]; ring
            have h_pow2 : (-1 : ℤ)^(j + 1) = -(-1 : ℤ)^j := by rw [pow_add, pow_one]; ring
            have h_pow3 : (-1 : ℤ)^(j + 2) = (-1 : ℤ)^j := by rw [pow_add, pow_two]; ring
            rw [h_rec_B_z, h_fib_z, h_pow1, h_pow2, h_pow3]
            ring
          have h_index : k - (j + 3) = k - 3 - j := by omega
          rw [h_index]
          have h_goal_pow : (-1 : ℤ)^(j + 2 + 1) = (-1 : ℤ)^(j + 3) := rfl
          have h_goal_fib : (Nat.fib (j + 2 + 1 - 1) : ℤ) = (Nat.fib (j + 2) : ℤ) := by
            have : j + 2 + 1 - 1 = j + 2 := rfl
            rw [this]
          rw [h_goal_pow, h_goal_fib]
          rw [h_comb]
          exact dvd_sub ih1 ih2

theorem B_gcd (k : ℕ) : Nat.gcd (B (k + 1) - 1) (B k - 1) = 1 := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rcases k with _ | k
    · exact base_gcd_0
    · rcases k with _ | k
      · have h_gcd := gcd_step 0
        rw [h_gcd]
        exact base_gcd_1
      · set d := Nat.gcd (B (k + 3) - 1) (B (k + 2) - 1)
        have hd1 : d ∣ B (k + 3) - 1 := Nat.gcd_dvd_left _ _
        have hd2 : d ∣ B (k + 2) - 1 := Nat.gcd_dvd_right _ _
        have hd1_z : (d : ℤ) ∣ (B (k + 3) : ℤ) - 1 := by
          have h_sub : ((B (k + 3) - 1 : ℕ) : ℤ) = (B (k + 3) : ℤ) - 1 := by
            have : 1 ≤ B (k + 3) := B_pos (k + 3)
            omega
          rw [← h_sub]
          exact Int.ofNat_dvd.mpr hd1
        have hd2_z : (d : ℤ) ∣ (B (k + 2) : ℤ) - 1 := by
          have h_sub : ((B (k + 2) - 1 : ℕ) : ℤ) = (B (k + 2) : ℤ) - 1 := by
            have : 1 ≤ B (k + 2) := B_pos (k + 2)
            omega
          rw [← h_sub]
          exact Int.ofNat_dvd.mpr hd2
        have h_div_j_2 := B_gcd_div_fib_sub_1 (k + 2) d hd1_z hd2_z 2 (by omega) (by omega)
        have h_sub_j_2 : k + 2 - 2 = k := by omega
        have h_fib_1_eq : (Nat.fib 1 : ℤ) = 1 := rfl
        have h_pow_2 : (-1 : ℤ)^2 = 1 := rfl
        rw [h_sub_j_2, h_fib_1_eq, h_pow_2] at h_div_j_2
        simp only [mul_one] at h_div_j_2
        have hd_Bk_sub_1 : d ∣ B k - 1 := by
          have h_sub : ((B k - 1 : ℕ) : ℤ) = (B k : ℤ) - 1 := by
            have : 1 ≤ B k := B_pos k
            omega
          rw [← h_sub] at h_div_j_2
          exact Int.ofNat_dvd.mp h_div_j_2
        have hd_Bk_sub_1_z : (d : ℤ) ∣ (B k : ℤ) - 1 := Int.ofNat_dvd.mpr hd_Bk_sub_1
        have h_gcd_eq := G_relation (k + 1) (by omega)
        have hd_Bkp1 : d ∣ B (k + 1) := by
          have hd_gcd_G : d ∣ Nat.gcd (B (k + 3) - 1) (B (k + 2) - 1) := by exact dvd_refl d
          rw [h_gcd_eq] at hd_gcd_G
          exact Nat.dvd_trans hd_gcd_G (Nat.gcd_dvd_left _ _)
        obtain ⟨q2, hq2⟩ := hd1_z
        obtain ⟨q1, hq1⟩ := hd2_z
        obtain ⟨q3, hq3⟩ := hd_Bkp1
        obtain ⟨q4, hq4⟩ := hd_Bk_sub_1_z
        have h_rec_3 : (B (k + 3) : ℤ) = (B (k + 2) : ℤ) + (B (k + 1) : ℤ) := by
          have : B (k + 3) = B (k + 2) + B (k + 1) := rfl
          exact_mod_cast this
        have h_rec_2 : (B (k + 2) : ℤ) = (B (k + 1) : ℤ) + (B k : ℤ) := by
          have : B (k + 2) = B (k + 1) + B k := rfl
          exact_mod_cast this
        have hd_one_z : (d : ℤ) ∣ 1 := by
          use q1 - q3 - q4
          -- C_val check: B (k + 2) = d * q1 + 1. B (k + 1) = d * q3. B k = d * q4 + 1.
          -- So d * q1 + 1 = d * q3 + d * q4 + 1 -> d * (q1 - q3 - q4) = 0? No!
          -- Let's check:
          -- B (k+2) = B (k+1) + B k
          -- LHS: d * q1 + 1
          -- RHS: d * q3 + (d * q4 + 1) = d * (q3 + q4) + 1
          -- So d * q1 + 1 = d * (q3 + q4) + 1
          -- d * (q1 - q3 - q4) = 0.
          -- Wait! This only gives q1 - q3 - q4 = 0. It doesn't give d | 1.
          sorry
        sorry
