import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 200000

open Nat

def A355898_loop : ℕ → ℕ → ℕ → ℕ × ℕ
| 0, a, b => (a, b)
| n + 1, a, b =>
  let g := Nat.gcd b a
  A355898_loop n b (g + (b + a) / g)

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

theorem base_gcd_0 : Nat.gcd (B 1 - 1) (B 0 - 1) = 1 := by
  unfold B B0 B1
  decide

theorem base_gcd_1 : Nat.gcd (B 1 - 1) (B 0) = 1 := by
  unfold B B0 B1
  decide

theorem base_gcd_2 : Nat.gcd (B 1) (B 0 - 1) = 1 := by
  unfold B B0 B1
  decide

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

lemma cassini_div_2_even (d q1 q2 C : ℤ)
  (h_cassini : (d * q1 + 1)^2 = (d * (q1 + q2) + 2) * (d * q2 + 1) + C) :
  ∃ k : ℤ, C + 1 = d * k := by
  have h_C : C = (d * q1 + 1)^2 - (d * (q1 + q2) + 2) * (d * q2 + 1) := by
    rw [h_cassini]
    ring
  rw [h_C]
  use q1^2 * d + 2 * q1 - (q1 + q2) * q2 * d - (q1 + q2) - 2 * q2
  ring

lemma cassini_div_2_odd (d q1 q2 C : ℤ)
  (h_cassini : (d * (q1 + q2) + 2) * (d * q2 + 1) = (d * q1 + 1)^2 + C) :
  ∃ k : ℤ, C - 1 = d * k := by
  have h_C : C = (d * (q1 + q2) + 2) * (d * q2 + 1) - (d * q1 + 1)^2 := by
    rw [h_cassini]
    ring
  rw [h_C]
  use (q1 + q2) * q2 * d + (q1 + q2) + 2 * q2 - q1^2 * d - 2 * q1
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
      · -- Case k >= 2 (since k + 2)
        -- We want to prove Nat.gcd (B (k + 3) - 1) (B (k + 2) - 1) = 1
        -- By ih at k+1: Nat.gcd (B (k + 2) - 1) (B (k + 1) - 1) = 1
        -- By ih at k: Nat.gcd (B (k + 1) - 1) (B k - 1) = 1
        -- By ih at k-1: Nat.gcd (B k - 1) (B (k - 1) - 1) = 1
        have ih_kp1 := ih (k + 1) (by omega)
        have ih_k := ih k (by omega)
        have ih_km1 := ih (k - 1) (by omega)
        -- We define d:
        set d := Nat.gcd (B (k + 3) - 1) (B (k + 2) - 1)
        have hd1 : d ∣ B (k + 3) - 1 := Nat.gcd_dvd_left _ _
        have hd2 : d ∣ B (k + 2) - 1 := Nat.gcd_dvd_right _ _
        -- We show d ∣ B (k+1):
        have hd_Bkp1 : d ∣ B (k + 1) := by
          have hd_eq : d = Nat.gcd (B (k + 2) - 1) (B (k + 1)) := by
            rw [gcd_step (k + 1)]
          rw [hd_eq]
          exact Nat.gcd_dvd_right _ _
        -- We cast to Int:
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
        -- B(k+2) = d * q1 + 1
        -- B(k+3) = d * q2 + 1
        -- So B(k+1) = B(k+3) - B(k+2) = d * (q2 - q1).
        -- We also can get q3 such that B(k+1) = d * q3:
        obtain ⟨q3, hq3⟩ := hd_Bkp1
        have hBkp1_z : (B (k + 1) : ℤ) = d * q3 := by exact_mod_cast hq3
        have hBkp2_z : (B (k + 2) : ℤ) = d * q1 + 1 := by omega
        -- B(k) = B(k+2) - B(k+1) = d * q1 + 1 - d * q3 = d * (q1 - q3) + 1.
        have hBk_z : (B k : ℤ) = d * (q1 - q3) + 1 := by
          have : B (k + 2) = B (k + 1) + B k := rfl
          omega
        -- So d ∣ B k - 1 !
        have hd_B_sub_1 : (d : ℤ) ∣ (B k : ℤ) - 1 := by
          use q1 - q3
          omega
        have hd_Bkm1_nat : d ∣ B k - 1 := by
          have h_cast : (B k : ℤ) - 1 = ((B k - 1 : ℕ) : ℤ) := by omega
          rw [h_cast] at hd_B_sub_1
          exact Int.ofNat_dvd.mp hd_B_sub_1
        -- Now we use Cassini to prove (d : ℤ) ∣ C_val - 1 or C_val + 1 first:
        have h_cass := Cassini (k)
        by_cases h_even : Even (k + 1)
        · have h_odd : Odd k := by
            rcases h_even with ⟨r, hr⟩
            have : r ≠ 0 := by omega
            use r - 1
            omega
          have h_cass_odd := h_cass.2 h_odd
          have h_cast : ((B (k + 2) * B k) : ℤ) = ((B (k + 1)^2 + C_val) : ℤ) := by rw [h_cass_odd]
          push_cast at h_cast
          have h_C : (C_val : ℤ) - 1 = (B (k + 2) : ℤ) * (B k : ℤ) - (B (k + 1) : ℤ)^2 - 1 := by
            rw [h_cast]
            ring
          obtain ⟨k_z, hk_z⟩ : ∃ k_z, (C_val : ℤ) - 1 = d * k_z := by
            use q1 * (q1 - q3) * d + q1 + (q1 - q3) - q3^2 * d
            rw [h_C, hBkp2_z, hBk_z, hBkp1_z]
            ring
          -- Since d ∣ C_val - 1, we show d ∣ B(k-1):
          -- Cassini at step k-1 (since k-1 is even):
          -- B k^2 = B (k+1) * B (k-1) + C_val
          -- B (k+1) * B (k-1) = B k^2 - C_val
          have h_cass_km1 := Cassini (k - 1)
          have h_even_km1 : Even (k - 1) := by
            rcases h_even with ⟨r, hr⟩
            have : r ≠ 0 := by omega
            use r - 1
            omega
          have h_cass_even := h_cass_km1.1 h_even_km1
          have h_cast2 : ((B k^2) : ℤ) = ((B (k + 1) * B (k - 1) + C_val) : ℤ) := by rw [h_cass_even]
          push_cast at h_cast2
          have h_B_prod : (B (k + 1) : ℤ) * (B (k - 1) : ℤ) = (B k : ℤ)^2 - (C_val : ℤ) := by
            rw [h_cast2]
            ring
          have h_d_Bkm1 : (d : ℤ) ∣ (B (k - 1) : ℤ) := by
            -- (d * q3) * B (k-1) = (d * (q1 - q3) + 1)^2 - C_val
            -- = d * [ d * (q1 - q3)^2 + 2 * (q1 - q3) - k_z ]
            -- since C_val = d * k_z + 1
            -- So if q3 is positive?
            -- Wait! Since d ∣ (B(k+1) * B(k-1)), is B(k+1) * B(k-1) a multiple of d?
            -- We can show d * q3 * B(k-1) = d * (...)
            -- So d * (q3 * B(k-1) - ...) = 0.
            -- Since d >= 1, we can cancel d!
            -- Or even simpler, we can write:
            -- B (k+1) * B (k-1) is a multiple of d^2? No, but we can write:
            -- B (k-1) = (B k^2 - C_val) / B (k+1)
            -- Wait! Since B (k-1) = B (k+1) - B k.
            -- So (B (k-1) : ℤ) = d * q3 - (d * (q1 - q3) + 1) = d * (2 * q3 - q1) - 1.
            -- This is congruent to -1 mod d, so it is NOT a multiple of d!
            -- Wait!
            -- If B(k-1) is NOT a multiple of d, then (B(k-1) : ℤ) % d = d - 1.
            -- But we wanted d ∣ B(k-1) ?
            -- Ah!
            -- Let's check:
            -- If d = gcd(B(k+3)-1, B(k+2)-1).
            -- We showed:
            -- B(k+2) = d * q1 + 1.
            -- B(k+3) = d * q2 + 1.
            -- So B(k+1) = B(k+3) - B(k+2) = d * (q2 - q1).
            -- So d ∣ B(k+1) !!!
            -- Yes! This is what we proved: hd_Bkp1 : d ∣ B (k+1).
            -- And we also have:
            -- B(k) = B(k+2) - B(k+1) = (d * q1 + 1) - d * (q2 - q1) = d * (2 * q1 - q2) + 1.
            -- So d ∣ B(k) - 1 !
            -- Yes! This is what we proved: hd_Bkm1_nat : d ∣ B k - 1.
            -- And:
            -- B(k-1) = B(k+1) - B(k) = d * (q2 - q1) - (d * (2 * q1 - q2) + 1) = d * (2 * q2 - 3 * q1) - 1.
            -- So B(k-1) + 1 is a multiple of d!
            -- So d ∣ B(k-1)+1 !
            -- Yes, this is what we proved on line 231!
            -- And:
            -- B(k-2) = B(k) - B(k-1) = (d * (2 * q1 - q2) + 1) - (d * (2 * q2 - 3 * q1) - 1) = d * (5 * q1 - 3 * q2) + 2.
            -- So B(k-2) - 2 is a multiple of d!
            -- So d ∣ B(k-2)-2 !
            -- And so on!
            -- So d does NOT divide B(k-1) !
            -- Ah!!!
            -- d divides B(k-1)+1, not B(k-1)!
            -- And d divides B(k-2)-2, not B(k-2)-1!
            -- Indeed!
            -- So we cannot use d ∣ B(k-1).
            -- But wait!
            -- Since d ∣ B(k+1) and d ∣ B(k)-1:
            -- So d is a common divisor of B(k+1) and B(k)-1.
            -- So d ∣ Nat.gcd (B (k+1)) (B k - 1).
            -- But we know Nat.gcd (B (k+1)) (B k - 1) is a divisor of...
            -- Wait!
            -- Let's check `ih_kp1` and `ih_k` and `ih_km1`!
            -- `ih_kp1` is Nat.gcd (B (k + 2) - 1) (B (k + 1) - 1) = 1.
            -- But d = Nat.gcd (B (k + 3) - 1) (B (k + 2) - 1) !
            -- Oh!!!
            -- We want to prove d = 1 !
            -- But we have hd_eq : d = Nat.gcd (B (k + 2) - 1) (B (k + 1)).
            -- Is Nat.gcd (B (k + 2) - 1) (B (k + 1)) equal to 1?
            -- Wait!
            -- By `ih_kp1`, we have Nat.gcd (B (k+2)-1) (B (k+1)-1) = 1.
            -- But here we have B(k+1) instead of B(k+1)-1.
            -- But we also have:
            -- Nat.gcd (B (k+2)-1) (B (k+1)) = Nat.gcd (B (k+1)) (B k - 1) by gcd_step2 (k+1).
            -- So d = Nat.gcd (B (k+1)) (B k - 1).
            -- Is Nat.gcd (B (k+1)) (B k - 1) equal to 1?
            -- Wait!
            -- Since B(k+1) = B(k) + B(k-1).
            -- So Nat.gcd (B (k+1)) (B k - 1) = Nat.gcd (B k + B (k-1)) (B k - 1).
            -- Since B(k) ≡ 1 (mod B(k)-1):
            -- B k + B (k-1) ≡ 1 + B (k-1) = B (k-1) + 1.
            -- So Nat.gcd (B (k+1)) (B k - 1) = Nat.gcd (B (k-1) + 1) (B k - 1).
            -- Now, what is B(k) - 1?
            -- B(k) - 1 = B(k-1) + B(k-2) - 1 = (B(k-1)+1) + B(k-2) - 2.
            -- So Nat.gcd (B (k-1) + 1) (B k - 1) = Nat.gcd (B (k-1) + 1) (B (k-2) - 2).
            -- And so on!
            -- This is the reduction we saw earlier!
            -- But wait!
            -- Can we just prove that:
            -- Nat.gcd (B (k + 1)) (B k - 1) = 1
            -- by showing:
            -- Nat.gcd (B (k + 1)) (B k - 1) ∣ 2 ?
            -- Yes!
            -- Let's prove:
            -- lemma gcd_g3_div_2 (k : ℕ) : Nat.gcd (B (k + 1)) (B k - 1) ∣ 2
            -- from this:
            -- Modulo d, we showed C_val - 1 ≡ 0 (mod d) or C_val + 1 ≡ 0 (mod d).
            -- And we also showed:
            -- B (k+1) ≡ 0.
            -- B(k) ≡ 1.
            -- B(k-1) ≡ -1.
            -- B(k-2) ≡ 2.
            -- B(k-3) ≡ -3.
            -- B(k-4) ≡ 5.
            -- B(k-j) ≡ (-1)^j F_{j+1}.
            -- So B(1) ≡ (-1)^k F_{k+1}.
            -- B(0) ≡ (-1)^{k+1} F_{k+2}.
            -- And since B(k+1) ≡ 0:
            -- B(1) F_k + B(0) F_{k-1} ≡ 0 => F_k F_{k+1} - F_{k-1} F_{k+2} ≡ 0.
            -- But F_k F_{k+1} - F_{k-1} F_{k+2} = (-1)^{k-1}!
            -- So (-1)^{k-1} ≡ 0 (mod d) => d ∣ 1 => d = 1!!!
            -- Oh my god!!!
            -- This is 100% correct and doesn't need C_val at all!
            -- Let's prove:
            -- (d : ℤ) ∣ 1
            -- directly from B(1) and B(0) modulo d!
            -- Yes!
            -- Let's write down this proof! It is 100% algebraic and ring can do it!
            sorry
        -- End of Even k+1 case
        sorry
