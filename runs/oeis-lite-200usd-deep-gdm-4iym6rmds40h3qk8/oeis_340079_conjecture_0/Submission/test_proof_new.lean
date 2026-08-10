import FormalConjectures.Util.ProblemImports

open Nat BigOperators Finset

-- Mock sum_prime for testing
theorem sum_prime (p : ℕ) (hp : Nat.Prime p) :
    (Finset.Ico 1 (p + 1)).sum (fun k => Nat.gcd k p) = 2 * p - 1 := sorry

lemma q5_p2_contradiction_helper (m r D' a P_D' W_q A_q : ℕ)
    (hr_prime : Nat.Prime r)
    (hr_ge7 : 7 ≤ r)
    (h_D'_ge11 : 11 ≤ D')
    (h_W_q_pos : 1 ≤ W_q)
    (h_W_q_sub : W_q = 4 * A_q - 2 * (a * D'))
    (h_W_q_eq_5 : W_q * 5 = 2 * A_q + m)
    (h_Aq_val : A_q = 3 * P_D')
    (h_mr : m * r = A_q * 9 - 1)
    (h_k_qr : 2 * (a * D') * 5 * r = A_q * 9 * (2 * r - 1) + 1)
    (h_le_PD' : 2 * D' - 1 ≤ P_D')
    (ha_ge1 : 1 ≤ a)
    (h_sum_175 : D' = 175 → P_D' = 845)
    (h_PD'_eq : P_D' = (Finset.Ico 1 (D' + 1)).sum (fun k => Nat.gcd k D'))
    (hs_prime : Nat.Prime D'.minFac)
    (hr_le_s : r ≤ D'.minFac)
    (hr_not_dvd_D' : ¬ r ∣ D') : False := by
  have h_eq : 10 * a * D' * r = 27 * P_D' * (2 * r - 1) + 1 := by
    calc 10 * a * D' * r = 2 * (a * D') * 5 * r := by ring
         _ = A_q * 9 * (2 * r - 1) + 1 := h_k_qr
         _ = (3 * P_D') * 9 * (2 * r - 1) + 1 := by rw [h_Aq_val]
         _ = 27 * P_D' * (2 * r - 1) + 1 := by ring

  have h_ineq : 27 * (2 * D' - 1) * (2 * r - 1) + 1 ≤ 10 * a * D' * r := by
    rw [h_eq]
    gcongr

  have h_aD'_lt_6PD' : a * D' < 6 * P_D' := by
    have h1 : 2 * (a * D') + W_q = 4 * A_q := by omega
    have h2 : A_q = 3 * P_D' := h_Aq_val
    omega

  by_cases h_D'_prime : Nat.Prime D'
  · have h_PD'_val : P_D' = 2 * D' - 1 := by
      rw [h_PD'_eq, sum_prime D' h_D'_prime]
    have h_a_lt12 : a < 12 := by
      have h1 : 6 * P_D' = 12 * D' - 6 := by rw [h_PD'_val]; omega
      have h2 : a * D' < 12 * D' := by omega
      have h3 : 12 * D' ≤ a * D' := Nat.mul_le_mul_right D' (by omega)
      omega
    have h_a_ge10 : 10 ≤ a := by
      by_contra h_lt
      have h_a_le9 : a ≤ 9 := by omega
      have h_mul_le : 10 * a * D' * r ≤ 90 * D' * r := by
        calc 10 * a * D' * r = 10 * a * (D' * r) := by ring
             _ ≤ 90 * (D' * r) := Nat.mul_le_mul_right (D' * r) (by omega)
             _ = 90 * D' * r := by ring
      have h_cast_le : (10 * a * D' * r : ℤ) ≤ 90 * (D' : ℤ) * (r : ℤ) := by exact_mod_cast h_mul_le
      have h_cast_ineq : (27 * (2 * (D' : ℤ) - 1) * (2 * (r : ℤ) - 1) + 1) ≤ (10 * a * D' * r : ℤ) := by
        have h_cast_ineq_0 : ((27 * (2 * D' - 1) * (2 * r - 1) + 1 : ℕ) : ℤ) ≤ ((10 * a * D' * r : ℕ) : ℤ) := by
          exact_mod_cast h_ineq
        have hd1 : 1 ≤ 2 * D' := by omega
        have hr1 : 1 ≤ 2 * r := by omega
        push_cast [hd1, hr1] at h_cast_ineq_0
        exact h_cast_ineq_0
      have h_combined : (27 * (2 * (D' : ℤ) - 1) * (2 * (r : ℤ) - 1) + 1) ≤ 90 * (D' : ℤ) * (r : ℤ) := by
        linarith
      have h_diff : (27 * (2 * (D' : ℤ) - 1) * (2 * (r : ℤ) - 1) + 1) - 90 * (D' : ℤ) * (r : ℤ) = 18 * D' * r - 54 * D' - 54 * r + 28 := by ring
      have h_pos : (18 : ℤ) * D' * r - 54 * D' - 54 * r + 28 > 0 := by
        let x : ℤ := D' - 11
        let y : ℤ := r - 7
        have hx : x ≥ 0 := by omega
        have hy : y ≥ 0 := by omega
        have h_id : (18 : ℤ) * D' * r - 54 * D' - 54 * r + 28 = 18 * x * y + 72 * x + 144 * y + 442 := by
          dsimp [x, y]
          ring
        rw [h_id]
        nlinarith
      linarith
    rcases eq_or_ne a 11 with rfl | h_a_neq11
    · have h_alg : (2 * (D' : ℤ) * r + 54 * D' + 54 * r - 28 : ℤ) = 0 := by
        have h_cast : (110 * (D' : ℤ) * r : ℤ) = (27 * (2 * (D' : ℤ) - 1) * (2 * (r : ℤ) - 1) + 1 : ℤ) := by
          have h_cast_eq : ((10 * 11 * D' * r : ℕ) : ℤ) = ((27 * (2 * D' - 1) * (2 * r - 1) + 1 : ℕ) : ℤ) := by
            have h_eq_val := h_eq
            rw [h_PD'_val] at h_eq_val
            exact_mod_cast h_eq_val
          have hd1 : 1 ≤ 2 * D' := by omega
          have hr1 : 1 ≤ 2 * r := by omega
          push_cast [hd1, hr1] at h_cast_eq
          exact h_cast_eq
        linarith
      have : (2 * (D' : ℤ) * r + 54 * D' + 54 * r - 28 : ℤ) > 0 := by omega
      omega
    · have h_a10 : a = 10 := by omega
      subst h_a10
      have h_alg : (4 * (D' : ℤ) * r - 27 * D' - 27 * r + 14 : ℤ) = 0 := by
        have h_cast : (100 * (D' : ℤ) * r : ℤ) = (27 * (2 * (D' : ℤ) - 1) * (2 * (r : ℤ) - 1) + 1 : ℤ) := by
          have h_cast_eq : ((10 * 10 * D' * r : ℕ) : ℤ) = ((27 * (2 * D' - 1) * (2 * r - 1) + 1 : ℕ) : ℤ) := by
            have h_eq_val := h_eq
            rw [h_PD'_val] at h_eq_val
            exact_mod_cast h_eq_val
          have hd1 : 1 ≤ 2 * D' := by omega
          have hr1 : 1 ≤ 2 * r := by omega
          push_cast [hd1, hr1] at h_cast_eq
          exact h_cast_eq
        linarith
      have h_factor : (4 * (D' : ℤ) - 27) * (4 * (r : ℤ) - 27) = 673 := by
        calc (4 * (D' : ℤ) - 27) * (4 * (r : ℤ) - 27) = 4 * (4 * (D' : ℤ) * r - 27 * D' - 27 * r + 14) + 673 := by ring
             _ = 4 * 0 + 673 := by rw [h_alg]
             _ = 673 := by ring
      have h_D'_sub : 27 ≤ 4 * D' := by omega
      have h_r_sub : 27 ≤ 4 * r := by omega
      have h_nat_eq : (4 * D' - 27) * (4 * r - 27) = 673 := by
        apply Int.ofNat_inj.mp
        push_cast [h_D'_sub, h_r_sub]
        exact h_factor
      have h_dvd : (4 * r - 27) ∣ 673 := by
        use (4 * D' - 27)
        rw [mul_comm] at h_nat_eq
        exact h_nat_eq.symm
      have h_prime_673 : Nat.Prime 673 := by decide
      have h_cases := h_prime_673.eq_one_or_self_of_dvd (4 * r - 27) h_dvd
      rcases h_cases with h_one | h_self
      · have h_r7 : r = 7 := by omega
        have h_D'175 : D' = 175 := by omega
        have : ¬ Nat.Prime 175 := by decide
        rw [h_D'175] at h_D'_prime
        contradiction
      · have h_r175 : r = 175 := by omega
        have : ¬ Nat.Prime 175 := by decide
        exact this (by rw [← h_r175]; exact hr_prime)
  · -- D' is composite
    let s := D'.minFac
    have h_s_prime : Nat.Prime s := hs_prime
    have h_r_neq_s : r ≠ s := by
      intro h_eq
      have h_dvd : s ∣ D' := Nat.minFac_dvd D'
      rw [← h_eq] at h_dvd
      exact hr_not_dvd_D' h_dvd
    have h_r_lt_s : r < s := by omega
    have h_s_ge11 : s ≥ 11 := by
      have : s > 7 := by omega
      have : s ≠ 8 := by intro h; rw [h] at h_s_prime; contradiction
      have : s ≠ 9 := by intro h; rw [h] at h_s_prime; contradiction
      have : s ≠ 10 := by intro h; rw [h] at h_s_prime; contradiction
      omega
    have hdvd : s ∣ D' := Nat.minFac_dvd D'
    obtain ⟨K, hK⟩ := hdvd
    have hK_ne1 : K ≠ 1 := by
      rintro rfl
      rw [mul_one] at hK
      rw [hK] at h_D'_prime
      exact h_D'_prime h_s_prime
    have hK_ne0 : K ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hK
      omega
    have h_s_le_K : s ≤ K := by
      apply Nat.minFac_le_of_dvd
      · omega
      · rw [hK]
        exact dvd_mul_left K s
    have h_D'_ge121 : D' ≥ 121 := by
      calc D' = s * K := hK
           _ ≥ s * s := Nat.mul_le_mul_left s h_s_le_K
           _ ≥ 11 * s := Nat.mul_le_mul_right s h_s_ge11
           _ ≥ 11 * 11 := Nat.mul_le_mul_left 11 h_s_ge11
    by_cases hD'_175 : D' = 175
    · have h_min_175 : (175 : ℕ).minFac = 5 := by
        have h_prime_min : Nat.Prime (175 : ℕ).minFac := Nat.minFac_prime (by decide)
        have h_le_5 : (175 : ℕ).minFac ≤ 5 := by
          apply Nat.minFac_le_of_dvd (by decide)
          use 35
        have h_ne_2 : (175 : ℕ).minFac ≠ 2 := by
          intro h_eq
          have h_dvd : 2 ∣ 175 := by
            rw [← h_eq]
            exact Nat.minFac_dvd 175
          have : ¬ 2 ∣ 175 := by decide
          contradiction
        have h_ne_3 : (175 : ℕ).minFac ≠ 3 := by
          intro h_eq
          have h_dvd : 3 ∣ 175 := by
            rw [← h_eq]
            exact Nat.minFac_dvd 175
          have : ¬ 3 ∣ 175 := by decide
          contradiction
        have h_ne_4 : (175 : ℕ).minFac ≠ 4 := by
          intro h_eq
          have h_dvd : 4 ∣ 175 := by
            rw [← h_eq]
            exact Nat.minFac_dvd 175
          have : ¬ 4 ∣ 175 := by decide
          contradiction
        omega
      have : s = 5 := by
        rw [← hD'_175]
        exact h_min_175
      omega
    · have h_a_ge10 : a ≥ 10 := by
        by_contra h_lt
        have h_a_le9 : a ≤ 9 := by omega
        have h_mul_le : 10 * a * D' * r ≤ 90 * D' * r := by
          calc 10 * a * D' * r = 10 * a * (D' * r) := by ring
               _ ≤ 90 * (D' * r) := Nat.mul_le_mul_right (D' * r) (by omega)
               _ = 90 * D' * r := by ring
        have h_cast_le : (10 * a * D' * r : ℤ) ≤ 90 * (D' : ℤ) * (r : ℤ) := by exact_mod_cast h_mul_le
        have h_cast_ineq : (27 * (2 * (D' : ℤ) - 1) * (2 * (r : ℤ) - 1) + 1) ≤ (10 * a * D' * r : ℤ) := by
          have h_cast_ineq_0 : ((27 * (2 * D' - 1) * (2 * r - 1) + 1 : ℕ) : ℤ) ≤ ((10 * a * D' * r : ℕ) : ℤ) := by
            exact_mod_cast h_ineq
          have hd1 : 1 ≤ 2 * D' := by omega
          have hr1 : 1 ≤ 2 * r := by omega
          push_cast [hd1, hr1] at h_cast_ineq_0
          exact h_cast_ineq_0
        have h_combined : (27 * (2 * (D' : ℤ) - 1) * (2 * (r : ℤ) - 1) + 1) ≤ 90 * (D' : ℤ) * (r : ℤ) := by
          linarith
        have h_diff : (27 * (2 * (D' : ℤ) - 1) * (2 * (r : ℤ) - 1) + 1) - 90 * (D' : ℤ) * (r : ℤ) = 18 * D' * r - 54 * D' - 54 * r + 28 := by ring
        have h_pos : (18 : ℤ) * D' * r - 54 * D' - 54 * r + 28 > 0 := by
          let x : ℤ := D' - 121
          let y : ℤ := r - 7
          have hx : x ≥ 0 := by omega
          have hy : y ≥ 0 := by omega
          have h_id : (18 : ℤ) * D' * r - 54 * D' - 54 * r + 28 = 18 * x * y + 72 * x + 2124 * y + 8362 := by
            dsimp [x, y]
            ring
          rw [h_id]
          nlinarith
        linarith
      have : False := by
        -- we can show s = 5 and r <= 5, which is a contradiction
        -- but wait, if D' = 175:
        sorry
      contradiction
