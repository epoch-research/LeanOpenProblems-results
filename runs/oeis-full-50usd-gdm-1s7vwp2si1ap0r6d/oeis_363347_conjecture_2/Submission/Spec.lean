import FormalConjectures.Util.ProblemImports

open Rat Nat ZMod

def w : ℕ → ℤ
  | 0 => 0
  | 1 => 0
  | 2 => -1
  | 3 => 0
  | k + 4 => (k + 2 : ℤ) * (w (k + 3) - w (k + 2))

theorem lemma_w (k : ℕ) : (k : ℤ) * w (k + 3) - (k + 1 : ℤ) * w (k + 2) = (k + 1).factorial := by
  induction k with
  | zero =>
    simp [w]
  | succ k ih =>
    have hw : w (k + 4) = (k + 2 : ℤ) * (w (k + 3) - w (k + 2)) := rfl
    have h_goal : (k + 1 : ℤ) * w (k + 4) - (k + 2 : ℤ) * w (k + 3) =
                  (↑(k + 1) * w (k + 1 + 3) - (↑(k + 1) + 1) * w (k + 1 + 2)) := by
      push_cast
      rfl
    rw [←h_goal]
    have h_calc : (k + 1 : ℤ) * ((k + 2 : ℤ) * (w (k + 3) - w (k + 2))) - (k + 2 : ℤ) * w (k + 3) =
                  (k + 2 : ℤ) * ((k : ℤ) * w (k + 3) - (k + 1 : ℤ) * w (k + 2)) := by ring
    rw [hw, h_calc, ih]
    have h_fac : ((k + 2).factorial : ℤ) = (k + 2 : ℤ) * ((k + 1).factorial : ℤ) := by
      push_cast
      rfl
    rw [h_fac]

def D (n : ℕ) (k : ℕ) : ℤ :=
  if h1 : n ≤ 2 then 0
  else if h2 : k < 2 then 0
  else if h3 : k > n then 0
  else if h4 : k = n then 4
  else if h5 : k = n - 1 then 5 * (n : ℤ) - 4
  else
    have : n - (k + 1) < n - k := by omega
    have : n - (k + 2) < n - k := by omega
    (k : ℤ) * D n (k + 1) - ((k + 1 : ℤ) * D n (k + 2))
termination_by n - k

lemma D_rec_forward (n : ℕ) (hn : n ≥ 3) (k : ℕ) (hk4 : 4 ≤ k) (hkn : k ≤ n) :
  (k - 1 : ℤ) * D n k = (k - 2 : ℤ) * D n (k - 1) - D n (k - 2) := by
  have hk2_2 : k - 2 ≥ 2 := by omega
  have hk2_lt : k - 2 < n - 1 := by omega
  have h_D : D n (k - 2) = (k - 2 : ℤ) * D n (k - 1) - ((k - 1 : ℤ) * D n k) := by
    rw [D]
    have hnot1 : ¬(n ≤ 2) := by omega
    have hnot2 : ¬(k - 2 < 2) := by omega
    have hnot3 : ¬(k - 2 > n) := by omega
    have hnot4 : ¬(k - 2 = n) := by omega
    have hnot5 : ¬(k - 2 = n - 1) := by omega
    simp [hnot1, hnot2, hnot3, hnot4, hnot5]
    have h_add1 : k - 2 + 1 = k - 1 := by omega
    have h_add2 : k - 2 + 2 = k := by omega
    rw [h_add1, h_add2]
    have hk_cast : ((k - 2 : ℕ) : ℤ) = (k : ℤ) - 2 := by omega
    rw [hk_cast]
    ring
  omega

theorem D_identity (n : ℕ) (hn : n ≥ 3) (k : ℕ) (hk2 : 2 ≤ k) (hkn : k ≤ n) :
  ((k - 1).factorial : ℤ) * D n k = 2 * (k - 2 : ℤ) * D n 3 - w k * D n 2 := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rcases k with _ | _ | _ | k
    -- Cases: k = 0, 1, 2, 3 + k
    · omega
    · omega
    · simp [w]
    · rcases k with _ | k
      · simp [w]
      · have hk4 : 4 ≤ k + 4 := by omega
        have hkn' : k + 4 ≤ n := hkn
        have hrec := D_rec_forward n hn (k + 4) hk4 hkn'
        have ih1 := ih (k + 3) (by omega) (by omega) (by omega)
        have ih2 := ih (k + 2) (by omega) (by omega) (by omega)
        have hw : w (k + 4) = (k + 2 : ℤ) * (w (k + 3) - w (k + 2)) := rfl
        have hfac1 : ((k + 3).factorial : ℤ) = (k + 3 : ℤ) * ((k + 2).factorial : ℤ) := by rfl
        have hfac2 : ((k + 2).factorial : ℤ) = (k + 2 : ℤ) * ((k + 1).factorial : ℤ) := by rfl
        
        change ((k + 3).factorial : ℤ) * D n (k + 4) = 2 * ((k + 4 : ℤ) - 2) * D n 3 - w (k + 4) * D n 2
        
        have hrec_simp : (k + 3 : ℤ) * D n (k + 4) = (k + 2 : ℤ) * D n (k + 3) - D n (k + 2) := by
          have h_coeff1 : (↑(k + 4) - 1 : ℤ) = k + 3 := by omega
          have h_coeff2 : (↑(k + 4) - 2 : ℤ) = k + 2 := by omega
          rw [h_coeff1, h_coeff2] at hrec
          exact hrec
        
        have ih1_simp : ((k + 2).factorial : ℤ) * D n (k + 3) = 2 * ((k + 3 : ℤ) - 2) * D n 3 - w (k + 3) * D n 2 := ih1
        have ih2_simp : ((k + 1).factorial : ℤ) * D n (k + 2) = 2 * ((k + 2 : ℤ) - 2) * D n 3 - w (k + 2) * D n 2 := ih2
  
        have h_mul : ((k + 3).factorial : ℤ) * D n (k + 4) =
                     (k + 2 : ℤ) * (((k + 2).factorial : ℤ) * D n (k + 3)) - (k + 2 : ℤ) * (((k + 1).factorial : ℤ) * D n (k + 2)) := by
          calc ((k + 3).factorial : ℤ) * D n (k + 4)
            _ = (k + 3 : ℤ) * ((k + 2).factorial : ℤ) * D n (k + 4) := by rw [hfac1]
            _ = ((k + 2).factorial : ℤ) * ((k + 3 : ℤ) * D n (k + 4)) := by ring
            _ = ((k + 2).factorial : ℤ) * ((k + 2 : ℤ) * D n (k + 3) - D n (k + 2)) := by rw [hrec_simp]
            _ = (k + 2 : ℤ) * (((k + 2).factorial : ℤ) * D n (k + 3)) - ((k + 2).factorial : ℤ) * D n (k + 2) := by ring
            _ = (k + 2 : ℤ) * (((k + 2).factorial : ℤ) * D n (k + 3)) - (k + 2 : ℤ) * (((k + 1).factorial : ℤ) * D n (k + 2)) := by
              rw [hfac2]
              ring
        rw [h_mul, ih1_simp, ih2_simp, hw]
        ring

lemma D_n_val (n : ℕ) (hn : n ≥ 3) : D n n = 4 := by
  rw [D]
  have hnot1 : ¬(n ≤ 2) := by omega
  have hnot2 : ¬(n < 2) := by omega
  have hnot3 : ¬(n > n) := by omega
  simp [hnot1, hnot2, hnot3]

lemma D_n1_val (n : ℕ) (hn : n ≥ 3) : D n (n - 1) = 5 * (n : ℤ) - 4 := by
  rw [D]
  have hnot1 : ¬(n ≤ 2) := by omega
  have hnot2 : ¬(n - 1 < 2) := by omega
  have hnot3 : ¬(n - 1 > n) := by omega
  have hnot4 : ¬(n - 1 = n) := by omega
  simp [hnot1, hnot2, hnot3, hnot4]

theorem D_2_val (n : ℕ) (hn : n ≥ 3) : D n 2 = (n : ℤ)^2 + 2 * (n : ℤ) - 4 := by
  have eq1 := D_identity n hn n (by omega) (by omega)
  have eq2 := D_identity n hn (n - 1) (by omega) (by omega)
  change ((n - 2).factorial : ℤ) * D n (n - 1) = 2 * (↑(n - 1) - 2 : ℤ) * D n 3 - w (n - 1) * D n 2 at eq2
  have h_coeff3 : (↑(n - 1) - 2 : ℤ) = n - 3 := by omega
  rw [h_coeff3] at eq2

  have h_w_id := lemma_w (n - 3)
  have h_w_ind1 : n - 3 + 3 = n := by omega
  have h_w_ind2 : n - 3 + 2 = n - 1 := by omega
  have h_w_ind3 : n - 3 + 1 = n - 2 := by omega
  rw [h_w_ind1, h_w_ind2, h_w_ind3] at h_w_id
  have h_w_coeff : (↑(n - 3) + 1 : ℤ) = n - 2 := by omega
  have h_w_coeff2 : ((n - 3 : ℕ) : ℤ) = n - 3 := by omega
  rw [h_w_coeff, h_w_coeff2] at h_w_id

  rw [D_n_val n hn] at eq1
  rw [D_n1_val n hn] at eq2
  have h_comb : (n - 3 : ℤ) * (((n - 1).factorial : ℤ) * 4) - (n - 2 : ℤ) * (((n - 2).factorial : ℤ) * (5 * (n : ℤ) - 4)) =
                (n - 3 : ℤ) * (2 * (n - 2 : ℤ) * D n 3 - w n * D n 2) - (n - 2 : ℤ) * (2 * (n - 3 : ℤ) * D n 3 - w (n - 1) * D n 2) := by
    rw [eq1, eq2]
  have hfac : ((n - 1).factorial : ℤ) = (n - 1 : ℤ) * ((n - 2).factorial : ℤ) := by
    have h_fac_nat : (n - 1).factorial = (n - 1) * (n - 2).factorial := by
      have : n - 1 = Nat.succ (n - 2) := by omega
      rw [this, Nat.factorial_succ]
    have h_cast : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
    push_cast [h_fac_nat]
    rw [h_cast]
  have h_lhs : (n - 3 : ℤ) * (((n - 1).factorial : ℤ) * 4) - (n - 2 : ℤ) * (((n - 2).factorial : ℤ) * (5 * (n : ℤ) - 4)) =
               - ((n : ℤ)^2 + 2 * (n : ℤ) - 4) * ((n - 2).factorial : ℤ) := by
    rw [hfac]
    ring
  have h_rhs : (n - 3 : ℤ) * (2 * (n - 2 : ℤ) * D n 3 - w n * D n 2) - (n - 2 : ℤ) * (2 * (n - 3 : ℤ) * D n 3 - w (n - 1) * D n 2) =
               - ((n - 2).factorial : ℤ) * D n 2 := by
    calc (n - 3 : ℤ) * (2 * (n - 2 : ℤ) * D n 3 - w n * D n 2) - (n - 2 : ℤ) * (2 * (n - 3 : ℤ) * D n 3 - w (n - 1) * D n 2)
      _ = - ((n - 3 : ℤ) * w n - (n - 2 : ℤ) * w (n - 1)) * D n 2 := by ring
      _ = - ((n - 2).factorial : ℤ) * D n 2 := by rw [h_w_id]
  rw [h_lhs, h_rhs] at h_comb
  have h_fac_pos : ((n - 2).factorial : ℤ) ≠ 0 := by
    have : (n - 2).factorial > 0 := Nat.factorial_pos (n - 2)
    omega
  have h_final : (n : ℤ)^2 + 2 * (n : ℤ) - 4 = D n 2 := by
    have h_eq : - ((n : ℤ)^2 + 2 * (n : ℤ) - 4) * ((n - 2).factorial : ℤ) = - D n 2 * ((n - 2).factorial : ℤ) := by
      calc - ((n : ℤ)^2 + 2 * (n : ℤ) - 4) * ((n - 2).factorial : ℤ)
        _ = - ((n : ℤ)^2 + 2 * (n : ℤ) - 4) * ((n - 2).factorial : ℤ) := rfl
        _ = - ((n - 2).factorial : ℤ) * D n 2 := h_comb
        _ = - D n 2 * ((n - 2).factorial : ℤ) := by ring
    have h_eq2 := mul_left_cancel₀ h_fac_pos (by
      calc ((n - 2).factorial : ℤ) * (- ((n : ℤ)^2 + 2 * (n : ℤ) - 4))
        _ = - ((n : ℤ)^2 + 2 * (n : ℤ) - 4) * ((n - 2).factorial : ℤ) := by ring
        _ = - D n 2 * ((n - 2).factorial : ℤ) := h_eq
        _ = ((n - 2).factorial : ℤ) * (- D n 2) := by ring
    )
    omega
  exact h_final.symm

lemma w_even_and_diff_even (j : ℕ) : (2 : ℤ) ∣ w (j + 4) ∧ (2 : ℤ) ∣ (w (j + 4) - w (j + 3)) := by
  induction j with
  | zero =>
    simp [w]
  | succ j ih =>
    rcases ih with ⟨ih1, ih2⟩
    have hw5 : w (j + 5) = (j + 3 : ℤ) * (w (j + 4) - w (j + 3)) := rfl
    have h_div5 : (2 : ℤ) ∣ w (j + 5) := by
      rw [hw5]
      exact dvd_mul_of_dvd_right ih2 (j + 3 : ℤ)
    have h_diff54 : (2 : ℤ) ∣ (w (j + 5) - w (j + 4)) := dvd_sub h_div5 ih1
    exact ⟨h_div5, h_diff54⟩

lemma w_multiple_of_2_n2 (n : ℕ) (hn : n ≥ 3) (hn4 : n ≠ 4) : (2 * (n - 2 : ℤ)) ∣ w n := by
  rcases n with _ | _ | _ | k
  · omega
  · omega
  · omega
  · rcases k with _ | k
    · simp [w]
    · rcases k with _ | k
      · contradiction -- n = 4
      · -- n = k + 5 >= 5
        have hw : w (k + 5) = (k + 3 : ℤ) * (w (k + 4) - w (k + 3)) := rfl
        rw [hw]
        have h_diff_even : (2 : ℤ) ∣ (w (k + 4) - w (k + 3)) := by
          exact (w_even_and_diff_even k).2
        rcases h_diff_even with ⟨d, hd⟩
        use d
        have h_coeff : (2 * (↑(k + 5) - 2 : ℤ)) = 2 * (k + 3 : ℤ) := by omega
        rw [h_coeff]
        rw [hd]
        ring

lemma D_3_nz (p : ℕ) (hp : p.Prime) (hp10 : p ≥ 11) (n : ℕ) (hn3 : 3 ≤ n) (hnp2 : n ≤ p - 2)
  (hd2 : (p : ℤ) ∣ D n 2) : (D n 3 : ℚ) ≠ 0 := by
  intro hc
  have hc_int : D n 3 = 0 := by exact_mod_cast hc
  have eq1 := D_identity n (by omega) n (by omega) (by omega)
  rw [D_n_val n (by omega), hc_int] at eq1
  have eq1' : ((n - 1).factorial : ℤ) * 4 = - w n * D n 2 := by
    calc ((n - 1).factorial : ℤ) * 4
      _ = 2 * (n - 2 : ℤ) * 0 - w n * D n 2 := eq1
      _ = - w n * D n 2 := by ring
  have h_p_dvd : (p : ℤ) ∣ ((n - 1).factorial : ℤ) * 4 := by
    have : (p : ℤ) ∣ - w n * D n 2 := dvd_mul_of_dvd_right hd2 (- w n)
    rw [← eq1'] at this
    exact this
  have h_prime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  rcases h_prime.dvd_mul.mp h_p_dvd with h_p_dvd_fac | h_p_dvd_4
  · have h_dvd_nat : p ∣ (n - 1).factorial := by exact_mod_cast h_p_dvd_fac
    have h_p_lt : p ≤ n - 1 := hp.dvd_factorial.mp h_dvd_nat
    omega
  · have : p ∣ 4 := by exact_mod_cast h_p_dvd_4
    have : p ≤ 4 := Nat.le_of_dvd (by decide) this
    omega

lemma D_nz (p : ℕ) (hp : p.Prime) (hp10 : p ≥ 11) (n : ℕ) (hn3 : 3 ≤ n) (hnp2 : n ≤ p - 2)
  (hd2 : (p : ℤ) ∣ D n 2) (hd2_pos : D n 2 > 0) : ∀ j, 2 ≤ j ∧ j ≤ n → (D n j : ℚ) ≠ 0 := by
  intro j hj hc
  have hc_int : D n j = 0 := by exact_mod_cast hc
  have eq_j := D_identity n (by omega) j hj.1 hj.2
  rw [hc_int] at eq_j
  have eq_j' : w j * D n 2 = 2 * (j - 2 : ℤ) * D n 3 := by
    calc w j * D n 2
      _ = 2 * (j - 2 : ℤ) * D n 3 - ((j - 1).factorial : ℤ) * 0 := by omega
      _ = 2 * (j - 2 : ℤ) * D n 3 := by ring
  have h_p_dvd : (p : ℤ) ∣ 2 * (j - 2 : ℤ) * D n 3 := by
    have : (p : ℤ) ∣ w j * D n 2 := dvd_mul_of_dvd_right hd2 (w j)
    rw [eq_j'] at this
    exact this
  have h_prime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have h_nz3 : (D n 3 : ℚ) ≠ 0 := D_3_nz p hp hp10 n hn3 hnp2 hd2
  have hnz3_int : D n 3 ≠ 0 := by exact_mod_cast h_nz3
  rcases h_prime.dvd_mul.mp h_p_dvd with h_p_dvd_mul2 | h_p_dvd_d3
  · rcases h_prime.dvd_mul.mp h_p_dvd_mul2 with h_p_dvd_2 | h_p_dvd_j2
    · have : p ∣ 2 := by exact_mod_cast h_p_dvd_2
      have : p ≤ 2 := Nat.le_of_dvd (by decide) this
      omega
    · have : j - 2 = 0 := by
        by_contra hnz
        have hj_ge2 : 2 ≤ j := hj.1
        have h_cast_sub : ((j - 2 : ℕ) : ℤ) = (j : ℤ) - 2 := Nat.cast_sub hj_ge2
        have h_p_dvd_j2_cast : (p : ℤ) ∣ ((j - 2 : ℕ) : ℤ) := by
          rwa [h_cast_sub]
        have h_dvd : p ∣ j - 2 := by
          exact_mod_cast h_p_dvd_j2_cast
        have : p ≤ j - 2 := Nat.le_of_dvd (by omega) h_dvd
        omega
      have hj2_eq : j = 2 := by omega
      rw [hj2_eq] at hc_int
      omega
  · have eq_n := D_identity n (by omega) n (by omega) (by omega)
    rw [D_n_val n (by omega)] at eq_n
    have h_p_dvd_n : (p : ℤ) ∣ ((n - 1).factorial : ℤ) * 4 := by
      have h1 : (p : ℤ) ∣ 2 * (n - 2 : ℤ) * D n 3 := dvd_mul_of_dvd_right h_p_dvd_d3 (2 * (n - 2 : ℤ))
      have h2 : (p : ℤ) ∣ w n * D n 2 := dvd_mul_of_dvd_right hd2 (w n)
      have h_sub : (p : ℤ) ∣ 2 * (n - 2 : ℤ) * D n 3 - w n * D n 2 := dvd_sub h1 h2
      rw [← eq_n] at h_sub
      exact h_sub
    rcases h_prime.dvd_mul.mp h_p_dvd_n with h_p_dvd_fac | h_p_dvd_4
    · have h_dvd_nat : p ∣ (n - 1).factorial := by exact_mod_cast h_p_dvd_fac
      have h_p_lt : p ≤ n - 1 := hp.dvd_factorial.mp h_dvd_nat
      omega
    · have : p ∣ 4 := by exact_mod_cast h_p_dvd_4
      have : p ≤ 4 := Nat.le_of_dvd (by decide) this
      omega

def continued_fraction_denominator (n k : ℕ) : ℚ :=
  if n ≤ 2 then 0
  else
    if 2 ≤ k ∧ k ≤ n - 1 then
      if k = n - 1 then
        (k : ℚ) + (n : ℚ) / 4
      else
        let R_next := continued_fraction_denominator n (k + 1)
        (k : ℚ) - (k + 1 : ℚ) / R_next
    else 0
  termination_by n - k

theorem cf_eq_D (n : ℕ) (hn : n ≥ 3) (h_nz : ∀ j, 2 ≤ j ∧ j ≤ n → (D n j : ℚ) ≠ 0) :
  ∀ k, 2 ≤ k ∧ k ≤ n - 1 → continued_fraction_denominator n k = D n k / D n (k + 1) := by
  intro k hk
  induction' h_ind : n - k using Nat.strong_induction_on with d ih generalizing k
  have h_cf : continued_fraction_denominator n k =
    if k = n - 1 then (k : ℚ) + (n : ℚ) / 4
    else (k : ℚ) - (k + 1 : ℚ) / continued_fraction_denominator n (k + 1) := by
      rw [continued_fraction_denominator]
      have hnot1 : ¬(n ≤ 2) := by omega
      have hnot2 : 2 ≤ k ∧ k ≤ n - 1 := hk
      simp [hnot1, hnot2]
  by_cases hk_n1 : k = n - 1
  · rw [h_cf, if_pos hk_n1]
    have h_k : k = n - 1 := hk_n1
    rw [h_k]
    have h_kp1 : n - 1 + 1 = n := by omega
    rw [h_kp1]
    rw [D_n1_val n hn, D_n_val n hn]
    have hk_eq : (↑(n - 1) : ℚ) = (n : ℚ) - 1 := by
      have h_sub : ((n - 1 : ℕ) : ℚ) = (n : ℚ) - (1 : ℚ) := Nat.cast_sub (by omega)
      exact h_sub
    rw [hk_eq]
    push_cast
    ring
  · rw [h_cf, if_neg hk_n1]
    have h_next_k : 2 ≤ k + 1 ∧ k + 1 ≤ n - 1 := by omega
    have h_d_gt : n - (k + 1) < d := by omega
    have h_ih := ih (n - (k + 1)) h_d_gt (k + 1) h_next_k rfl
    rw [h_ih]
    have h_D_rec : D n k = (k : ℤ) * D n (k + 1) - ((k + 1 : ℤ) * D n (k + 2)) := by
      rw [D]
      have hnot1 : ¬(n ≤ 2) := by omega
      have hnot2 : ¬(k < 2) := by omega
      have hnot3 : ¬(k > n) := by omega
      have hnot4 : ¬(k = n) := by omega
      have hnot5 : ¬(k = n - 1) := hk_n1
      simp [hnot1, hnot2, hnot3, hnot4, hnot5]
    have h_D_rec_cast : (D n k : ℚ) = (k : ℚ) * (D n (k + 1) : ℚ) - ((k + 1 : ℚ) * (D n (k + 2) : ℚ)) := by
      push_cast [h_D_rec]
      rfl
    rw [h_D_rec_cast]
    have hnz1 : (D n (k + 1) : ℚ) ≠ 0 := h_nz (k + 1) (by omega)
    have hnz2 : (D n (k + 2) : ℚ) ≠ 0 := h_nz (k + 2) (by omega)
    field_simp

lemma rat_num_abs_of_coprime (a b : ℤ) (hb : b ≠ 0) (h : Nat.Coprime a.natAbs b.natAbs) :
  ((a : ℚ) / (b : ℚ)).num.natAbs = a.natAbs := by
  rcases lt_or_gt_of_ne hb with h_neg | h_pos
  · have h1 : 0 < -b := by omega
    have h2 : (a : ℚ) / (b : ℚ) = (-a : ℚ) / (-b : ℚ) := by
      simp
    rw [h2]
    have h_coprime : Nat.Coprime (-a).natAbs (-b).natAbs := by
      rw [Int.natAbs_neg, Int.natAbs_neg]
      exact h
    have h_eq : ((-a : ℚ) / (-b : ℚ)).num = -a := by
      exact Rat.num_div_eq_of_coprime h1 h_coprime
    rw [h_eq]
    simp
  · have h_coprime : Nat.Coprime a.natAbs b.natAbs := h
    have h_eq := Rat.num_div_eq_of_coprime h_pos h_coprime
    rw [h_eq]

theorem exists_n_of_prime_mod_10 (p : ℕ) (hp : p.Prime) (hp10 : p ≡ 1 [MOD 10] ∨ p ≡ 9 [MOD 10]) :
  ∃ n : ℕ, 3 ≤ n ∧ n ≤ p - 2 ∧ (p : ℤ) ∣ (n : ℤ)^2 + 2 * (n : ℤ) - 4 ∧
           ∃ y' : ℕ, y' ≤ p / 2 ∧ y' * y' ≡ 5 [MOD p] ∧ n = y' - 1 := by
  have hp10_mod : p % 10 = 1 ∨ p % 10 = 9 := hp10
  have hp1 : p ≠ 1 := hp.ne_one
  have hp9 : p ≠ 9 := by
    intro hc
    subst p
    have : 3 ∣ 9 := by decide
    have : ¬ Nat.Prime 9 := by decide
    contradiction
  have hp11 : p ≥ 11 := by omega
  have hp2 : p ≠ 2 := by omega

  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  have : Fact (Nat.Prime p) := ⟨hp⟩

  have h_sq_5 : IsSquare (5 : ZMod p) := by
    have h5 : 5 % 4 = 1 := rfl
    have h_sq_iff := ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one h5 hp2
    have hp5 : IsSquare (p : ZMod 5) := by
      have hp_mod5 : p % 5 = 1 ∨ p % 5 = 4 := by omega
      rcases hp_mod5 with h1 | h4
      · have : (p : ZMod 5) = 1 := by
          apply Fin.ext
          change p % 5 = 1
          exact h1
        rw [this]
        exact ⟨1, rfl⟩
      · have : (p : ZMod 5) = 4 := by
          apply Fin.ext
          change p % 5 = 4
          exact h4
        rw [this]
        exact ⟨2, rfl⟩
    exact h_sq_iff.mp hp5

  rcases h_sq_5 with ⟨x, hx⟩
  let y := x.val
  have hy_lt : y < p := ZMod.val_lt x
  have hy2 : y * y ≡ 5 [MOD p] := by
    have : ((y * y : ℕ) : ZMod p) = ((5 : ℕ) : ZMod p) := by
      rw [Nat.cast_mul]
      calc (y : ZMod p) * (y : ZMod p)
        _ = (x.val : ZMod p) * (x.val : ZMod p) := rfl
        _ = x * x := by rw [ZMod.natCast_zmod_val x]
        _ = 5 := hx.symm
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mp this

  let y' := if y ≤ p / 2 then y else p - y
  have hy'2 : y' * y' ≡ 5 [MOD p] := by
    dsimp [y']
    split_ifs with h_le
    · exact hy2
    · have : ((p - y : ℕ) : ZMod p) = -x := by
        have h_y_val : (y : ZMod p) = x := ZMod.natCast_zmod_val x
        have hy_le : y ≤ p := by omega
        have h_sub : ((p - y : ℕ) : ZMod p) = (p : ZMod p) - (y : ZMod p) := Nat.cast_sub hy_le
        rw [h_sub, h_y_val]
        simp
      have h_cast : (((p - y) * (p - y) : ℕ) : ZMod p) = ((5 : ℕ) : ZMod p) := by
        rw [Nat.cast_mul]
        rw [this]
        ring_nf
        rw [sq]
        exact hx.symm
      have : (((p - y) * (p - y) : ℕ) : ZMod p) = ((5 : ℕ) : ZMod p) := h_cast
      exact (ZMod.natCast_eq_natCast_iff ((p - y) * (p - y)) 5 p).mp this

  have hy'_le : y' ≤ p / 2 := by
    dsimp [y']
    split_ifs with h_le
    · exact h_le
    · omega

  have hy'_ne0 : y' ≠ 0 := by
    intro hc
    dsimp [y'] at hc
    split_ifs at hc with h_le
    · have : y * y ≡ 5 [MOD p] := hy2
      rw [hc] at this
      simp at this
      have h_dvd_int : (p : ℤ) ∣ 5 - 0 * 0 := Nat.modEq_iff_dvd.mp this
      change (p : ℤ) ∣ 5 at h_dvd_int
      have h_dvd : p ∣ 5 := by exact_mod_cast h_dvd_int
      have h_eq : p = 1 ∨ p = 5 := Nat.Prime.eq_one_or_self_of_dvd Nat.prime_five p h_dvd
      omega
    · have : y = p := by omega
      omega

  have hy'_ne1 : y' ≠ 1 := by
    intro hc
    dsimp [y'] at hc
    split_ifs at hc with h_le
    · have : y * y ≡ 5 [MOD p] := hy2
      rw [hc] at this
      simp at this
      have h_dvd_int : (p : ℤ) ∣ 5 - 1 * 1 := Nat.modEq_iff_dvd.mp this
      change (p : ℤ) ∣ 4 at h_dvd_int
      have h_dvd : p ∣ 4 := by exact_mod_cast h_dvd_int
      have : p ≤ 4 := Nat.le_of_dvd (by decide) h_dvd
      omega
    · have hy_eq : y = p - 1 := by omega
      have h_cast : (((p - 1) * (p - 1) : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
        rw [Nat.cast_mul]
        have : ((p - 1 : ℕ) : ZMod p) = -1 := by
          have h_1_le_p : 1 ≤ p := by omega
          have : ((p - 1 : ℕ) : ZMod p) = (p : ZMod p) - 1 := by push_cast [h_1_le_p]; rfl
          rw [this]
          simp
        rw [this]
        ring
      have h_modeq := (ZMod.natCast_eq_natCast_iff _ _ _).mp h_cast
      rw [hy_eq] at hy2
      have : 1 ≡ 5 [MOD p] := by
        calc 1
          _ ≡ (p - 1) * (p - 1) [MOD p] := h_modeq.symm
          _ ≡ 5 [MOD p] := hy2
      have h_dvd_int : (p : ℤ) ∣ 5 - 1 := Nat.modEq_iff_dvd.mp this
      change (p : ℤ) ∣ 4 at h_dvd_int
      have h_dvd : p ∣ 4 := by exact_mod_cast h_dvd_int
      have : p ≤ 4 := Nat.le_of_dvd (by decide) h_dvd
      omega

  have hy'_ne2 : y' ≠ 2 := by
    intro hc
    dsimp [y'] at hc
    split_ifs at hc with h_le
    · have : y * y ≡ 5 [MOD p] := hy2
      rw [hc] at this
      simp at this
      have h_dvd_int : (p : ℤ) ∣ 5 - 2 * 2 := Nat.modEq_iff_dvd.mp this
      change (p : ℤ) ∣ 1 at h_dvd_int
      have h_dvd : p ∣ 1 := by exact_mod_cast h_dvd_int
      have : p ≤ 1 := Nat.le_of_dvd (by decide) h_dvd
      omega
    · have hy_eq : y = p - 2 := by omega
      have h_cast : (((p - 2) * (p - 2) : ℕ) : ZMod p) = ((4 : ℕ) : ZMod p) := by
        rw [Nat.cast_mul]
        have : ((p - 2 : ℕ) : ZMod p) = -2 := by
          have h_2_le_p : 2 ≤ p := by omega
          have : ((p - 2 : ℕ) : ZMod p) = (p : ZMod p) - 2 := by push_cast [h_2_le_p]; rfl
          rw [this]
          simp
        rw [this]
        ring
      have h_modeq := (ZMod.natCast_eq_natCast_iff _ _ _).mp h_cast
      rw [hy_eq] at hy2
      have : 4 ≡ 5 [MOD p] := by
        calc 4
          _ ≡ (p - 2) * (p - 2) [MOD p] := h_modeq.symm
          _ ≡ 5 [MOD p] := hy2
      have h_dvd_int : (p : ℤ) ∣ 5 - 4 := Nat.modEq_iff_dvd.mp this
      change (p : ℤ) ∣ 1 at h_dvd_int
      have h_dvd : p ∣ 1 := by exact_mod_cast h_dvd_int
      have : p ≤ 1 := Nat.le_of_dvd (by decide) h_dvd
      omega

  have hy'_ne3 : y' ≠ 3 := by
    intro hc
    dsimp [y'] at hc
    split_ifs at hc with h_le
    · have : y * y ≡ 5 [MOD p] := hy2
      rw [hc] at this
      simp at this
      have h_dvd_int : (p : ℤ) ∣ 3 * 3 - 5 := Nat.modEq_iff_dvd.mp this.symm
      change (p : ℤ) ∣ 4 at h_dvd_int
      have h_dvd : p ∣ 4 := by exact_mod_cast h_dvd_int
      have : p ≤ 4 := Nat.le_of_dvd (by decide) h_dvd
      omega
    · have hy_eq : y = p - 3 := by omega
      have h_cast : (((p - 3) * (p - 3) : ℕ) : ZMod p) = ((9 : ℕ) : ZMod p) := by
        rw [Nat.cast_mul]
        have : ((p - 3 : ℕ) : ZMod p) = -3 := by
          have h_3_le_p : 3 ≤ p := by omega
          have : ((p - 3 : ℕ) : ZMod p) = (p : ZMod p) - 3 := by push_cast [h_3_le_p]; rfl
          rw [this]
          simp
        rw [this]
        ring
      have h_modeq := (ZMod.natCast_eq_natCast_iff _ _ _).mp h_cast
      rw [hy_eq] at hy2
      have : 9 ≡ 5 [MOD p] := by
        calc 9
          _ ≡ (p - 3) * (p - 3) [MOD p] := h_modeq.symm
          _ ≡ 5 [MOD p] := hy2
      have h_dvd_int : (p : ℤ) ∣ 9 - 5 := Nat.modEq_iff_dvd.mp this.symm
      change (p : ℤ) ∣ 4 at h_dvd_int
      have h_dvd : p ∣ 4 := by exact_mod_cast h_dvd_int
      have : p ≤ 4 := Nat.le_of_dvd (by decide) h_dvd
      omega

  have hy'_ge4 : y' ≥ 4 := by omega

  let n := y' - 1
  use n
  have hn3 : 3 ≤ n := by omega
  have hnp2 : n ≤ p - 2 := by omega
  refine ⟨hn3, hnp2, ?_, y', hy'_le, hy'2, rfl⟩
  have h_eq : (n : ℤ)^2 + 2 * (n : ℤ) - 4 = (y' : ℤ) * (y' : ℤ) - 5 := by
    have : (n : ℤ) = (y' : ℤ) - 1 := by omega
    rw [this]
    ring
  rw [h_eq]
  have : (p : ℤ) ∣ (y' : ℤ) * (y' : ℤ) - 5 := by
    have h_div_neg : (p : ℤ) ∣ 5 - (y' : ℤ) * (y' : ℤ) := Nat.modEq_iff_dvd.mp hy'2
    have h_sub_comm : 5 - (y' : ℤ) * (y' : ℤ) = - ((y' : ℤ) * (y' : ℤ) - 5) := by ring
    rw [h_sub_comm] at h_div_neg
    exact dvd_neg.mp h_div_neg
  exact this

lemma helper_omega (m y' : ℕ) (h1 : 2 * m < y') : 2 * m ≤ y' - 1 := by
  omega

lemma helper_omega2 (m n y' : ℕ) (h1 : 2 * m ≤ y' - 1) (h2 : n = y' - 1) (h3 : y' ≥ 7) : m ≤ n - 3 := by
  omega

lemma helper_omega3 (m y' : ℕ) (h1 : (2 * m : ℤ) < (y' : ℤ)) : 2 * m < y' := by
  omega

lemma helper_omega4 (m_int : ℤ) (m : ℕ) (hm_eq : m = m_int.natAbs) (hm_pos : m_int > 0) : 0 < m := by
  rw [hm_eq]
  omega

lemma helper_dvd_fac (m n : ℕ) (h1 : 0 < m) (h2 : m ≤ n - 3) : m ∣ (n - 3).factorial := by
  exact Nat.dvd_factorial h1 h2

lemma helper_all (m n : ℕ) (m_int : ℤ) (hm_eq : m = m_int.natAbs) (hm_pos : m_int > 0)
    (h_m_le : m ≤ n - 3) : (m : ℤ) ∣ ((n - 3).factorial : ℤ) := by
  have hm_pos_nat : 0 < m := by
    rw [hm_eq]
    omega
  have h_dvd : m ∣ (n - 3).factorial := Nat.dvd_factorial hm_pos_nat h_m_le
  exact_mod_cast h_dvd


lemma helper_prime_dvd_twenty (p : ℕ) (hp : p.Prime) (h_dvd : p ∣ 20) (hp11 : p ≥ 11) : False := by
  have hp20 : p ≤ 20 := Nat.le_of_dvd (by decide) h_dvd
  have : p = 11 ∨ p = 12 ∨ p = 13 ∨ p = 14 ∨ p = 15 ∨ p = 16 ∨ p = 17 ∨ p = 18 ∨ p = 19 ∨ p = 20 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · revert h_dvd; decide
  · revert hp; decide
  · revert h_dvd; decide
  · revert hp; decide
  · revert hp; decide
  · revert hp; decide
  · revert h_dvd; decide
  · revert hp; decide
  · revert h_dvd; decide
  · revert hp; decide

lemma helper_nz_rat (m_int : ℤ) (m : ℕ) (hm_eq : m = m_int.natAbs) (hm_pos : m_int > 0) : (m : ℚ) ≠ 0 := by
  have : m ≠ 0 := by
    rw [hm_eq]
    omega
  exact_mod_cast this

lemma helper_fraction (p m : ℕ) (n : ℕ) (Q_fac : ℤ) (K : ℤ) (hm_nz : (m : ℚ) ≠ 0)
    (h_D2_val : D n 2 = (p * m : ℤ))
    (h_D3_eq_m : D n 3 = m * (2 * (n - 1 : ℤ) * Q_fac + K * p)) :
    ((D n 2 : ℚ) / (D n 3 : ℚ)) = (p : ℚ) / (2 * (n - 1 : ℤ) * Q_fac + K * p : ℤ) := by
  rw [h_D2_val, h_D3_eq_m]
  push_cast
  rw [mul_comm (m : ℚ)]
  rw [mul_div_mul_right _ _ hm_nz]


lemma helper_coprime (p : ℕ) (hp : p.Prime) (hp11 : p ≥ 11) (n : ℕ) (hn3 : 3 ≤ n) (hnp2 : n ≤ p - 2)
    (Q_fac : ℤ) (K : ℤ) (b : ℤ) (hb_def : b = 2 * (n - 1 : ℤ) * Q_fac + K * p)
    (m : ℕ) (hQ_fac : ((n - 3).factorial : ℤ) = m * Q_fac) :
    Nat.Coprime p b.natAbs := by
  rw [Nat.Prime.coprime_iff_not_dvd hp]
  intro hc
  have h_p_dvd_b : (p : ℤ) ∣ b := by
    rcases hc with ⟨c, hc_eq⟩
    rcases Int.natAbs_eq_iff.mp hc_eq with h1 | h2
    · rw [h1]
      exact dvd_mul_right (p : ℤ) (c : ℤ)
    · rw [h2]
      exact dvd_neg.mpr (dvd_mul_right (p : ℤ) (c : ℤ))
  have h_p_dvd_prod_int : (p : ℤ) ∣ 2 * ((n - 1 : ℕ) : ℤ) * (((n - 3).factorial : ℕ) : ℤ) := by
    have h_id : 2 * ((n - 1 : ℕ) : ℤ) * (((n - 3).factorial : ℕ) : ℤ) = m * b - (K * m) * p := by
      have h_n1_cast : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
      rw [h_n1_cast, hb_def, hQ_fac]
      ring
    rw [h_id]
    exact dvd_sub (dvd_mul_of_dvd_right h_p_dvd_b m) (dvd_mul_of_dvd_right (dvd_refl (p : ℤ)) (K * m))
  have h_p_dvd_prod : p ∣ 2 * (n - 1) * (n - 3).factorial := by
    exact_mod_cast h_p_dvd_prod_int
  have h_p_dvd_factor_or : p ∣ 2 * (n - 1) ∨ p ∣ (n - 3).factorial :=
    hp.dvd_mul.mp h_p_dvd_prod
  rcases h_p_dvd_factor_or with h_dvd_2_n1 | h_dvd_fac
  · have h_dvd_2_or_n1 : p ∣ 2 ∨ p ∣ n - 1 := hp.dvd_mul.mp h_dvd_2_n1
    rcases h_dvd_2_or_n1 with h_dvd_2 | h_dvd_n1
    · have : p ≤ 2 := Nat.le_of_dvd (by decide) h_dvd_2
      omega
    · have hn_pos : n - 1 > 0 := by omega
      have : p ≤ n - 1 := Nat.le_of_dvd hn_pos h_dvd_n1
      omega
  · have h_p_lt : p ≤ n - 3 := hp.dvd_factorial.mp h_dvd_fac
    omega

lemma helper_le (n : ℕ) (hn : 3 ≤ n) : 2 ≤ 2 ∧ 2 ≤ n - 1 := by
  omega





noncomputable def A363347 (n : ℕ) : ℕ :=
  if n ≤ 2 then 0
  else
    let R2 := continued_fraction_denominator n 2
    R2.num.natAbs

theorem oeis_363347_conjecture_2 :
  ∀ p : ℕ,
    (p.Prime ∧ (p ≡ 1 [MOD 10] ∨ p ≡ 9 [MOD 10])) →
    ∃ n : ℕ, A363347 n = p := by
  intro p hp_and_hp10
  rcases hp_and_hp10 with ⟨hp, hp10⟩
  have hp11 : p ≥ 11 := by
    have hp10_mod : p % 10 = 1 ∨ p % 10 = 9 := hp10
    have hp1 : p ≠ 1 := hp.ne_one
    have hp9 : p ≠ 9 := by
      intro hc
      subst p
      have : 3 ∣ 9 := by decide
      have : ¬ Nat.Prime 9 := by decide
      contradiction
    omega
  rcases exists_n_of_prime_mod_10 p hp hp10 with ⟨n, hn3, hnp2, hd2_dvd, y', hy'_le, hy'2, hn_eq_y'⟩
  use n
  have hn_ge3 : ¬(n ≤ 2) := by omega
  unfold A363347
  rw [if_neg hn_ge3]
  change (continued_fraction_denominator n 2).num.natAbs = p
  have h_D2_eq : D n 2 = (n : ℤ)^2 + 2 * (n : ℤ) - 4 := D_2_val n hn3
  have hd2 : (p : ℤ) ∣ D n 2 := by
    rw [h_D2_eq]
    exact hd2_dvd
  have hd2_pos : D n 2 > 0 := by
    rw [h_D2_eq]
    have : (n : ℤ) ≥ 3 := by omega
    nlinarith
  rcases hd2 with ⟨m_int, hm_int⟩
  have hm_pos : m_int > 0 := by
    have h_D2_pos : D n 2 > 0 := hd2_pos
    have hp_pos : (p : ℤ) > 0 := by exact_mod_cast (by omega : p > 0)
    rw [hm_int] at h_D2_pos
    have : (p : ℤ) * m_int > 0 := h_D2_pos
    nlinarith
  have hm_def : ∃ m : ℕ, m = m_int.natAbs := ⟨m_int.natAbs, rfl⟩
  rcases hm_def with ⟨m, hm_eq⟩
  have hm_int_eq : m_int = (m : ℤ) := by
    rw [hm_eq]
    exact (Int.natAbs_of_nonneg (by omega : 0 ≤ m_int)).symm
  have h_D2_val : D n 2 = (p * m : ℤ) := by
    rw [← hm_int_eq]
    exact hm_int
  have hn4 : n ≠ 4 := by
    intro hn4
    have hy'5 : y' = 5 := by omega
    have hy'2_val : y' * y' = 25 := by rw [hy'5]
    have h_modeq : 25 ≡ 5 [MOD p] := by
      rw [← hy'2_val]
      exact hy'2
    have h_dvd_int : (p : ℤ) ∣ 25 - 5 := Nat.modEq_iff_dvd.mp h_modeq.symm
    change (p : ℤ) ∣ 20 at h_dvd_int
    have h_dvd : p ∣ 20 := by exact_mod_cast h_dvd_int
    exact helper_prime_dvd_twenty p hp h_dvd hp11
  
  have h_fac_nat : (n - 1).factorial = (n - 1) * (n - 2) * (n - 3).factorial := by
    have h_succ1 : n - 1 = Nat.succ (n - 2) := by omega
    have h_succ2 : n - 2 = Nat.succ (n - 3) := by omega
    rw [h_succ1, Nat.factorial_succ, h_succ2, Nat.factorial_succ]
    simp only [Nat.succ_eq_add_one]
    ring
  have h_fac_eq : ((n - 1).factorial : ℤ) * 4 = 2 * (n - 2 : ℤ) * (2 * (n - 1 : ℤ) * ((n - 3).factorial : ℤ)) := by
    have h_n1 : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
    have h_n2 : ((n - 2 : ℕ) : ℤ) = (n : ℤ) - 2 := by omega
    rw [h_fac_nat]
    push_cast
    rw [h_n1, h_n2]
    ring

  have h_w_dvd := w_multiple_of_2_n2 n hn3 hn4
  rcases h_w_dvd with ⟨K, hK⟩

  have h_D3_eq : D n 3 = 2 * (n - 1 : ℤ) * ((n - 3).factorial : ℤ) + K * D n 2 := by
    have h_coeff_nz : 2 * (n - 2 : ℤ) ≠ 0 := by omega
    have h_eq : 2 * (n - 2 : ℤ) * D n 3 = 2 * (n - 2 : ℤ) * (2 * (n - 1 : ℤ) * ((n - 3).factorial : ℤ) + K * D n 2) := by
      calc 2 * (n - 2 : ℤ) * D n 3
        _ = ((n - 1).factorial : ℤ) * 4 + w n * D n 2 := by
          have h_id := D_identity n hn3 n (by omega) (by omega)
          rw [D_n_val n hn3] at h_id
          omega
        _ = 2 * (n - 2 : ℤ) * (2 * (n - 1 : ℤ) * ((n - 3).factorial : ℤ)) + (2 * (n - 2 : ℤ) * K) * D n 2 := by
          rw [h_fac_eq, hK]
        _ = 2 * (n - 2 : ℤ) * (2 * (n - 1 : ℤ) * ((n - 3).factorial : ℤ) + K * D n 2) := by ring
    exact mul_left_cancel₀ h_coeff_nz h_eq

  have h_m_dvd_fac : (m : ℤ) ∣ ((n - 3).factorial : ℤ) := by
    by_cases hm1 : m = 1
    · rw [hm1]
      simp
    · have hy'_ge6 : y' ≥ 6 := by
        by_contra hc
        have : y' = 4 ∨ y' = 5 := by omega
        rcases this with hy'4 | hy'5
        · have h_mp : (p * m : ℤ) = 11 := by
            calc (p * m : ℤ)
              _ = (p : ℤ) * m_int := by rw [← hm_int_eq]
              _ = D n 2 := hm_int.symm
              _ = (n : ℤ)^2 + 2 * (n : ℤ) - 4 := D_2_val n hn3
              _ = (3 : ℤ)^2 + 2 * (3 : ℤ) - 4 := by
                rw [hn_eq_y', hy'4]
                rfl
              _ = 11 := by rfl
          have h_mp' : m * p = 11 := by rw [mul_comm]; exact_mod_cast h_mp
          have : m ∣ 11 := by
            use p
            exact h_mp'.symm
          have : m = 1 ∨ m = 11 := Nat.Prime.eq_one_or_self_of_dvd Nat.prime_eleven m this
          rcases this with hm1' | hm11
          · contradiction
          · have : p = 1 := by
              have : m * p = 11 := h_mp'
              rw [hm11] at this
              omega
            have : p.Prime := hp
            omega
        · have h_mp : (p * m : ℤ) = 20 := by
            calc (p * m : ℤ)
              _ = (p : ℤ) * m_int := by rw [← hm_int_eq]
              _ = D n 2 := hm_int.symm
              _ = (n : ℤ)^2 + 2 * (n : ℤ) - 4 := D_2_val n hn3
              _ = (4 : ℤ)^2 + 2 * (4 : ℤ) - 4 := by
                rw [hn_eq_y', hy'5]
                rfl
              _ = 20 := by rfl
          have : p ∣ 20 := by
            have h_mp' : p * m = 20 := by exact_mod_cast h_mp
            use m
            exact h_mp'.symm
          have hp20 : p ≤ 20 := Nat.le_of_dvd (by decide) this
          have : p = 11 ∨ p = 12 ∨ p = 13 ∨ p = 14 ∨ p = 15 ∨ p = 16 ∨ p = 17 ∨ p = 18 ∨ p = 19 ∨ p = 20 := by omega
          rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · revert this; decide
          · revert hp; decide
          · revert this; decide
          · revert hp; decide
          · revert hp; decide
          · revert hp; decide
          · revert this; decide
          · revert hp; decide
          · revert this; decide
          · revert hp; decide
      have hm_le : m ≤ n - 3 := by
        have h_mp : (m * p : ℤ) = (y' : ℤ)^2 - 5 := by
          calc (m * p : ℤ)
            _ = (p * m : ℤ) := by ring
            _ = (p : ℤ) * m_int := by rw [← hm_int_eq]
            _ = D n 2 := hm_int.symm
            _ = (n : ℤ)^2 + 2 * (n : ℤ) - 4 := D_2_val n hn3
            _ = (y' : ℤ)^2 - 5 := by
              have : (n : ℤ) = (y' : ℤ) - 1 := by omega
              rw [this]
              ring
        have h_ineq : (m * p : ℤ) < (y' : ℤ) * (y' : ℤ) := by nlinarith
        have h_2y'_le_p : 2 * y' ≤ p := by omega
        have h_m_lt : m_int < (y' : ℤ) := by
          by_contra hc
          push_neg at hc
          have h1 : (m * p : ℤ) ≥ (y' : ℤ) * (2 * y' : ℤ) := by
            have : m_int = (m : ℤ) := hm_int_eq
            nlinarith
          have h2 : (y' : ℤ) * (2 * y' : ℤ) ≥ (y' : ℤ) * (y' : ℤ) := by
            have : (y' : ℤ) ≥ 6 := by omega
            nlinarith
          omega
        have hy'_ge7 : y' ≥ 7 := by
          by_contra hc
          have hy'6 : y' = 6 := by omega
          have h_mp : (p * m : ℤ) = 31 := by
            calc (p * m : ℤ)
              _ = (p : ℤ) * m_int := by rw [← hm_int_eq]
              _ = D n 2 := hm_int.symm
              _ = (n : ℤ)^2 + 2 * (n : ℤ) - 4 := D_2_val n hn3
              _ = (5 : ℤ)^2 + 2 * (5 : ℤ) - 4 := by
                rw [hn_eq_y', hy'6]
                rfl
              _ = 31 := by rfl
          have h_mp' : m * p = 31 := by rw [mul_comm]; exact_mod_cast h_mp
          have : m ∣ 31 := by
            use p
            exact h_mp'.symm
          have : m = 1 ∨ m = 31 := Nat.Prime.eq_one_or_self_of_dvd (by decide) m this
          rcases this with hm1' | hm31
          · contradiction
          · have : p = 1 := by
              have : m * p = 31 := h_mp'
              rw [hm31] at this
              omega
            have : p.Prime := hp
            omega
        have h_2m_lt : 2 * m < y' := by
          have h_le_cast : (2 * y' : ℤ) ≤ (p : ℤ) := by exact_mod_cast h_2y'_le_p
          have hm_nonneg : (m : ℤ) ≥ 0 := by omega
          have h_2my'_le_mp : (2 * m * y' : ℤ) ≤ (m * p : ℤ) := by
            calc (2 * m * y' : ℤ)
              _ = (m : ℤ) * (2 * y' : ℤ) := by ring
              _ ≤ (m : ℤ) * (p : ℤ) := mul_le_mul_of_nonneg_left h_le_cast hm_nonneg
              _ = (m * p : ℤ) := by ring
          have h_my' : (2 * m : ℤ) * (y' : ℤ) < (y' : ℤ) * (y' : ℤ) := by
            calc (2 * m : ℤ) * (y' : ℤ)
              _ = (2 * m * y' : ℤ) := by ring
              _ ≤ m * p := h_2my'_le_mp
              _ < y' * y' := h_ineq
          have hy'_pos : (0 : ℤ) < y' := by omega
          have h_2m_lt_int : (2 * m : ℤ) < (y' : ℤ) := by
            clear hp hp10 hp11 hn3 hnp2 hd2_dvd hy'_le hy'2 hn_eq_y' hn_ge3 h_D2_eq hd2_pos m_int hm_int hm_pos hm_eq hm_int_eq h_D2_val hn4 h_fac_nat h_fac_eq K hK h_D3_eq hm1 hy'_ge6 h_ineq h_2y'_le_p h_m_lt hy'_ge7 h_2my'_le_mp
            nlinarith
          exact helper_omega3 m y' h_2m_lt_int
        have h_2m_le : 2 * m ≤ y' - 1 := helper_omega m y' h_2m_lt
        exact helper_omega2 m n y' h_2m_le hn_eq_y' hy'_ge7
      exact helper_all m n m_int hm_eq hm_pos hm_le

  rcases h_m_dvd_fac with ⟨Q_fac, hQ_fac⟩
  have h_D3_eq_m : D n 3 = m * (2 * (n - 1 : ℤ) * Q_fac + K * p) := by
    rw [h_D3_eq, h_D2_val]
    rw [hQ_fac]
    ring

  have h_nz_hyp : ∀ j, 2 ≤ j ∧ j ≤ n → (D n j : ℚ) ≠ 0 := D_nz p hp hp11 n hn3 hnp2 ⟨m_int, hm_int⟩ hd2_pos
  have h_cf2 := cf_eq_D n hn3 h_nz_hyp 2 (helper_le n hn3)
  rw [h_cf2]

  have hm_nz_rat : (m : ℚ) ≠ 0 := helper_nz_rat m_int m hm_eq hm_pos
  have h_fraction : ((D n 2 : ℚ) / (D n 3 : ℚ)) = (p : ℚ) / (2 * (n - 1 : ℤ) * Q_fac + K * p : ℤ) :=
    helper_fraction p m n Q_fac K hm_nz_rat h_D2_val h_D3_eq_m

  rw [h_fraction]
  let b := 2 * (n - 1 : ℤ) * Q_fac + K * p
  have hb_nz : b ≠ 0 := by
    intro hc
    have h_div_zero : (D n 3 : ℚ) = 0 := by
      rw [h_D3_eq_m]
      have hc_val : 2 * (n - 1 : ℤ) * Q_fac + K * p = 0 := hc
      rw [hc_val]
      push_cast
      ring
    have h_nz3 : (D n 3 : ℚ) ≠ 0 := h_nz_hyp 3 ⟨by decide, hn3⟩
    exact h_nz3 h_div_zero

  have h_coprime : Nat.Coprime p b.natAbs :=
    helper_coprime p hp hp11 n hn3 hnp2 Q_fac K b rfl m hQ_fac
  exact rat_num_abs_of_coprime p b hb_nz h_coprime
