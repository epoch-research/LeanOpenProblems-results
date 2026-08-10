import FormalConjectures.Util.ProblemImports

open Real Int

theorem pi_gt_60 : 3.141592653589793238462643383279502884197169399375105820974944592307816406286208 < Real.pi := sorry
theorem pi_lt_60 : Real.pi < 3.141592653589793238462643383279502884197169399375105820974944592307816406286210 := sorry

def S_prop (n : ℕ) : Prop :=
  ¬ ∃ (k : ℤ), Real.pi * (10 : ℝ) ^ n < (k : ℝ) ∧
    (k : ℝ) < Real.pi * (10 : ℝ) ^ n + 2 * (10 : ℝ) ^ (-n : ℤ)

def T_prop (n : ℕ) : Prop :=
  ∀ (r : ℤ), 1 ≤ r → r < 10 ^ (n - 59) →
    ¬ ∃ (q : ℤ), Real.pi * (10 : ℝ) ^ n - (r : ℝ) / (10 : ℝ) ^ (n - 59) < (q : ℝ) ∧
      (q : ℝ) < Real.pi * (10 : ℝ) ^ n - (r : ℝ) / (10 : ℝ) ^ (n - 59) + 2 * (10 : ℝ) ^ (-(n + (n - 59) + 1 : ℤ))

lemma subgoal_T_60 : T_prop 60 := by
  intro r hr1 hr2
  intro ⟨q, h1, h2⟩
  have h_pi_gt : 3.141592653589793238462643383279502884197169399375105820974944592307816406286208 < Real.pi := pi_gt_60
  have h_pi_lt : Real.pi < 3.141592653589793238462643383279502884197169399375105820974944592307816406286210 := pi_lt_60
  have h_pow_cast_real_60 : (10 : ℝ) ^ 60 = 1000000000000000000000000000000000000000000000000000000000000 := by norm_num
  have h_ten_neg : 2 * (10 : ℝ) ^ (-62 : ℤ) = 2 / 100000000000000000000000000000000000000000000000000000000000000 := by norm_num
  have h_pi_scaled_gt : 3141592653589793238462643383279502884197169399375105820974944.592307816406286208 < Real.pi * (10 : ℝ) ^ 60 := by
    have h_scale : (3141592653589793238462643383279502884197169399375105820974944.592307816406286208 : ℝ) = 3.141592653589793238462643383279502884197169399375105820974944592307816406286208 * (10 : ℝ) ^ 60 := by norm_num
    rw [h_scale]
    linarith [h_pi_gt]
  have h_pi_scaled_lt : Real.pi * (10 : ℝ) ^ 60 < 3141592653589793238462643383279502884197169399375105820974944.592307816406286210 := by
    have h_scale : (3141592653589793238462643383279502884197169399375105820974944.592307816406286210 : ℝ) = 3.141592653589793238462643383279502884197169399375105820974944592307816406286210 * (10 : ℝ) ^ 60 := by norm_num
    rw [h_scale]
    linarith [h_pi_lt]
  have h_or : r ≤ 5 ∨ 6 ≤ r := by omega
  rcases h_or with hr_le5 | hr_ge6
  · have hr_le5_real : (r : ℝ) ≤ 5 := by exact_mod_cast hr_le5
    have hr1_real : (1 : ℝ) ≤ r := by exact_mod_cast hr1
    have h_q_gt_real : (3141592653589793238462643383279502884197169399375105820974944 : ℝ) < (q : ℝ) := by
      have : Real.pi * (10 : ℝ) ^ 60 - (r : ℝ) / 10 < (q : ℝ) := h1
      linarith [h_pi_scaled_gt]
    have h_q_lt_real : (q : ℝ) < (3141592653589793238462643383279502884197169399375105820974945 : ℝ) := by
      have : (q : ℝ) < Real.pi * (10 : ℝ) ^ 60 - (r : ℝ) / 10 + 2 * (10 : ℝ) ^ (-62 : ℤ) := h2
      rw [h_ten_neg] at this
      linarith [h_pi_scaled_lt]
    have hk_gt : 3141592653589793238462643383279502884197169399375105820974944 < q := by exact_mod_cast h_q_gt_real
    have hk_lt : q < 3141592653589793238462643383279502884197169399375105820974945 := by exact_mod_cast h_q_lt_real
    omega
  · have hr_ge6_real : (6 : ℝ) ≤ r := by exact_mod_cast hr_ge6
    have hr2_real : (r : ℝ) ≤ 9 := by exact_mod_cast hr2
    have h_q_gt_real : (3141592653589793238462643383279502884197169399375105820974943 : ℝ) < (q : ℝ) := by
      have : Real.pi * (10 : ℝ) ^ 60 - (r : ℝ) / 10 < (q : ℝ) := h1
      linarith [h_pi_scaled_gt]
    have h_q_lt_real : (q : ℝ) < (3141592653589793238462643383279502884197169399375105820974944 : ℝ) := by
      have : (q : ℝ) < Real.pi * (10 : ℝ) ^ 60 - (r : ℝ) / 10 + 2 * (10 : ℝ) ^ (-62 : ℤ) := h2
      rw [h_ten_neg] at this
      linarith [h_pi_scaled_lt]
    have hk_gt : 3141592653589793238462643383279502884197169399375105820974943 < q := by exact_mod_cast h_q_gt_real
    have hk_lt : q < 3141592653589793238462643383279502884197169399375105820974944 := by exact_mod_cast h_q_lt_real
    omega

lemma main_induction_step (n : ℕ) (hn : 60 ≤ n) (IH : S_prop n ∧ T_prop n) : S_prop (n + 1) ∧ T_prop (n + 1) := by
  have hS : S_prop (n + 1) := by
    intro ⟨k, h1, h2⟩
    have h_gt : Real.pi * (10 : ℝ) ^ (n + 1) < (k : ℝ) := h1
    have h_lt : (k : ℝ) < Real.pi * (10 : ℝ) ^ (n + 1) + 2 * (10 : ℝ) ^ (-((n + 1) : ℤ)) := h2
    have h_div_10 : k % 10 = 0 ∨ (∃ r, (1 ≤ r ∧ r ≤ 9) ∧ k = 10 * (k / 10) + r) := by
      have : k % 10 = 0 ∨ 1 ≤ k % 10 ∧ k % 10 ≤ 9 := by omega
      rcases this with hk0 | hk_rem
      · left; exact hk0
      · right; use k % 10; exact ⟨hk_rem, by omega⟩
    rcases h_div_10 with hk0 | ⟨r, ⟨hr1, hr2⟩, hq⟩
    · let q := k / 10
      have h_k_eq : k = 10 * q := by omega
      have h_q_gt : Real.pi * (10 : ℝ) ^ n < (q : ℝ) := by
        have : (k : ℝ) = 10 * (q : ℝ) := by exact_mod_cast h_k_eq
        have h_gt_simp : Real.pi * (10 : ℝ) ^ (n + 1) < 10 * (q : ℝ) := by rwa [this] at h_gt
        have h_pow_eq_10_mul : (10 : ℝ) ^ (n + 1) = (10 : ℝ) ^ n * 10 := pow_succ 10 n
        rw [h_pow_eq_10_mul, ← mul_assoc] at h_gt_simp
        linarith
      have h_q_lt : (q : ℝ) < Real.pi * (10 : ℝ) ^ n + 2 * (10 : ℝ) ^ (-n : ℤ) := by
        have : (k : ℝ) = 10 * (q : ℝ) := by exact_mod_cast h_k_eq
        have h_lt_simp : 10 * (q : ℝ) < Real.pi * (10 : ℝ) ^ (n + 1) + 2 * (10 : ℝ) ^ (-((n + 1) : ℤ)) := by rwa [this] at h_lt
        have h_pow_eq_10_mul : (10 : ℝ) ^ (n + 1) = (10 : ℝ) ^ n * 10 := pow_succ 10 n
        have h_zpow_eq_10_div : (10 : ℝ) ^ (-((n + 1) : ℤ)) = (10 : ℝ) ^ (-n : ℤ) / 10 := by
          have : -((n + 1) : ℤ) = -n - 1 := by omega
          rw [this, zpow_sub_one₀ (by norm_num)]
          ring
        rw [h_pow_eq_10_mul, h_zpow_eq_10_div, ← mul_assoc] at h_lt_simp
        linarith
      have h_contra : ∃ (k' : ℤ), Real.pi * (10 : ℝ) ^ n < k'.cast ∧ k'.cast < Real.pi * (10 : ℝ) ^ n + 2 * (10 : ℝ) ^ (-n : ℤ) := ⟨q, h_q_gt, h_q_lt⟩
      exact IH.left h_contra
    · let q := k / 10
      have h_k_eq : k = 10 * q + r := hq
      have : (k : ℝ) = 10 * (q : ℝ) + (r : ℝ) := by exact_mod_cast h_k_eq
      have h_gt' : Real.pi * (10 : ℝ) ^ n - (r : ℝ) / 10 < (q : ℝ) := by
        have h_gt_rw : Real.pi * (10 : ℝ) ^ (n + 1) < 10 * (q : ℝ) + (r : ℝ) := by rwa [this] at h_gt
        have h_pow_eq : (10 : ℝ) ^ (n + 1) = (10 : ℝ) ^ n * 10 := pow_succ 10 n
        rw [h_pow_eq, ← mul_assoc] at h_gt_rw
        linarith
      have h_lt' : (q : ℝ) < Real.pi * (10 : ℝ) ^ n - (r : ℝ) / 10 + 2 * (10 : ℝ) ^ (-(n + 2 : ℤ)) := by
        have h_lt_rw : 10 * (q : ℝ) + (r : ℝ) < Real.pi * (10 : ℝ) ^ (n + 1) + 2 * (10 : ℝ) ^ (-((n + 1) : ℤ)) := by rwa [this] at h_lt
        have h_pow_eq : (10 : ℝ) ^ (n + 1) = (10 : ℝ) ^ n * 10 := pow_succ 10 n
        have h_zpow_eq : (10 : ℝ) ^ (-((n + 1) : ℤ)) = (10 : ℝ) ^ (-(n + 2 : ℤ)) * 10 := by
          have : -((n + 1) : ℤ) = -(n + 2 : ℤ) + 1 := by omega
          rw [this, zpow_add₀ (by norm_num)]
          ring
        rw [h_pow_eq, h_zpow_eq, ← mul_assoc] at h_lt_rw
        linarith
      have h_contra : ∃ (q' : ℤ), Real.pi * (10 : ℝ) ^ n - (r : ℝ) / (10 : ℝ) ^ 1 < (q' : ℝ) ∧
          (q' : ℝ) < Real.pi * (10 : ℝ) ^ n - (r : ℝ) / (10 : ℝ) ^ 1 + 2 * (10 : ℝ) ^ (-(n + 1 + 1 : ℤ)) := by
        use q
        have : (10 : ℝ) ^ 1 = 10 := by norm_num
        have : -(n + 1 + 1 : ℤ) = -(n + 2 : ℤ) := by omega
        rw [this, ‹(10 : ℝ) ^ 1 = 10›]
        exact ⟨h_gt', h_lt'⟩
      have hr_pow : r < 10 ^ 1 := by omega
      have hr_pow_n : r < 10 ^ (n - 59) := by
        have : 1 ≤ n - 59 := by omega
        have h_ten : (10 : ℤ) ^ 1 ≤ 10 ^ (n - 59) := by
          apply pow_le_pow_right₀ (by norm_num) this
        omega
      exact IH.right r hr1 hr_pow_n h_contra

  have hT : T_prop (n + 1) := by
    intro k r' hr1' hr2'
    intro ⟨q', h1', h2'⟩
    let q'' := q' / 10
    let r'' := q' % 10
    have h_q'_eq : q' = 10 * q'' + r'' := by omega
    have h_r''1 : 0 ≤ r'' := by omega
    have h_r''2 : r'' ≤ 9 := by omega
    let R := 10 ^ k * r'' + r'
    have h_pow_pos : (10 : ℤ) ^ k > 0 := by positivity
    have h_pow_ge1 : (10 : ℤ) ^ k ≥ 1 := by omega
    have h_R_gt : 1 ≤ R := by
      nlinarith
    have h_pow_k_succ_int : (10 : ℤ) ^ (k + 1) = 10 ^ k * 10 := by ring
    have h_R_lt : R < 10 ^ (k + 1) := by
      nlinarith [h_pow_k_succ_int]
    have h_q'_eq_real : (q' : ℝ) = 10 * (q'' : ℝ) + (r'' : ℝ) := by exact_mod_cast h_q'_eq
    have h_pow_k_succ : (10 : ℝ) ^ (k + 1) = (10 : ℝ) ^ k * 10 := by rw [pow_succ]
    have h_R_real : (R : ℝ) = (10 : ℝ) ^ k * (r'' : ℝ) + (r' : ℝ) := by
      exact_mod_cast (by rfl : R = 10 ^ k * r'' + r')
    have h_pow_n_succ : (10 : ℝ) ^ (n + 1) = (10 : ℝ) ^ n * 10 := pow_succ 10 n
    have h_zpow_n_succ : (10 : ℝ) ^ (-(((n + 1 : ℕ) : ℤ) + (k : ℤ) + 1)) = (10 : ℝ) ^ (-(n + k + 2 : ℤ)) := by
      congr 1
      omega
    have h_zpow_n_div : (10 : ℝ) ^ (-(n + k + 2 : ℤ)) = (10 : ℝ) ^ (-(n + k + 1 : ℤ)) / 10 := by
      have : -(n + k + 2 : ℤ) = -(n + k + 1 : ℤ) - 1 := by omega
      rw [this, zpow_sub_one₀ (by norm_num)]
      ring
    have h_R_div : (R : ℝ) / (10 : ℝ) ^ (k + 1) = (r'' : ℝ) / 10 + (r' : ℝ) / ((10 : ℝ) ^ k * 10) := by
      rw [h_R_real, h_pow_k_succ]
      have h_denom : (10 : ℝ) ^ k * 10 ≠ 0 := by positivity
      field_simp
    have h_div_assoc : (r' : ℝ) / ((10 : ℝ) ^ k * 10) = ((r' : ℝ) / (10 : ℝ) ^ k) / 10 := by ring
    have h_gt : Real.pi * (10 : ℝ) ^ n - (R : ℝ) / (10 : ℝ) ^ (k + 1) < (q'' : ℝ) := by
      rw [h_pow_n_succ, h_q'_eq_real, ← mul_assoc] at h1'
      rw [h_R_div, h_div_assoc]
      linarith
    have h_zpow_goal : (10 : ℝ) ^ (-(n + (k + 1) + 1 : ℤ)) = (10 : ℝ) ^ (-(n + k + 1 : ℤ)) / 10 := by
      have : -(n + (k + 1) + 1 : ℤ) = -(n + k + 1 : ℤ) - 1 := by omega
      rw [this, zpow_sub_one₀ (by norm_num)]
      ring
    have h_lt : (q'' : ℝ) < Real.pi * (10 : ℝ) ^ n - (R : ℝ) / (10 : ℝ) ^ (k + 1) + 2 * (10 : ℝ) ^ (-(n + (k + 1) + 1 : ℤ)) := by
      rw [h_pow_n_succ, h_q'_eq_real, ← mul_assoc, h_zpow_n_succ, h_zpow_n_div] at h2'
      rw [h_R_div, h_div_assoc, h_zpow_goal]
      linarith
    have h_contra : ∃ (q'' : ℤ), Real.pi * (10 : ℝ) ^ n - (R : ℝ) / (10 : ℝ) ^ (k + 1) < (q'' : ℝ) ∧
        (q'' : ℝ) < Real.pi * (10 : ℝ) ^ n - (R : ℝ) / (10 : ℝ) ^ (k + 1) + 2 * (10 : ℝ) ^ (-(n + (k + 1) + 1 : ℤ)) := ⟨q'', h_gt, h_lt⟩
    have h_T_n := IH.right (k + 1) R h_R_gt h_R_lt h_contra
    exact h_T_n
  exact ⟨hS, hT⟩
