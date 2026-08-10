with open("/workspace/leanproject/Submission/Spec.lean", "r") as f:
    lines = f.readlines()

# Keep only the first 1791 lines
kept_lines = lines[:1791]

new_code = """
def S_prop (n : ℕ) : Prop :=
  ¬ ∃ (k : ℤ), Real.pi * (10 : ℝ) ^ n < (k : ℝ) ∧
    (k : ℝ) < Real.pi / Real.arctan (1 / (10 : ℝ) ^ n)

def T_prop_at (n : ℕ) (Y : ℕ) : Prop :=
  ∀ (r : ℤ), 1 ≤ r → r ≤ 9 →
    ¬ ∃ (q : ℤ), Real.pi * (10 : ℝ) ^ (n + Y) - (r : ℝ) / 10 < (q : ℝ) ∧
      (q : ℝ) < Real.pi * (10 : ℝ) ^ (n + Y) - (r : ℝ) / 10 + 2 * (10 : ℝ) ^ (-(n + Y + 2 : ℤ))

lemma T_prop_at_zero_of_S_prop (n : ℕ) (hS : S_prop (n + 1)) : T_prop_at n 0 := by
  intro r hr1 hr2
  intro ⟨q, h1, h2⟩
  let k := 10 * q + r
  have h_k_eq : (k : ℝ) = 10 * (q : ℝ) + (r : ℝ) := by exact_mod_cast (by rfl : k = 10 * q + r)
  have h_pow_eq : (10 : ℝ) ^ (n + 1) = (10 : ℝ) ^ n * 10 := pow_succ 10 n
  have h_gt : Real.pi * (10 : ℝ) ^ (n + 1) < (k : ℝ) := by
    rw [h_pow_eq, h_k_eq]
    have h1_simp : Real.pi * (10 : ℝ) ^ n - (r : ℝ) / 10 < (q : ℝ) := by
      rw [add_zero] at h1
      exact h1
    linarith
  have h_lt : (k : ℝ) < Real.pi / Real.arctan (1 / (10 : ℝ) ^ (n + 1)) := by
    have h_ub := upper_bound_interval_tight (n + 1) (by omega)
    push_cast at h_ub
    have h2_simp : (q : ℝ) < Real.pi * (10 : ℝ) ^ n - (r : ℝ) / 10 + 2 * (10 : ℝ) ^ (-(n + 2 : ℤ)) := by
      have h_eq : (-(n + 0 + 2 : ℤ)) = -(n + 2 : ℤ) := by omega
      rw [h_eq] at h2
      rw [add_zero] at h2
      exact h2
    have h_zpow_eq : (10 : ℝ) ^ (-((n + 1) : ℤ)) = (10 : ℝ) ^ (-(n + 2 : ℤ)) * 10 := by
      have : -((n + 1) : ℤ) = -(n + 2 : ℤ) + 1 := by omega
      rw [this, zpow_add₀ (by norm_num)]
      ring
    have h_lt_relaxed : 10 * (q : ℝ) + (r : ℝ) < Real.pi * (10 : ℝ) ^ (n + 1) + 2 * (10 : ℝ) ^ (-((n + 1) : ℤ)) := by
      rw [h_pow_eq, h_zpow_eq]
      linarith
    rw [h_k_eq]
    linarith [h_lt_relaxed, h_ub]
  have h_contra : ∃ (k' : ℤ), Real.pi * (10 : ℝ) ^ (n + 1) < (k' : ℝ) ∧ (k' : ℝ) < Real.pi / Real.arctan (1 / (10 : ℝ) ^ (n + 1)) := ⟨k, h_gt, h_lt⟩
  exact hS h_contra

lemma subgoal_S_60 : S_prop 60 := by
  intro ⟨k, h1, h2⟩
  have h_pow_cast_real : (10 : ℝ) ^ (60 : ℕ).cast = (10 : ℝ) ^ 60 := Real.rpow_natCast 10 60
  rw [h_pow_cast_real] at h1 h2
  exact subgoal_case_60 ⟨k, h1, h2⟩

lemma subgoal_T_60_zero : T_prop_at 60 0 := by
  intro r hr1 hr2
  intro ⟨q, h1, h2⟩
  have h_pi_gt : 3.141592653589793238462643383279502884197169399375105820974944592307816406286208 < Real.pi := pi_gt_60
  have h_pi_lt : Real.pi < 3.141592653589793238462643383279502884197169399375105820974944592307816406286210 := pi_lt_60
  have h_pow_cast_real_60 : (10 : ℝ) ^ 60 = 1000000000000000000000000000000000000000000000000000000000000 := by norm_num
  have h_ten_neg : 2 * (10 : ℝ) ^ (-62 : ℤ) = 2 / 100000000000000000000000000000000000000000000000000000000000000 := by norm_num
  have h_pi_scaled_gt : 3141592653589793238462643383279502884197169399375105820974944.592307816406286208 * (10 : ℝ) ^ 0 < Real.pi * (10 : ℝ) ^ 60 := by
    have h_scale : (3141592653589793238462643383279502884197169399375105820974944.592307816406286208 : ℝ) = 3.141592653589793238462643383279502884197169399375105820974944592307816406286208 * (10 : ℝ) ^ 60 := by norm_num
    rw [h_scale]
    rw [h_pow_cast_real_60]
    linarith [h_pi_gt]
  have h_pi_scaled_lt : Real.pi * (10 : ℝ) ^ 60 < 3141592653589793238462643383279502884197169399375105820974944.592307816406286210 := by
    have h_scale : (3141592653589793238462643383279502884197169399375105820974944.592307816406286210 : ℝ) = 3.141592653589793238462643383279502884197169399375105820974944592307816406286210 * (10 : ℝ) ^ 60 := by norm_num
    rw [h_scale]
    rw [h_pow_cast_real_60]
    linarith [h_pi_lt]
  have h_or : r ≤ 5 ∨ 6 ≤ r := by omega
  rcases h_or with hr_le5 | hr_ge6
  · have hr_le5_real : (r : ℝ) ≤ 5 := by exact_mod_cast hr_le5
    have hr1_real : (1 : ℝ) ≤ r := by exact_mod_cast hr1
    have h_q_gt_real : (3141592653589793238462643383279502884197169399375105820974944 : ℝ) < (q : ℝ) := by
      have : Real.pi * (10 : ℝ) ^ 60 - (r : ℝ) / 10 < (q : ℝ) := by
        rw [add_zero] at h1; exact h1
      linarith [h_pi_scaled_gt]
    have h_q_lt_real : (q : ℝ) < (3141592653589793238462643383279502884197169399375105820974945 : ℝ) := by
      have : (q : ℝ) < Real.pi * (10 : ℝ) ^ 60 - (r : ℝ) / 10 + 2 * (10 : ℝ) ^ (-62 : ℤ) := by
        have h2_rw := h2
        have h_eq : (-(60 + 0 + 2 : ℤ)) = -62 := by rfl
        rw [h_eq] at h2_rw
        rw [add_zero] at h2_rw
        exact h2_rw
      rw [h_ten_neg] at this
      linarith [h_pi_scaled_lt]
    have hk_gt : 3141592653589793238462643383279502884197169399375105820974944 < q := by exact_mod_cast h_q_gt_real
    have hk_lt : q < 3141592653589793238462643383279502884197169399375105820974945 := by exact_mod_cast h_q_lt_real
    omega
  · have hr_ge6_real : (6 : ℝ) ≤ r := by exact_mod_cast hr_ge6
    have hr2_real : (r : ℝ) ≤ 9 := by exact_mod_cast hr2
    have h_q_gt_real : (3141592653589793238462643383279502884197169399375105820974943 : ℝ) < (q : ℝ) := by
      have : Real.pi * (10 : ℝ) ^ 60 - (r : ℝ) / 10 < (q : ℝ) := by
        rw [add_zero] at h1; exact h1
      linarith [h_pi_scaled_gt]
    have h_q_lt_real : (q : ℝ) < (3141592653589793238462643383279502884197169399375105820974944 : ℝ) := by
      have : (q : ℝ) < Real.pi * (10 : ℝ) ^ 60 - (r : ℝ) / 10 + 2 * (10 : ℝ) ^ (-62 : ℤ) := by
        have h2_rw := h2
        have h_eq : (-(60 + 0 + 2 : ℤ)) = -62 := by rfl
        rw [h_eq] at h2_rw
        rw [add_zero] at h2_rw
        exact h2_rw
      rw [h_ten_neg] at this
      linarith [h_pi_scaled_lt]
    have hk_gt : 3141592653589793238462643383279502884197169399375105820974943 < q := by exact_mod_cast h_q_gt_real
    have hk_lt : q < 3141592653589793238462643383279502884197169399375105820974944 := by exact_mod_cast h_q_lt_real
    omega

lemma main_induction_new (m : ℕ) : S_prop (60 + m) ∧ (∀ Y ≤ m, T_prop_at 60 Y) := by
  induction' m with m IH
  · constructor
    · exact subgoal_S_60
    · intro Y hY
      have : Y = 0 := by omega
      rw [this]
      exact subgoal_T_60_zero
  · rcases IH with ⟨IH_S, IH_T⟩
    let n := 60 + m
    have hS : S_prop (n + 1) := by
      intro ⟨k, h1, h2⟩
      have h_ub := upper_bound_interval_tight (n + 1) (by omega)
      push_cast at h_ub
      have h_lt : (k : ℝ) < Real.pi * (10 : ℝ) ^ (n + 1) + 2 * (10 : ℝ) ^ (-(n + 1 : ℤ)) := by
        push_cast
        linarith [h2, h_ub]
      have h_gt : Real.pi * (10 : ℝ) ^ (n + 1) < (k : ℝ) := h1
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
          rw [h_pow_eq_10_mul] at h_gt_simp
          linarith [h_gt_simp]
        have h_q_lt : (q : ℝ) < Real.pi / Real.arctan (1 / (10 : ℝ) ^ n) := by
          have : (k : ℝ) = 10 * (q : ℝ) := by exact_mod_cast h_k_eq
          have h_lt_simp : 10 * (q : ℝ) < Real.pi * (10 : ℝ) ^ (n + 1) + 2 * (10 : ℝ) ^ (-((n + 1) : ℤ)) := by rwa [this] at h_lt
          have h_pow_eq_10_mul : (10 : ℝ) ^ (n + 1) = (10 : ℝ) ^ n * 10 := pow_succ 10 n
          have h_zpow_eq_10_div : (10 : ℝ) ^ (-((n + 1) : ℤ)) = (10 : ℝ) ^ (-n : ℤ) / 10 := by
            have : -((n + 1) : ℤ) = -n - 1 := by omega
            rw [this, zpow_sub_one₀ (by norm_num)]
            ring
          rw [h_pow_eq_10_mul, h_zpow_eq_10_div] at h_lt_simp
          have h_q_lt_linear : (q : ℝ) < Real.pi * (10 : ℝ) ^ n + 0.2 * (10 : ℝ) ^ (-n : ℤ) := by linarith
          have h_arctan_lower := pi_div_arctan_gt n (by omega)
          have h_pow_neg_eq : (10 : ℝ) ^ (-(n + 2 : ℤ)) = 0.01 * (10 : ℝ) ^ (-n : ℤ) := by
            have : (-(n + 2 : ℤ)) = (-n : ℤ) + (-2 : ℤ) := by omega
            rw [this, zpow_add₀ (by norm_num)]
            ring
          rw [h_pow_neg_eq] at h_arctan_lower
          linarith [h_q_lt_linear, h_arctan_lower]
        have h_contra : ∃ (k' : ℤ), Real.pi * (10 : ℝ) ^ n < k'.cast ∧ k'.cast < Real.pi / Real.arctan (1 / (10 : ℝ) ^ n) := ⟨q, h_q_gt, h_q_lt⟩
        exact IH_S h_contra
      · let q := k / 10
        have h_k_eq : k = 10 * q + r := hq
        have : (k : ℝ) = 10 * (q : ℝ) + (r : ℝ) := by exact_mod_cast h_k_eq
        have h_gt' : Real.pi * (10 : ℝ) ^ n - (r : ℝ) / 10 < (q : ℝ) := by
          have h_gt_rw : Real.pi * (10 : ℝ) ^ (n + 1) < 10 * (q : ℝ) + (r : ℝ) := by rwa [this] at h_gt
          have h_pow_eq : (10 : ℝ) ^ (n + 1) = (10 : ℝ) ^ n * 10 := pow_succ 10 n
          rw [h_pow_eq] at h_gt_rw
          linarith
        have h_lt' : (q : ℝ) < Real.pi * (10 : ℝ) ^ n - (r : ℝ) / 10 + 2 * (10 : ℝ) ^ (-(n + 2 : ℤ)) := by
          have h_lt_rw : 10 * (q : ℝ) + (r : ℝ) < Real.pi * (10 : ℝ) ^ (n + 1) + 2 * (10 : ℝ) ^ (-((n + 1) : ℤ)) := by rwa [this] at h_lt
          have h_pow_eq : (10 : ℝ) ^ (n + 1) = (10 : ℝ) ^ n * 10 := pow_succ 10 n
          have h_zpow_eq : (10 : ℝ) ^ (-((n + 1) : ℤ)) = (10 : ℝ) ^ (-(n + 2 : ℤ)) * 10 := by
            have : -((n + 1) : ℤ) = -(n + 2 : ℤ) + 1 := by omega
            rw [this, zpow_add₀ (by norm_num)]
            ring
          rw [h_pow_eq, h_zpow_eq] at h_lt_rw
          linarith
        have h_contra : ∃ (q' : ℤ), Real.pi * (10 : ℝ) ^ n - (r : ℝ) / 10 < (q' : ℝ) ∧
            (q' : ℝ) < Real.pi * (10 : ℝ) ^ n - (r : ℝ) / 10 + 2 * (10 : ℝ) ^ (-(n + 2 : ℤ)) := ⟨q, h_gt', h_lt'⟩
        exact IH_T m (by omega) r hr1 hr2 h_contra
    constructor
    · exact hS
    · intro Y hY
      have h_or : Y ≤ m ∨ Y = m + 1 := by omega
      rcases h_or with hY_le | rfl
      · exact IH_T Y hY_le
      · have : T_prop_at n 0 := T_prop_at_zero_of_S_prop n hS
        exact this

theorem oeis_a011545_conjecture_0 (n : ℕ) :
    ¬ ∃ (k : ℤ),
      (Real.pi * (10 : ℝ) ^ n.cast < k.cast) ∧
      (k.cast < Real.pi / Real.arctan (1 / (10 : ℝ) ^ n.cast)) := by
  rcases n with _ | n
  · intro ⟨k, h1, h2⟩
    have h_pi_gt : 3 < Real.pi := Real.pi_gt_three
    have h_pi_lt : Real.pi < 4 := Real.pi_lt_four
    simp only [Nat.cast_zero, pow_zero, div_one] at h1 h2
    have h_art : Real.arctan 1 = Real.pi / 4 := Real.arctan_one
    rw [h_art] at h2
    have h_div : Real.pi / (Real.pi / 4) = 4 := by
      have : Real.pi ≠ 0 := Real.pi_ne_zero
      field_simp
    rw [h_div] at h2
    have hk_gt : 3 < k := by
      exact_mod_cast (by linarith : 3 < (k : ℝ))
    have hk_lt : k < 4 := by
      exact_mod_cast (by linarith : (k : ℝ) < 4)
    omega
  · have h_or : n < 60 ∨ 60 ≤ n := by omega
    rcases h_or with hn_lt | hn_ge
    · interval_cases n
      · exact subgoal_case_1
      · exact subgoal_case_2
      · exact subgoal_case_3
      · exact subgoal_case_4
      · exact subgoal_case_5
      · exact subgoal_case_6
      · exact subgoal_case_7
      · exact subgoal_case_8
      · exact subgoal_case_9
      · exact subgoal_case_10
      · exact subgoal_case_11
      · exact subgoal_case_12
      · exact subgoal_case_13
      · exact subgoal_case_14
      · exact subgoal_case_15
      · exact subgoal_case_16
      · exact subgoal_case_17
      · exact subgoal_case_18
      · exact subgoal_case_19
      · exact subgoal_case_20
      · exact subgoal_case_21
      · exact subgoal_case_22
      · exact subgoal_case_23
      · exact subgoal_case_24
      · exact subgoal_case_25
      · exact subgoal_case_26
      · exact subgoal_case_27
      · exact subgoal_case_28
      · exact subgoal_case_29
      · exact subgoal_case_30
      · exact subgoal_case_31
      · exact subgoal_case_32
      · exact subgoal_case_33
      · exact subgoal_case_34
      · exact subgoal_case_35
      · exact subgoal_case_36
      · exact subgoal_case_37
      · exact subgoal_case_38
      · exact subgoal_case_39
      · exact subgoal_case_40
      · exact subgoal_case_41
      · exact subgoal_case_42
      · exact subgoal_case_43
      · exact subgoal_case_44
      · exact subgoal_case_45
      · exact subgoal_case_46
      · exact subgoal_case_47
      · exact subgoal_case_48
      · exact subgoal_case_49
      · exact subgoal_case_50
      · exact subgoal_case_51
      · exact subgoal_case_52
      · exact subgoal_case_53
      · exact subgoal_case_54
      · exact subgoal_case_55
      · exact subgoal_case_56
      · exact subgoal_case_57
      · exact subgoal_case_58
      · exact subgoal_case_59
      · exact subgoal_case_60
    · intro ⟨k, h1, h2⟩
      let m := n - 60
      have hn_eq : n = 60 + m := by omega
      have h_pow_cast_real : (10 : ℝ) ^ (n + 1 : ℕ).cast = (10 : ℝ) ^ (n + 1) := rfl
      rw [h_pow_cast_real] at h1 h2
      have h_ind := (main_induction_new (m + 1)).left
      have h_eq : 60 + (m + 1) = n + 1 := by omega
      rw [h_eq] at h_ind
      exact h_ind ⟨k, h1, h2⟩
"""

with open("/workspace/leanproject/Submission/Spec.lean", "w") as f:
    f.writelines(kept_lines)
    f.write(new_code)
