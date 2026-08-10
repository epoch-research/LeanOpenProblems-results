import os

# Read the original Spec.lean up to line 1792
header_lines = []
with open("/workspace/leanproject/Submission/Spec.lean.bak", "r") as f:
    for i in range(1792):
        line = f.readline()
        if not line:
            break
        header_lines.append(line)

new_content = "".join(header_lines)

# Append the new definitions and proofs
new_content += """
def T_prop (n : ℕ) : Prop :=
  ∀ (r : ℤ), 1 ≤ r → r ≤ 9 →
    ¬ ∃ (q : ℤ), Real.pi * (10 : ℝ) ^ n - (r : ℝ) / 10 < (q : ℝ) ∧
      (q : ℝ) < Real.pi * (10 : ℝ) ^ n - (r : ℝ) / 10 + 2 * (10 : ℝ) ^ (-(n + 2 : ℤ))

def S_prop (n : ℕ) : Prop :=
  ¬ ∃ (k : ℤ), Real.pi * (10 : ℝ) ^ n < (k : ℝ) ∧
    (k : ℝ) < Real.pi / Real.arctan (1 / (10 : ℝ) ^ n)

lemma subgoal_T_60 : T_prop 60 := by
  intro r hr1 hr2
  intro ⟨q, h1, h2⟩
  have h_pi_gt : 3.141592653589793238462643383279502884197169399375105820974944592307816406286208 < Real.pi := pi_gt_60
  have h_pi_lt : Real.pi < 3.141592653589793238462643383279502884197169399375105820974944592307816406286210 := pi_lt_60
  have h_pow_cast_real_60 : (10 : ℝ) ^ 60 = 1000000000000000000000000000000000000000000000000000000000000 := by norm_num
  have h_ten_neg_val : 2 * (10 : ℝ) ^ (-62 : ℤ) = 2 / 100000000000000000000000000000000000000000000000000000000000000 := by norm_num
  have h_lt_62 : (q : ℝ) < Real.pi * (10 : ℝ) ^ 60 - (r : ℝ) / 10 + 2 * (10 : ℝ) ^ (-62 : ℤ) := h2
  have h_gt_62 : Real.pi * (10 : ℝ) ^ 60 - (r : ℝ) / 10 < (q : ℝ) := h1
  interval_cases r
  · have hk_gt : 3141592653589793238462643383279502884197169399375105820974944 < q := by
      exact_mod_cast (by linarith : (3141592653589793238462643383279502884197169399375105820974944 : ℝ) < (q : ℝ))
    have hk_lt : q < 3141592653589793238462643383279502884197169399375105820974945 := by
      exact_mod_cast (by linarith : (q : ℝ) < (3141592653589793238462643383279502884197169399375105820974945 : ℝ))
    omega
  · have hk_gt : 3141592653589793238462643383279502884197169399375105820974944 < q := by
      exact_mod_cast (by linarith : (3141592653589793238462643383279502884197169399375105820974944 : ℝ) < (q : ℝ))
    have hk_lt : q < 3141592653589793238462643383279502884197169399375105820974945 := by
      exact_mod_cast (by linarith : (q : ℝ) < (3141592653589793238462643383279502884197169399375105820974945 : ℝ))
    omega
  · have hk_gt : 3141592653589793238462643383279502884197169399375105820974944 < q := by
      exact_mod_cast (by linarith : (3141592653589793238462643383279502884197169399375105820974944 : ℝ) < (q : ℝ))
    have hk_lt : q < 3141592653589793238462643383279502884197169399375105820974945 := by
      exact_mod_cast (by linarith : (q : ℝ) < (3141592653589793238462643383279502884197169399375105820974945 : ℝ))
    omega
  · have hk_gt : 3141592653589793238462643383279502884197169399375105820974944 < q := by
      exact_mod_cast (by linarith : (3141592653589793238462643383279502884197169399375105820974944 : ℝ) < (q : ℝ))
    have hk_lt : q < 3141592653589793238462643383279502884197169399375105820974945 := by
      exact_mod_cast (by linarith : (q : ℝ) < (3141592653589793238462643383279502884197169399375105820974945 : ℝ))
    omega
  · have hk_gt : 3141592653589793238462643383279502884197169399375105820974944 < q := by
      exact_mod_cast (by linarith : (3141592653589793238462643383279502884197169399375105820974944 : ℝ) < (q : ℝ))
    have hk_lt : q < 3141592653589793238462643383279502884197169399375105820974945 := by
      exact_mod_cast (by linarith : (q : ℝ) < (3141592653589793238462643383279502884197169399375105820974945 : ℝ))
    omega
  · have hk_gt : 3141592653589793238462643383279502884197169399375105820974943 < q := by
      exact_mod_cast (by linarith : (3141592653589793238462643383279502884197169399375105820974943 : ℝ) < (q : ℝ))
    have hk_lt : q < 3141592653589793238462643383279502884197169399375105820974944 := by
      exact_mod_cast (by linarith : (q : ℝ) < (3141592653589793238462643383279502884197169399375105820974944 : ℝ))
    omega
  · have hk_gt : 3141592653589793238462643383279502884197169399375105820974943 < q := by
      exact_mod_cast (by linarith : (3141592653589793238462643383279502884197169399375105820974943 : ℝ) < (q : ℝ))
    have hk_lt : q < 3141592653589793238462643383279502884197169399375105820974944 := by
      exact_mod_cast (by linarith : (q : ℝ) < (3141592653589793238462643383279502884197169399375105820974944 : ℝ))
    omega
  · have hk_gt : 3141592653589793238462643383279502884197169399375105820974943 < q := by
      exact_mod_cast (by linarith : (3141592653589793238462643383279502884197169399375105820974943 : ℝ) < (q : ℝ))
    have hk_lt : q < 3141592653589793238462643383279502884197169399375105820974944 := by
      exact_mod_cast (by linarith : (q : ℝ) < (3141592653589793238462643383279502884197169399375105820974944 : ℝ))
    omega
  · have hk_gt : 3141592653589793238462643383279502884197169399375105820974943 < q := by
      exact_mod_cast (by linarith : (3141592653589793238462643383279502884197169399375105820974943 : ℝ) < (q : ℝ))
    have hk_lt : q < 3141592653589793238462643383279502884197169399375105820974944 := by
      exact_mod_cast (by linarith : (q : ℝ) < (3141592653589793238462643383279502884197169399375105820974944 : ℝ))
    omega

lemma subgoal_S_60 : S_prop 60 := by
  have h := subgoal_case_60
  exact h

lemma main_induction_step (n : ℕ) (hn : 60 ≤ n) (IH : S_prop n ∧ T_prop n) : S_prop (n + 1) ∧ T_prop (n + 1) := by
  have hn_pos : 1 ≤ n := by omega
  have hS : S_prop (n + 1) := by
    intro ⟨k, h1, h2⟩
    have h_ub := upper_bound_interval_tight (n + 1) (by omega)
    have h2_cast : (k : ℝ) < Real.pi / Real.arctan (1 / (10 : ℝ) ^ (n + 1)) := by
      have : ((n + 1 : ℕ) : ℝ) = (n + 1 : ℕ) := rfl
      exact h2
    have h_lt : (k : ℝ) < Real.pi * (10 : ℝ) ^ (n + 1) + 2 * (10 : ℝ) ^ (-((n + 1 : ℕ) : ℤ)) := by
      linarith [h2_cast, h_ub]
    have h_gt : Real.pi * (10 : ℝ) ^ (n + 1) < (k : ℝ) := by
      have : ((n + 1 : ℕ) : ℝ) = (n + 1 : ℕ) := rfl
      exact h1
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
        have h_arctan_lower := pi_div_arctan_gt n hn_pos
        have h_pow_neg_eq : (10 : ℝ) ^ (-( (n : ℤ) + 2 )) = 0.01 * (10 : ℝ) ^ (- (n : ℤ)) := by
          have h_exp : -( (n : ℤ) + 2 ) = - (n : ℤ) + (-2 : ℤ) := by ring
          rw [h_exp, zpow_add₀ (by norm_num)]
          ring
        rw [h_pow_neg_eq] at h_arctan_lower
        linarith [h_q_lt_linear, h_arctan_lower]
      have h_contra : ∃ (k' : ℤ), Real.pi * (10 : ℝ) ^ n < k'.cast ∧ k'.cast < Real.pi / Real.arctan (1 / (10 : ℝ) ^ n) := by
        use q
        exact ⟨h_q_gt, h_q_lt⟩
      exact IH.left h_contra
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
          (q' : ℝ) < Real.pi * (10 : ℝ) ^ n - (r : ℝ) / 10 + 2 * (10 : ℝ) ^ (-(n + 2 : ℤ)) := by
        use q
        exact ⟨h_gt', h_lt'⟩
      exact IH.right r hr1 hr2 h_contra
      
  have hT : T_prop (n + 1) := by
    intro r' hr1' hr2'
    intro ⟨q', h1', h2'⟩
    let k' := 10 * q' + r'
    have : (k' : ℝ) = 10 * (q' : ℝ) + (r' : ℝ) := by exact_mod_cast (by rfl : k' = 10 * q' + r')
    have h_pow_eq : (10 : ℝ) ^ (n + 1) = (10 : ℝ) ^ n * 10 := pow_succ 10 n
    have h_zpow_eq : (10 : ℝ) ^ (-((n + 1) : ℤ)) = (10 : ℝ) ^ (-(n + 2 : ℤ)) * 10 := by
      have : -((n + 1) : ℤ) = -(n + 2 : ℤ) + 1 := by omega
      rw [this, zpow_add₀ (by norm_num)]
      ring
    have h_pi_pos : 0 < Real.pi := by linarith [Real.pi_gt_three]
    have h_pow_pos : 0 < (10 : ℝ) ^ n := by positivity
    have h_prod_pos : 0 < Real.pi * (10 : ℝ) ^ n * 10 := by linarith [mul_pos h_pi_pos h_pow_pos]
    have h_ten_pos : 0 < (10 : ℝ) ^ (-2 - (n : ℤ)) := by positivity
    have h_inv : (10 : ℝ)⁻¹ = 1 / 10 := by norm_num
    have h_gt' : Real.pi * (10 : ℝ) ^ (n + 1) < (k' : ℝ) := by
      have h1_rw := h1'
      rw [h_pow_eq] at h1_rw
      rw [this, h_pow_eq]
      linarith [h1_rw, h_prod_pos]
    have h_lt' : (k' : ℝ) < Real.pi * (10 : ℝ) ^ (n + 1) + 2 * (10 : ℝ) ^ (-((n + 1) : ℤ)) := by
      have h2_rw := h2'
      have h_exp : (-(((n + 1 : ℕ) : ℤ) + 2)) = -(n + 2 : ℤ) - 1 := by omega
      rw [h_exp] at h2_rw
      rw [h_pow_eq] at h2_rw
      rw [this, h_pow_eq, h_zpow_eq]
      rw [zpow_sub_one₀ (by norm_num)] at h2_rw
      rw [h_inv] at h2_rw
      ring_nf at h2_rw
      ring_nf
      linarith [h2_rw, h_ten_pos]
    have h_div_10 : k' % 10 = 0 ∨ (∃ r, (1 ≤ r ∧ r ≤ 9) ∧ k' = 10 * (k' / 10) + r) := by
      have : k' % 10 = 0 ∨ 1 ≤ k' % 10 ∧ k' % 10 ≤ 9 := by omega
      rcases this with hk0 | hk_rem
      · left; exact hk0
      · right; use k' % 10; exact ⟨hk_rem, by omega⟩
    rcases h_div_10 with hk0 | ⟨r, ⟨hr1, hr2⟩, hq⟩
    · let q'' := k' / 10
      have h_k_eq : k' = 10 * q'' := by omega
      have h_q_gt : Real.pi * (10 : ℝ) ^ n < (q'' : ℝ) := by
        have : (k' : ℝ) = 10 * (q'' : ℝ) := by exact_mod_cast h_k_eq
        have h_gt_simp : Real.pi * (10 : ℝ) ^ (n + 1) < 10 * (q'' : ℝ) := by rwa [this] at h_gt'
        rw [h_pow_eq] at h_gt_simp
        linarith [h_gt_simp]
      have h_q_lt : (q'' : ℝ) < Real.pi / Real.arctan (1 / (10 : ℝ) ^ n) := by
        have : (k' : ℝ) = 10 * (q'' : ℝ) := by exact_mod_cast h_k_eq
        have h_lt_simp : 10 * (q'' : ℝ) < Real.pi * (10 : ℝ) ^ (n + 1) + 2 * (10 : ℝ) ^ (-((n + 1) : ℤ)) := by rwa [this] at h_lt'
        have h_zpow_eq_10_div : (10 : ℝ) ^ (-((n + 1) : ℤ)) = (10 : ℝ) ^ (-n : ℤ) / 10 := by
          have : -((n + 1) : ℤ) = -n - 1 := by omega
          rw [this, zpow_sub_one₀ (by norm_num)]
          ring
        rw [h_pow_eq, h_zpow_eq_10_div] at h_lt_simp
        have h_q_lt_linear : (q'' : ℝ) < Real.pi * (10 : ℝ) ^ n + 0.2 * (10 : ℝ) ^ (-n : ℤ) := by linarith
        have h_arctan_lower := pi_div_arctan_gt n hn_pos
        have h_pow_neg_eq : (10 : ℝ) ^ (-( (n : ℤ) + 2 )) = 0.01 * (10 : ℝ) ^ (- (n : ℤ)) := by
          have h_exp : -( (n : ℤ) + 2 ) = - (n : ℤ) + (-2 : ℤ) := by ring
          rw [h_exp, zpow_add₀ (by norm_num)]
          ring
        rw [h_pow_neg_eq] at h_arctan_lower
        linarith [h_q_lt_linear, h_arctan_lower]
      have h_contra : ∃ (k'' : ℤ), Real.pi * (10 : ℝ) ^ n < k''.cast ∧ k''.cast < Real.pi / Real.arctan (1 / (10 : ℝ) ^ n) := by
        use q''
        exact ⟨h_q_gt, h_q_lt⟩
      exact IH.left h_contra
    · let q'' := k' / 10
      have h_k_eq : k' = 10 * q'' + r := hq
      have : (k' : ℝ) = 10 * (q'' : ℝ) + (r : ℝ) := by exact_mod_cast h_k_eq
      have h_gt'' : Real.pi * (10 : ℝ) ^ n - (r : ℝ) / 10 < (q'' : ℝ) := by
        have h_gt_rw : Real.pi * (10 : ℝ) ^ (n + 1) < 10 * (q'' : ℝ) + (r : ℝ) := by rwa [this] at h_gt'
        rw [h_pow_eq] at h_gt_rw
        linarith
      have h_lt'' : (q'' : ℝ) < Real.pi * (10 : ℝ) ^ n - (r : ℝ) / 10 + 2 * (10 : ℝ) ^ (-(n + 2 : ℤ)) := by
        have h_lt_rw : 10 * (q'' : ℝ) + (r : ℝ) < Real.pi * (10 : ℝ) ^ (n + 1) + 2 * (10 : ℝ) ^ (-((n + 1) : ℤ)) := by rwa [this] at h_lt'
        rw [h_pow_eq, h_zpow_eq] at h_lt_rw
        linarith
      have h_contra : ∃ (q'' : ℤ), Real.pi * (10 : ℝ) ^ n - (r : ℝ) / 10 < (q'' : ℝ) ∧
          (q'' : ℝ) < Real.pi * (10 : ℝ) ^ n - (r : ℝ) / 10 + 2 * (10 : ℝ) ^ (-(n + 2 : ℤ)) := by
        use q''
        exact ⟨h_gt'', h_lt''⟩
      exact IH.right r hr1 hr2 h_contra
  exact ⟨hS, hT⟩

lemma main_induction (m : ℕ) : S_prop (60 + m) ∧ T_prop (60 + m) := by
  induction' m with m IH
  · exact ⟨subgoal_S_60, subgoal_T_60⟩
  · exact main_induction_step (60 + m) (by omega) IH

lemma general_induction (n : ℕ) (hn : 60 ≤ n) : S_prop n ∧ T_prop n := by
  have h_m : ∃ m, n = 60 + m := by
    use n - 60
    omega
  rcases h_m with ⟨m, rfl⟩
  exact main_induction m

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
      have h_S_prop := (general_induction (n + 1) (by omega)).left
      have h_contra : ∃ (k' : ℤ), Real.pi * (10 : ℝ) ^ (n + 1) < (k' : ℝ) ∧ (k' : ℝ) < Real.pi / Real.arctan (1 / (10 : ℝ) ^ (n + 1)) := by
        use k
        exact_mod_cast ⟨h1, h2⟩
      exact h_S_prop h_contra
"""

with open("/workspace/leanproject/Submission/Spec.lean", "w") as f:
    f.write(new_content)

print("edit_spec.py executed successfully.")
