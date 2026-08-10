import FormalConjectures.Util.ProblemImports

open Real Int

theorem pi_gt_60 : 3.141592653589793238462643383279502884197169399375105820974944592307816406286208 < Real.pi := sorry
theorem pi_lt_60 : Real.pi < 3.141592653589793238462643383279502884197169399375105820974944592307816406286210 := sorry

lemma pi_div_arctan_gt (n : ℕ) (hn : 1 ≤ n) :
    Real.pi * (10 : ℝ)^n + 2 * (10 : ℝ)^(-(n + 2 : ℤ)) < Real.pi / Real.arctan (1 / (10 : ℝ)^n) := sorry

lemma upper_bound_interval_tight (n : ℕ) (hn : 1 ≤ n) :
    Real.pi / Real.arctan (1 / (10 : ℝ) ^ n) < Real.pi * (10 : ℝ) ^ n + 2 * (10 : ℝ) ^ (-n : ℤ) := sorry

def S_prop (n : ℕ) : Prop :=
  ¬ ∃ (k : ℤ), Real.pi * (10 : ℝ) ^ n < (k : ℝ) ∧
    (k : ℝ) < Real.pi / Real.arctan (1 / (10 : ℝ) ^ n)

def T_prop_at (n : ℕ) (Y : ℕ) : Prop :=
  ∀ (r : ℤ), 1 ≤ r → r ≤ 9 →
    ¬ ∃ (q : ℤ), Real.pi * (10 : ℝ) ^ (n + Y) - (r : ℝ) / 10 < (q : ℝ) ∧
      (q : ℝ) < Real.pi * (10 : ℝ) ^ (n + Y) - (r : ℝ) / 10 + 2 * (10 : ℝ) ^ (-(n + Y + 4 : ℤ))

lemma subgoal_S_60 : S_prop 60 := sorry

lemma T_prop_at_zero_of_S_prop (n : ℕ) (hS : S_prop (n + 1)) (r : ℤ) (hr1 : 1 ≤ r) (hr2 : r ≤ 9) :
    ¬ ∃ (q : ℤ), Real.pi * (10 : ℝ) ^ n - (r : ℝ) / 10 < (q : ℝ) ∧
      (q : ℝ) < Real.pi * (10 : ℝ) ^ n - (r : ℝ) / 10 + 2 * (10 : ℝ) ^ (-(n + 4 : ℤ)) := by
  intro ⟨q, h1, h2⟩
  let k := 10 * q + r
  have h_k_eq : (k : ℝ) = 10 * (q : ℝ) + (r : ℝ) := by exact_mod_cast (by rfl : k = 10 * q + r)
  have h_pow_eq : (10 : ℝ) ^ (n + 1) = (10 : ℝ) ^ n * 10 := pow_succ 10 n
  have h_gt : Real.pi * (10 : ℝ) ^ (n + 1) < (k : ℝ) := by
    rw [h_pow_eq, h_k_eq]
    linarith
  have h_lt : (k : ℝ) < Real.pi / Real.arctan (1 / (10 : ℝ) ^ (n + 1)) := by
    have h_zpow_eq : (10 : ℝ) ^ (-(n + 4 : ℤ)) = (10 : ℝ) ^ (-(n + 3 : ℤ)) / 10 := by
      have : -(n + 4 : ℤ) = -(n + 3 : ℤ) - 1 := by omega
      rw [this, zpow_sub_one₀ (by norm_num)]
      ring
    have h_lt_relaxed : 10 * (q : ℝ) + (r : ℝ) < Real.pi * (10 : ℝ) ^ (n + 1) + 2 * (10 : ℝ) ^ (-(n + 4 : ℤ)) * 10 := by
      rw [h_pow_eq]
      linarith
    have h_ub := pi_div_arctan_gt (n + 1) (by omega)
    push_cast at h_ub
    have h_zpow_eq2 : (10 : ℝ) ^ (-(n + 1 + 2 : ℤ)) = (10 : ℝ) ^ (-(n + 3 : ℤ)) := by
      have : (n + 1 + 2 : ℤ) = n + 3 := by omega
      rw [this]
    rw [h_zpow_eq2] at h_ub
    rw [h_k_eq]
    rw [h_zpow_eq] at h_lt_relaxed
    linarith
  have h_contra : ∃ (k' : ℤ), Real.pi * (10 : ℝ) ^ (n + 1) < (k' : ℝ) ∧ (k' : ℝ) < Real.pi / Real.arctan (1 / (10 : ℝ) ^ (n + 1)) := ⟨k, h_gt, h_lt⟩
  exact hS h_contra

lemma subgoal_T_60_at_zero : T_prop_at 60 0 := by
  intro r hr1 hr2
  intro ⟨q, h1, h2⟩
  have h_pi_gt : 3.141592653589793238462643383279502884197169399375105820974944592307816406286208 < Real.pi := pi_gt_60
  have h_pi_lt : Real.pi < 3.141592653589793238462643383279502884197169399375105820974944592307816406286210 := pi_lt_60
  have h_pow : (10 : ℝ) ^ (60 + 0) = (10 : ℝ) ^ 60 := by norm_num
  have h_pow_60 : (10 : ℝ) ^ 60 = 1000000000000000000000000000000000000000000000000000000000000 := by norm_num
  have h_ten_neg : 2 * (10 : ℝ) ^ (-(60 + 0 + 2 : ℤ)) = 2 / 100000000000000000000000000000000000000000000000000000000000000 := by norm_num
  rw [h_pow] at h1 h2
  rw [h_pow_60] at h1 h2
  have h_or : r ≤ 5 ∨ r ≥ 6 := by omega
  rcases h_or with hr_le | hr_ge
  · -- r ≤ 5 case
    have h_lt_lim : (q : ℝ) < 3141592653589793238462643383279502884197169399375105820974945 := by
      calc (q : ℝ)
        _ < Real.pi * 1000000000000000000000000000000000000000000000000000000000000 - (r : ℝ) / 10 + 2 * (10 : ℝ) ^ (-(60 + 0 + 2 : ℤ)) := h2
        _ = Real.pi * 1000000000000000000000000000000000000000000000000000000000000 - (r : ℝ) / 10 + 2 / 100000000000000000000000000000000000000000000000000000000000000 := by rw [h_ten_neg]
        _ < 3.141592653589793238462643383279502884197169399375105820974944592307816406286210 * 1000000000000000000000000000000000000000000000000000000000000 - (r : ℝ) / 10 + 2 / 100000000000000000000000000000000000000000000000000000000000000 := by linarith [h_pi_lt]
        _ ≤ 3.141592653589793238462643383279502884197169399375105820974944592307816406286210 * 1000000000000000000000000000000000000000000000000000000000000 - 1 / 10 + 2 / 100000000000000000000000000000000000000000000000000000000000000 := by
          have : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
          linarith
        _ < 3141592653589793238462643383279502884197169399375105820974945 := by norm_num
    have h_gt_lim : 3141592653589793238462643383279502884197169399375105820974944 < (q : ℝ) := by
      calc (3141592653589793238462643383279502884197169399375105820974944 : ℝ)
        _ < 3.141592653589793238462643383279502884197169399375105820974944592307816406286208 * 1000000000000000000000000000000000000000000000000000000000000 - 5 / 10 := by norm_num
        _ ≤ 3.141592653589793238462643383279502884197169399375105820974944592307816406286208 * 1000000000000000000000000000000000000000000000000000000000000 - (r : ℝ) / 10 := by
          have : (r : ℝ) ≤ 5 := by exact_mod_cast hr_le
          linarith
        _ < Real.pi * 1000000000000000000000000000000000000000000000000000000000000 - (r : ℝ) / 10 := by linarith [h_pi_gt]
        _ < (q : ℝ) := h1
    have h_q_lt : q < 3141592653589793238462643383279502884197169399375105820974945 := by exact_mod_cast h_lt_lim
    have h_q_gt : q > 3141592653589793238462643383279502884197169399375105820974944 := by exact_mod_cast h_gt_lim
    omega
  · -- r ≥ 6 case
    have h_lt_lim : (q : ℝ) < 3141592653589793238462643383279502884197169399375105820974944 := by
      calc (q : ℝ)
        _ < Real.pi * 1000000000000000000000000000000000000000000000000000000000000 - (r : ℝ) / 10 + 2 * (10 : ℝ) ^ (-(60 + 0 + 2 : ℤ)) := h2
        _ = Real.pi * 1000000000000000000000000000000000000000000000000000000000000 - (r : ℝ) / 10 + 2 / 100000000000000000000000000000000000000000000000000000000000000 := by rw [h_ten_neg]
        _ < 3.141592653589793238462643383279502884197169399375105820974944592307816406286210 * 1000000000000000000000000000000000000000000000000000000000000 - (r : ℝ) / 10 + 2 / 100000000000000000000000000000000000000000000000000000000000000 := by linarith [h_pi_lt]
        _ ≤ 3.141592653589793238462643383279502884197169399375105820974944592307816406286210 * 1000000000000000000000000000000000000000000000000000000000000 - 6 / 10 + 2 / 100000000000000000000000000000000000000000000000000000000000000 := by
          have : (6 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr_ge
          linarith
        _ < 3141592653589793238462643383279502884197169399375105820974944 := by norm_num
    have h_gt_lim : 3141592653589793238462643383279502884197169399375105820974943 < (q : ℝ) := by
      calc (3141592653589793238462643383279502884197169399375105820974943 : ℝ)
        _ < 3.141592653589793238462643383279502884197169399375105820974944592307816406286208 * 1000000000000000000000000000000000000000000000000000000000000 - 9 / 10 := by norm_num
        _ ≤ 3.141592653589793238462643383279502884197169399375105820974944592307816406286208 * 1000000000000000000000000000000000000000000000000000000000000 - (r : ℝ) / 10 := by
          have : (r : ℝ) ≤ 9 := by exact_mod_cast hr2
          linarith
        _ < Real.pi * 1000000000000000000000000000000000000000000000000000000000000 - (r : ℝ) / 10 := by linarith [h_pi_gt]
        _ < (q : ℝ) := h1
    have h_q_lt : q < 3141592653589793238462643383279502884197169399375105820974944 := by exact_mod_cast h_lt_lim
    have h_q_gt : q > 3141592653589793238462643383279502884197169399375105820974943 := by exact_mod_cast h_gt_lim
    omega

lemma main_induction_new (m : ℕ) : S_prop (60 + m + 1) ∧ T_prop_at 60 m := by
  induction' m with m IH
  · constructor
    · intro ⟨k, h1, h2⟩
      have h_ub := upper_bound_interval_tight 61 (by norm_num)
      push_cast at h_ub
      have h_lt : (k : ℝ) < Real.pi * (10 : ℝ) ^ 61 + 2 * (10 : ℝ) ^ (-61 : ℤ) := by
        push_cast
        linarith [h2, h_ub]
      have h_gt : Real.pi * (10 : ℝ) ^ 61 < (k : ℝ) := h1
      have h_div_10 : k % 10 = 0 ∨ (∃ r, (1 ≤ r ∧ r ≤ 9) ∧ k = 10 * (k / 10) + r) := by
        have : k % 10 = 0 ∨ 1 ≤ k % 10 ∧ k % 10 ≤ 9 := by omega
        rcases this with hk0 | hk_rem
        · left; exact hk0
        · right; use k % 10; exact ⟨hk_rem, by omega⟩
      rcases h_div_10 with hk0 | ⟨r, ⟨hr1, hr2⟩, hq⟩
      · let q := k / 10
        have h_k_eq : k = 10 * q := by omega
        have h_q_gt : Real.pi * (10 : ℝ) ^ 60 < (q : ℝ) := by
          have : (k : ℝ) = 10 * (q : ℝ) := by exact_mod_cast h_k_eq
          have h_gt_simp : Real.pi * (10 : ℝ) ^ 61 < 10 * (q : ℝ) := by rwa [this] at h_gt
          have h_pow_eq_10_mul : (10 : ℝ) ^ 61 = (10 : ℝ) ^ 60 * 10 := rfl
          rw [h_pow_eq_10_mul] at h_gt_simp
          linarith [h_gt_simp]
        have h_q_lt : (q : ℝ) < Real.pi / Real.arctan (1 / (10 : ℝ) ^ 60) := by
          have : (k : ℝ) = 10 * (q : ℝ) := by exact_mod_cast h_k_eq
          have h_lt_simp : 10 * (q : ℝ) < Real.pi * (10 : ℝ) ^ 61 + 2 * (10 : ℝ) ^ (-61 : ℤ) := by rwa [this] at h_lt
          have h_pow_eq_10_mul : (10 : ℝ) ^ 61 = (10 : ℝ) ^ 60 * 10 := rfl
          have h_zpow_eq_10_div : (10 : ℝ) ^ (-61 : ℤ) = (10 : ℝ) ^ (-60 : ℤ) / 10 := by
            have : (-61 : ℤ) = -60 - 1 := by omega
            rw [this, zpow_sub_one₀ (by norm_num)]
            ring
          rw [h_pow_eq_10_mul, h_zpow_eq_10_div] at h_lt_simp
          have h_q_lt_linear : (q : ℝ) < Real.pi * (10 : ℝ) ^ 60 + 0.2 * (10 : ℝ) ^ (-60 : ℤ) := by linarith
          have h_arctan_lower := pi_div_arctan_gt 60 (by norm_num)
          have h_pow_neg_eq : (10 : ℝ) ^ (-(62 : ℤ)) = 0.01 * (10 : ℝ) ^ (-60 : ℤ) := by
            have : (-(62 : ℤ)) = (-60 : ℤ) + (-2 : ℤ) := by omega
            rw [this, zpow_add₀ (by norm_num)]
            ring
          rw [h_pow_neg_eq] at h_arctan_lower
          linarith [h_q_lt_linear, h_arctan_lower]
        have h_contra : ∃ (k' : ℤ), Real.pi * (10 : ℝ) ^ 60 < k'.cast ∧ k'.cast < Real.pi / Real.arctan (1 / (10 : ℝ) ^ 60) := ⟨q, h_q_gt, h_q_lt⟩
        exact subgoal_S_60 h_contra
      · let q := k / 10
        have h_k_eq : k = 10 * q + r := hq
        have : (k : ℝ) = 10 * (q : ℝ) + (r : ℝ) := by exact_mod_cast h_k_eq
        have h_gt' : Real.pi * (10 : ℝ) ^ 60 - (r : ℝ) / 10 < (q : ℝ) := by
          have h_gt_rw : Real.pi * (10 : ℝ) ^ 61 < 10 * (q : ℝ) + (r : ℝ) := by rwa [this] at h_gt
          have h_pow_eq : (10 : ℝ) ^ 61 = (10 : ℝ) ^ 60 * 10 := rfl
          rw [h_pow_eq] at h_gt_rw
          linarith
        have h_lt' : (q : ℝ) < Real.pi * (10 : ℝ) ^ 60 - (r : ℝ) / 10 + 2 * (10 : ℝ) ^ (-(62 : ℤ)) := by
          have h_lt_rw : 10 * (q : ℝ) + (r : ℝ) < Real.pi * (10 : ℝ) ^ 61 + 2 * (10 : ℝ) ^ (-61 : ℤ) := by rwa [this] at h_lt
          have h_pow_eq : (10 : ℝ) ^ 61 = (10 : ℝ) ^ 60 * 10 := rfl
          have h_zpow_eq : (10 : ℝ) ^ (-61 : ℤ) = (10 : ℝ) ^ (-(62 : ℤ)) * 10 := by
            have : (-61 : ℤ) = -(62 : ℤ) + 1 := by omega
            rw [this, zpow_add₀ (by norm_num)]
            ring
          rw [h_pow_eq, h_zpow_eq] at h_lt_rw
          linarith
        have h_contra : ∃ (q' : ℤ), Real.pi * (10 : ℝ) ^ 60 - (r : ℝ) / 10 < (q' : ℝ) ∧
            (q' : ℝ) < Real.pi * (10 : ℝ) ^ 60 - (r : ℝ) / 10 + 2 * (10 : ℝ) ^ (-(62 : ℤ)) := ⟨q, h_gt', h_lt'⟩
        exact subgoal_T_60_at_zero r hr1 hr2 h_contra
    · exact subgoal_T_60_at_zero
  · rcases IH with ⟨IH_S, IH_T⟩
    have h_T_succ : T_prop_at 60 (m + 1) := T_prop_at_zero_of_S_prop (60 + m + 1) IH_S
    constructor
    · intro ⟨k, h1, h2⟩
      let n := 60 + m + 1
      have h_ub := upper_bound_interval_tight (n + 1) (by omega)
      push_cast at h_ub
      have h_lt : (k : ℝ) < Real.pi * (10 : ℝ) ^ (n + 1) + 2 * (10 : ℝ) ^ (-(((n + 1 : ℕ) : ℤ))) := by
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
          have h_lt_simp : 10 * (q : ℝ) < Real.pi * (10 : ℝ) ^ (n + 1) + 2 * (10 : ℝ) ^ (-(((n + 1 : ℕ) : ℤ))) := by rwa [this] at h_lt
          have h_pow_eq_10_mul : (10 : ℝ) ^ (n + 1) = (10 : ℝ) ^ n * 10 := pow_succ 10 n
          have h_zpow_eq_10_div : (10 : ℝ) ^ (-(((n + 1 : ℕ) : ℤ))) = (10 : ℝ) ^ (-n : ℤ) / 10 := by
            have : -(((n + 1 : ℕ) : ℤ)) = -n - 1 := by omega
            rw [this, zpow_sub_one₀ (by norm_num)]
            ring
          rw [h_pow_eq_10_mul, h_zpow_eq_10_div] at h_lt_simp
          have h_q_lt_linear : (q : ℝ) < Real.pi * (10 : ℝ) ^ n + 0.2 * (10 : ℝ) ^ (-n : ℤ) := by linarith
          have h_arctan_lower := pi_div_arctan_gt n (by omega)
          push_cast at h_arctan_lower
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
          have h_lt_rw : 10 * (q : ℝ) + (r : ℝ) < Real.pi * (10 : ℝ) ^ (n + 1) + 2 * (10 : ℝ) ^ (-(((n + 1 : ℕ) : ℤ))) := by rwa [this] at h_lt
          have h_pow_eq : (10 : ℝ) ^ (n + 1) = (10 : ℝ) ^ n * 10 := pow_succ 10 n
          have h_zpow_eq : (10 : ℝ) ^ (-(((n + 1 : ℕ) : ℤ))) = (10 : ℝ) ^ (-(n + 2 : ℤ)) * 10 := by
            have : -(((n + 1 : ℕ) : ℤ)) = -(n + 2 : ℤ) + 1 := by omega
            rw [this, zpow_add₀ (by norm_num)]
            ring
          rw [h_pow_eq, h_zpow_eq] at h_lt_rw
          linarith
        have h_contra : ∃ (q' : ℤ), Real.pi * (10 : ℝ) ^ n - (r : ℝ) / 10 < (q' : ℝ) ∧
            (q' : ℝ) < Real.pi * (10 : ℝ) ^ n - (r : ℝ) / 10 + 2 * (10 : ℝ) ^ (-(n + 2 : ℤ)) := ⟨q, h_gt', h_lt'⟩
        exact h_T_succ r hr1 hr2 h_contra
    · exact h_T_succ
