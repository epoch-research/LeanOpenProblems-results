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

def T_prop (n : ℕ) : Prop :=
  ∀ (R : ℝ), 0 < R → R < 1 →
    ¬ ∃ (q : ℤ), Real.pi * (10 : ℝ) ^ n - R < (q : ℝ) ∧
      (q : ℝ) < Real.pi * (10 : ℝ) ^ n - R + 2 * (10 : ℝ) ^ (-(n + 2 : ℤ))

lemma main_induction_step (n : ℕ) (hn : 60 ≤ n) (IH : S_prop n ∧ T_prop n) :
    S_prop (n + 1) ∧ T_prop (n + 1) := by
  have hn_pos : 1 ≤ n := by omega
  constructor
  · intro ⟨k, h1, h2⟩
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
      exact IH.left ⟨q, h_q_gt, h_q_lt⟩
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
      have h_R_pos : 0 < (r : ℝ) / 10 := by
        have : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
        linarith
      have h_R_lt : (r : ℝ) / 10 < 1 := by
        have : (r : ℝ) < 10 := by exact_mod_cast (by omega : r < 10)
        linarith
      exact IH.right ((r : ℝ) / 10) h_R_pos h_R_lt ⟨q, h_gt', h_lt'⟩

  · intro R' hR1' hR2' ⟨q', h1', h2'⟩
    have h_div_10 : q' % 10 = 0 ∨ (∃ r'', (1 ≤ r'' ∧ r'' ≤ 9) ∧ q' = 10 * (q' / 10) + r'') := by
      have : q' % 10 = 0 ∨ 1 ≤ q' % 10 ∧ q' % 10 ≤ 9 := by omega
      rcases this with hk0 | hk_rem
      · left; exact hk0
      · right; use q' % 10; exact ⟨hk_rem, by omega⟩
    rcases h_div_10 with hk0 | ⟨r'', ⟨hr1'', hr2''⟩, hq⟩
    · let q'' := q' / 10
      have h_q_eq : q' = 10 * q'' := by omega
      have : (q' : ℝ) = 10 * (q'' : ℝ) := by exact_mod_cast h_q_eq
      have h_gt' : Real.pi * (10 : ℝ) ^ n - R' / 10 < (q'' : ℝ) := by
        have h_pow_eq : (10 : ℝ) ^ (n + 1) = (10 : ℝ) ^ n * 10 := pow_succ 10 n
        have h_gt_rw : Real.pi * (10 : ℝ) ^ (n + 1) - R' < (q' : ℝ) := h1'
        rw [this, h_pow_eq] at h_gt_rw
        linarith
      have h_lt' : (q'' : ℝ) < Real.pi * (10 : ℝ) ^ n - R' / 10 + 2 * (10 : ℝ) ^ (-(n + 2 : ℤ)) := by
        have h_pow_eq : (10 : ℝ) ^ (n + 1) = (10 : ℝ) ^ n * 10 := pow_succ 10 n
        have h_lt_rw : (q' : ℝ) < Real.pi * (10 : ℝ) ^ (n + 1) - R' + 2 * (10 : ℝ) ^ (-(((n + 1 : ℕ) : ℤ) + 2)) := h2'
        have h_zpow_eq : (10 : ℝ) ^ (-(((n + 1 : ℕ) : ℤ) + 2)) = (10 : ℝ) ^ (-(n + 2 : ℤ)) / 10 := by
          have : -(((n + 1 : ℕ) : ℤ) + 2) = -(n + 2 : ℤ) - 1 := by omega
          rw [this, zpow_sub_one₀ (by norm_num)]
          ring
        rw [this, h_pow_eq, h_zpow_eq] at h_lt_rw
        linarith
      have h_R_pos : 0 < R' / 10 := by linarith
      have h_R_lt : R' / 10 < 1 := by linarith
      exact IH.right (R' / 10) h_R_pos h_R_lt ⟨q'', h_gt', h_lt'⟩
    · let q'' := q' / 10
      have h_q_eq : q' = 10 * q'' + r'' := hq
      have : (q' : ℝ) = 10 * (q'' : ℝ) + (r'' : ℝ) := by exact_mod_cast h_q_eq
      have h_gt' : Real.pi * (10 : ℝ) ^ n - (R' + r'') / 10 < (q'' : ℝ) := by
        have h_pow_eq : (10 : ℝ) ^ (n + 1) = (10 : ℝ) ^ n * 10 := pow_succ 10 n
        have h_gt_rw : Real.pi * (10 : ℝ) ^ (n + 1) - R' < (q' : ℝ) := h1'
        rw [this, h_pow_eq] at h_gt_rw
        linarith
      have h_lt' : (q'' : ℝ) < Real.pi * (10 : ℝ) ^ n - (R' + r'') / 10 + 2 * (10 : ℝ) ^ (-(n + 2 : ℤ)) := by
        have h_pow_eq : (10 : ℝ) ^ (n + 1) = (10 : ℝ) ^ n * 10 := pow_succ 10 n
        have h_lt_rw : (q' : ℝ) < Real.pi * (10 : ℝ) ^ (n + 1) - R' + 2 * (10 : ℝ) ^ (-(((n + 1 : ℕ) : ℤ) + 2)) := h2'
        have h_zpow_eq : (10 : ℝ) ^ (-(((n + 1 : ℕ) : ℤ) + 2)) = (10 : ℝ) ^ (-(n + 2 : ℤ)) / 10 := by
          have : -(((n + 1 : ℕ) : ℤ) + 2) = -(n + 2 : ℤ) - 1 := by omega
          rw [this, zpow_sub_one₀ (by norm_num)]
          ring
        rw [this, h_pow_eq, h_zpow_eq] at h_lt_rw
        linarith
      have h_R_pos : 0 < (R' + r'') / 10 := by
        have : (0 : ℝ) < (r'' : ℝ) := by exact_mod_cast (by omega : 0 < r'')
        linarith
      have h_R_lt : (R' + r'') / 10 < 1 := by
        have : (r'' : ℝ) ≤ 9 := by exact_mod_cast hr2''
        linarith
      exact IH.right ((R' + r'') / 10) h_R_pos h_R_lt ⟨q'', h_gt', h_lt'⟩
