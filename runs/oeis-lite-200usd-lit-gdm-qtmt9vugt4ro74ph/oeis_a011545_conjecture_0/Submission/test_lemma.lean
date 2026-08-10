import FormalConjectures.Util.ProblemImports

open Real Int

axiom upper_bound_interval_tight (n : ℕ) (hn : 1 ≤ n) :
  Real.pi / Real.arctan (1 / (10 : ℝ) ^ n) < Real.pi * (10 : ℝ) ^ n + 2 * (10 : ℝ) ^ (-n : ℤ)

axiom pi_div_arctan_gt (n : ℕ) (hn : 1 ≤ n) :
  Real.pi * (10 : ℝ)^n + 2 * (10 : ℝ)^(-(n + 2 : ℤ)) < Real.pi / Real.arctan (1 / (10 : ℝ)^n)

def S_prop (n : ℕ) : Prop :=
  ¬ ∃ (k : ℤ), Real.pi * (10 : ℝ) ^ n < (k : ℝ) ∧
    (k : ℝ) < Real.pi / Real.arctan (1 / (10 : ℝ) ^ n)

def T_prop (n : ℕ) : Prop :=
  ∀ (r : ℤ), 1 ≤ r → r ≤ 9 →
    ¬ ∃ (q : ℤ), Real.pi * (10 : ℝ) ^ n - (r : ℝ) / 10 < (q : ℝ) ∧
      (q : ℝ) < Real.pi * (10 : ℝ) ^ n - (r : ℝ) / 10 + 2 * (10 : ℝ) ^ (-(n + 2 : ℤ))

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
