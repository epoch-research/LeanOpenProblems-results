import FormalConjectures.Util.ProblemImports

open Real Int

def S_prop (n : ℕ) : Prop :=
  ¬ ∃ (k : ℤ), Real.pi * (10 : ℝ) ^ n < (k : ℝ) ∧
    (k : ℝ) < Real.pi * (10 : ℝ) ^ n + 2 * (10 : ℝ) ^ (-n : ℤ)

def T_prop (n : ℕ) : Prop :=
  ∀ (r : ℤ), 1 ≤ r → r ≤ 9 →
    ¬ ∃ (q : ℤ), Real.pi * (10 : ℝ) ^ n - (r : ℝ) / 10 < (q : ℝ) ∧
      (q : ℝ) < Real.pi * (10 : ℝ) ^ n - (r : ℝ) / 10 + 2 * (10 : ℝ) ^ (-(n + 2 : ℤ))

lemma main_induction_step (n : ℕ) (IH : S_prop n ∧ T_prop n) : S_prop (n + 1) ∧ T_prop (n + 1) := by
  have hS : S_prop (n + 1) := by
    intro ⟨k, h1, h2⟩
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
        have h_gt_simp : Real.pi * (10 : ℝ) ^ (n + 1) < 10 * (q : ℝ) := by rwa [this] at h1
        have h_pow_eq_10_mul : (10 : ℝ) ^ (n + 1) = (10 : ℝ) ^ n * 10 := pow_succ 10 n
        rw [h_pow_eq_10_mul] at h_gt_simp
        linarith [h_gt_simp]
      have h_q_lt : (q : ℝ) < Real.pi * (10 : ℝ) ^ n + 2 * (10 : ℝ) ^ (-n : ℤ) := by
        have : (k : ℝ) = 10 * (q : ℝ) := by exact_mod_cast h_k_eq
        have h_lt_simp : 10 * (q : ℝ) < Real.pi * (10 : ℝ) ^ (n + 1) + 2 * (10 : ℝ) ^ (-((n + 1 : ℕ) : ℤ)) := by rwa [this] at h2
        have h_pow_eq_10_mul : (10 : ℝ) ^ (n + 1) = (10 : ℝ) ^ n * 10 := pow_succ 10 n
        have h_zpow_eq_10_div : (10 : ℝ) ^ (-((n + 1 : ℕ) : ℤ)) = (10 : ℝ) ^ (-n : ℤ) / 10 := by
          have : -((n + 1 : ℕ) : ℤ) = -n - 1 := by omega
          rw [this, zpow_sub_one₀ (by norm_num)]
          ring
        rw [h_pow_eq_10_mul, h_zpow_eq_10_div] at h_lt_simp
        linarith
      have h_contra : ∃ (k' : ℤ), Real.pi * (10 : ℝ) ^ n < k'.cast ∧ k'.cast < Real.pi * (10 : ℝ) ^ n + 2 * (10 : ℝ) ^ (-n : ℤ) := ⟨q, h_q_gt, h_q_lt⟩
      exact IH.left h_contra
    · let q := k / 10
      have h_k_eq : k = 10 * q + r := hq
      have : (k : ℝ) = 10 * (q : ℝ) + (r : ℝ) := by exact_mod_cast h_k_eq
      have h_gt' : Real.pi * (10 : ℝ) ^ n - (r : ℝ) / 10 < (q : ℝ) := by
        have h_gt_rw : Real.pi * (10 : ℝ) ^ (n + 1) < 10 * (q : ℝ) + (r : ℝ) := by rwa [this] at h1
        have h_pow_eq : (10 : ℝ) ^ (n + 1) = (10 : ℝ) ^ n * 10 := pow_succ 10 n
        rw [h_pow_eq] at h_gt_rw
        linarith
      have h_lt' : (q : ℝ) < Real.pi * (10 : ℝ) ^ n - (r : ℝ) / 10 + 2 * (10 : ℝ) ^ (-(n + 2 : ℤ)) := by
        have h_lt_rw : 10 * (q : ℝ) + (r : ℝ) < Real.pi * (10 : ℝ) ^ (n + 1) + 2 * (10 : ℝ) ^ (-((n + 1 : ℕ) : ℤ)) := by rwa [this] at h2
        have h_pow_eq : (10 : ℝ) ^ (n + 1) = (10 : ℝ) ^ n * 10 := pow_succ 10 n
        have h_zpow_eq : (10 : ℝ) ^ (-((n + 1 : ℕ) : ℤ)) = (10 : ℝ) ^ (-(n + 2 : ℤ) + 1) := by
          have : -((n + 1 : ℕ) : ℤ) = -(n + 2 : ℤ) + 1 := by omega
          rw [this]
        rw [h_pow_eq, h_zpow_eq] at h_lt_rw
        rw [zpow_add₀ (by norm_num)] at h_lt_rw
        linarith
      have h_contra : ∃ (q' : ℤ), Real.pi * (10 : ℝ) ^ n - (r : ℝ) / 10 < (q' : ℝ) ∧
          (q' : ℝ) < Real.pi * (10 : ℝ) ^ n - (r : ℝ) / 10 + 2 * (10 : ℝ) ^ (-(n + 2 : ℤ)) := ⟨q, h_gt', h_lt'⟩
      exact IH.right r hr1 hr2 h_contra

  have hT : T_prop (n + 1) := by
    intro r hr1 hr2
    intro ⟨q, h1, h2⟩
    let k := 10 * q + r
    have hk_eq : (k : ℝ) = 10 * (q : ℝ) + (r : ℝ) := by exact_mod_cast (by rfl : k = 10 * q + r)
    have h_gt' : Real.pi * (10 : ℝ) ^ (n + 1) < (k : ℝ) := by
      rw [hk_eq]
      have h_pow_succ : (10 : ℝ) ^ (n + 1) = (10 : ℝ) ^ n * 10 := pow_succ 10 n
      rw [h_pow_succ] at h1
      linarith
    have h_lt' : (k : ℝ) < Real.pi * (10 : ℝ) ^ (n + 1) + 2 * (10 : ℝ) ^ (-(n + 1 : ℤ)) := by
      rw [hk_eq]
      have h_pow_succ : (10 : ℝ) ^ (n + 1) = (10 : ℝ) ^ n * 10 := pow_succ 10 n
      have h_zpow_rel : (10 : ℝ) ^ (-((n + 1 : ℕ) + 2 : ℤ)) * 10 = (10 : ℝ) ^ (-(n + 1 : ℤ)) := by
        have : -((n + 1 : ℕ) + 2 : ℤ) = -(n + 1 : ℤ) - 1 := by omega
        rw [this, zpow_sub_one₀ (by norm_num)]
        ring
      have h_lt_relaxed : 10 * (q : ℝ) + (r : ℝ) < Real.pi * (10 : ℝ) ^ (n + 1) * 10 + 2 * (10 : ℝ) ^ (-((n + 1 : ℕ) + 2 : ℤ)) * 10 := by
        have h_pow_succ2 : (10 : ℝ) ^ (n + 1 + 1) = (10 : ℝ) ^ (n + 1) * 10 := pow_succ 10 (n + 1)
        -- h2 is about n+1
        -- q < pi * 10^(n+1) - r/10 + 2 * 10^-(n + 1 + 2)
        -- 10 * q + r < pi * 10^(n+1) * 10 + 2 * 10^-(n + 3) * 10
        linarith
      rw [h_zpow_rel] at h_lt_relaxed
      linarith
    have h_contra : ∃ k', Real.pi * (10 : ℝ) ^ (n + 1) < k'.cast ∧ k'.cast < Real.pi * (10 : ℝ) ^ (n + 1) + 2 * (10 : ℝ) ^ (-(n + 1 : ℤ)) := ⟨k, h_gt', h_lt'⟩
    exact hS h_contra
  exact ⟨hS, hT⟩
