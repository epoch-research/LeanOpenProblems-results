import FormalConjectures.Util.ProblemImports

open Real Int

def S_prop (n : ℕ) : Prop :=
  ¬ ∃ (k : ℤ), Real.pi * (10 : ℝ) ^ n < (k : ℝ) ∧
    (k : ℝ) < Real.pi / Real.arctan (1 / (10 : ℝ) ^ n)

lemma pi_div_arctan_gt (n : ℕ) (hn : 1 ≤ n) :
    Real.pi * (10 : ℝ)^n + 2 * (10 : ℝ)^(-(n + 2 : ℤ)) < Real.pi / Real.arctan (1 / (10 : ℝ)^n) := sorry

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
