import FormalConjectures.Util.ProblemImports

open Complex Polynomial

noncomputable def w : ℂ := exp (2 * Real.pi * I / 13)

lemma w_sub_one_ne_zero : w - 1 ≠ 0 := by
  intro h
  have h1 : w = 1 := sub_eq_zero.mp h
  rw [w, Complex.exp_eq_one_iff] at h1
  rcases h1 with ⟨n, hn⟩
  have hz : 2 * (Real.pi : ℂ) * I ≠ 0 := by
    intro hc
    simp [Complex.I_ne_zero, Real.pi_ne_zero] at hc
  have H : (2 * Real.pi * I / 13) / (2 * Real.pi * I) = ↑n := by
    rw [hn, mul_div_cancel_right₀ _ hz]
  have H2 : (2 * Real.pi * I / 13) / (2 * Real.pi * I) = (1 / 13 : ℂ) := by
    have : 2 * ↑Real.pi * I / 13 = (1 / 13 : ℂ) * (2 * ↑Real.pi * I) := by ring
    rw [this, mul_div_cancel_right₀ _ hz]
  rw [H2] at H
  have H4 : (1 / 13 : ℂ).re = (n : ℂ).re := by rw [H]
  simp at H4
  have H5 : (13⁻¹ : ℝ) = (n : ℝ) := H4
  have H6 : (0 : ℝ) < 13⁻¹ := by norm_num
  have H7 : (13⁻¹ : ℝ) < 1 := by norm_num
  rw [H5] at H6 H7
  have H8 : (0 : ℤ) < n := by exact_mod_cast H6
  have H9 : n < (1 : ℤ) := by exact_mod_cast H7
  linarith

lemma exp_mul (z : ℂ) (k : ℕ) : exp (k * z) = (exp z)^k := by
  induction k with
  | zero => simp
  | succ n ih =>
    have : (n.succ : ℂ) * z = n * z + z := by
      push_cast
      ring
    rw [this, exp_add, ih, pow_succ]

lemma w_pow (k : ℕ) : w^k = exp (k * 2 * Real.pi * I / 13) := by
  have : (k : ℂ) * (2 * ↑Real.pi * I / 13) = ↑k * 2 * ↑Real.pi * I / 13 := by ring
  rw [w, ← exp_mul, this]

lemma w_pow_13 : w^13 = 1 := by
  rw [w_pow]
  have : (13 : ℂ) * 2 * Real.pi * I / 13 = 2 * Real.pi * I := by ring
  have h_cast : (13 : ℂ) = (13 : ℕ) := by norm_num
  rw [← h_cast]
  rw [this]
  exact Complex.exp_two_pi_mul_I

lemma w_sum_12 : w^12 + w^11 + w^10 + w^9 + w^8 + w^7 + w^6 + w^5 + w^4 + w^3 + w^2 + w + 1 = 0 := by
  have h : w^13 - 1 = (w - 1) * (w^12 + w^11 + w^10 + w^9 + w^8 + w^7 + w^6 + w^5 + w^4 + w^3 + w^2 + w + 1) := by ring
  have h2 : w^13 - 1 = 0 := by rw [w_pow_13, sub_self]
  rw [h2] at h
  cases mul_eq_zero.mp h.symm with
  | inl h3 => exact False.elim (w_sub_one_ne_zero h3)
  | inr h4 => exact h4

