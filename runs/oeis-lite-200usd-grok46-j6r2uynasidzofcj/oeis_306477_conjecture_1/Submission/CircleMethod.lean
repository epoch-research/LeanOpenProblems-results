import FormalConjectures.Util.ProblemImports

/-!
Elementary exponential-sum estimates aimed at the 2-4-6-8 conjecture.
We work with `e : ℝ → ℂ`, `e θ = exp(2πi θ)`.
-/

open Complex Real

noncomputable def e (θ : ℝ) : ℂ := cexp (2 * π * I * θ)

lemma e_add (a b : ℝ) : e (a + b) = e a * e b := by
  simp [e, mul_add, add_mul, Complex.exp_add]

lemma e_zero : e 0 = 1 := by simp [e]

lemma e_int (n : ℤ) : e n = 1 := by
  simp [e, mul_comm (n : ℂ), ← mul_assoc]
  have : (2 * π * I * (n : ℂ) : ℂ) = (n : ℂ) * (2 * π * I) := by ring
  rw [this, Complex.exp_int_mul]
  simp [Complex.exp_two_pi_mul_I]

lemma e_nat (n : ℕ) : e (n : ℝ) = 1 := e_int n

lemma norm_e (θ : ℝ) : ‖e θ‖ = 1 := by
  simp [e, Complex.norm_exp]
  ring_nf
  simp

lemma e_periodic (θ : ℝ) (n : ℤ) : e (θ + n) = e θ := by
  rw [e_add, e_int, mul_one]

/-- Geometric sum: `∑_{j=0}^{N-1} e (j α)`. -/
lemma geom_sum_e (α : ℝ) (N : ℕ) :
    ∑ j ∈ Finset.range N, e (j * α) =
      if e α = 1 then N else (1 - e (N * α)) / (1 - e α) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases h : e α = 1
    · simp [h, e_add]
      -- e (N*α) = e α ^ N = 1
      have : e (N * α) = 1 := by
        -- e(Nα) = e(α)^N by iterating e_add
        have hpow : e (N * α) = e α ^ N := by
          induction N with
          | zero => simp [e_zero]
          | succ N ih =>
            rw [Nat.cast_succ, add_mul, one_mul, e_add, ih, pow_succ]
        simpa [h] using hpow
      simp [this]
    · simp [h]
      have hden : (1 - e α) ≠ 0 := by
        intro hz; apply h; linear_combination hz
      field_simp [hden]
      have : e (N * α) * e α = e ((N + 1) * α) := by
        rw [← e_add]; ring_nf
      rw [this]
      ring

lemma norm_geom_sum_e_le (α : ℝ) (N : ℕ) :
    ‖∑ j ∈ Finset.range N, e (j * α)‖ ≤ min N (1 / |1 - (e α).re| * 2) := by
  sorry
