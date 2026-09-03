import Submission.GreedyCodegreeGrowing

/-! Separating small analytic factors from the much larger envelope budget. -/
namespace Erdos773.GreedyRelaxedBudget
open GreedyHorizonFactors GreedyPolynomialFailure GreedyTrajectoryCalculus
set_option maxHeartbeats 2500000
noncomputable section

lemma exp_fiftieth_bound {m : ℕ} {τ : ℝ} (hτ : 0 ≤ τ)
    (hm : horizonBudget τ ≤ (m:ℝ)^25) : Real.exp (50*(1+τ)^3) ≤ m := by
  apply le_of_pow_le_pow_left₀ (by decide : (25:ℕ)≠0) (Nat.cast_nonneg m)
  calc
    (Real.exp (50*(1+τ)^3))^25 = Real.exp (1250*(1+τ)^3) := by
      rw [← Real.exp_nat_mul]
      congr 1
      norm_num
      ring
    _  ≤  horizonBudget τ := by
      apply Real.exp_le_exp.mpr
      have hh : 0 ≤ (1+τ)^3 := by positivity
      nlinarith
    _  ≤  _ := hm

lemma small_factor_bounds {m : ℕ} {τ : ℝ} (hτ : 0 ≤ τ)
    (hm : horizonBudget τ ≤ (m:ℝ)^25) :
    fixedPenalty τ ≤ m ∧ fixedSpeed τ ≤ m ∧ 4/q τ ≤ m ∧ 4*τ/q τ ≤ m ∧
      288/q τ ≤ m ∧ 54/(q τ)^2 ≤ m := by
  have h50 := exp_fiftieth_bound hτ hm
  have hB : 0 ≤ (1+τ)^3 := by positivity
  have h20 : Real.exp (20*(1+τ)^3) ≤ m := by
    apply le_trans _ h50
    exact Real.exp_le_exp.mpr (by nlinarith)
  refine ⟨(penalty_exp_bound hτ).trans h50,(speed_exp_bound hτ).trans h20,?_,?_,?_,?_⟩
  · have hc : (4:ℝ) ≤ Real.exp 2 := by have hh := two_pow_le_exp 2; norm_num at hh; exact hh
    calc
      _ = 4*Real.exp (τ^3) := by rw [div_eq_mul_inv,inv_q]
      _  ≤  Real.exp 2*Real.exp (τ^3) := mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le
      _ = Real.exp (2+τ^3) := (Real.exp_add _ _).symm
      _  ≤  _ := (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg τ,pow_nonneg hτ 3])).trans h20
  · have hc : (4:ℝ) ≤ Real.exp 2 := by have hh := two_pow_le_exp 2; norm_num at hh; exact hh
    have ht : τ ≤ Real.exp τ := by linarith [Real.add_one_le_exp τ]
    calc
      _ = 4*τ*Real.exp (τ^3) := by rw [div_eq_mul_inv,inv_q]
      _  ≤  Real.exp 2*Real.exp τ*Real.exp (τ^3) :=
        mul_le_mul_of_nonneg_right (mul_le_mul hc ht hτ (Real.exp_pos 2).le) (Real.exp_pos _).le
      _ = Real.exp (2+τ+τ^3) := by rw [← Real.exp_add,← Real.exp_add]
      _  ≤  _ := (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg τ,pow_nonneg hτ 3])).trans h20
  · have hc : (288:ℝ) ≤ Real.exp 9 := by have hh := two_pow_le_exp 9; norm_num at hh; linarith
    calc
      _ = 288*Real.exp (τ^3) := by rw [div_eq_mul_inv,inv_q]
      _  ≤  Real.exp 9*Real.exp (τ^3) := mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le
      _ = Real.exp (9+τ^3) := (Real.exp_add _ _).symm
      _  ≤  _ := (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg τ,pow_nonneg hτ 3])).trans h20
  · have hc : (54:ℝ) ≤ Real.exp 6 := by have hh := two_pow_le_exp 6; norm_num at hh; linarith
    calc
      _ = 54*(Real.exp (τ^3))^2 := by rw [div_eq_mul_inv,← inv_pow,inv_q]
      _  ≤  Real.exp 6*(Real.exp (τ^3))^2 := mul_le_mul_of_nonneg_right hc (sq_nonneg _)
      _ = Real.exp (6+2*τ^3) := by rw [← Real.exp_nat_mul,← Real.exp_add]; norm_num
      _  ≤  _ := (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg τ,pow_nonneg hτ 3])).trans h20

lemma base_one {m : ℕ} {τ : ℝ} (hτ : 0 ≤ τ) (hm : horizonBudget τ ≤ (m:ℝ)^25) : (1:ℝ) ≤ m := by
  have he : (1:ℝ) ≤ Real.exp (50*(1+τ)^3) := Real.one_le_exp_iff.mpr (by positivity)
  exact he.trans (exp_fiftieth_bound hτ hm)

#print axioms small_factor_bounds
end
end Erdos773.GreedyRelaxedBudget
