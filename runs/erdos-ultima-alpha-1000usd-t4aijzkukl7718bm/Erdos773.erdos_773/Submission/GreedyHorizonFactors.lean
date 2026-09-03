import Submission.GreedyPolynomialFailure

/-!
Explicit exponential bounds on the horizon-dependent factors. These are
preparations for quantifying the growing-horizon concentration theorem;
that theorem is not assumed or asserted in this module.
-/
namespace Erdos773.GreedyHorizonFactors
open GreedyProfileRecords GreedyUniformMoments GreedyIntegratedVariance
open GreedyUniformCosts GreedyPolynomialFailure GreedyTrajectoryCalculus
set_option maxHeartbeats 2500000
noncomputable section

def horizonBudget (τ : ℝ) : ℝ := Real.exp (10000*(1+τ)^3)

lemma two_pow_le_exp (n : ℕ) : (2:ℝ)^n ≤ Real.exp (n:ℝ) := by
  have he : (2:ℝ) ≤ Real.exp 1 := by linarith only [Real.add_one_le_exp 1]
  have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) he n
  simpa only [← Real.exp_nat_mul,mul_one] using hh

lemma inv_q (τ : ℝ) : (q τ)⁻¹ = Real.exp (τ^3) := by
  rw [q,← Real.exp_neg,neg_neg]

lemma penalty_polynomial {τ : ℝ} (hτ : 0 ≤ τ) :
    fixedPenalty τ ≤ 1000000000*(1+τ)^9*Real.exp (τ^3) := by
  have hB : (1:ℝ) ≤ 1+τ := by linarith
  have he1 : (1:ℝ) ≤ Real.exp (τ^3) := Real.one_le_exp_iff.mpr (pow_nonneg hτ 3)
  have hpoly (n : ℕ) (hn : n ≤ 9) : (1+τ)^n ≤ (1+τ)^9 := pow_le_pow_right₀ hB hn
  have h9 : 0 ≤ (1+τ)^9 := pow_nonneg (by linarith only [hB]) 9
  have h9e : (1+τ)^9 ≤ (1+τ)^9*Real.exp (τ^3) := by nlinarith only [mul_le_mul_of_nonneg_left he1 h9]
  have he : fixedPenalty τ =
      (1200*(1+τ)^7+513921800*(1+τ)^9)*Real.exp (τ^3)+
      5*(1+τ)^2+16030*(1+τ)^4+2 := by
    dsimp [fixedPenalty,penalty,integratedFactor,varianceFactor,speed,params]
    rw [div_eq_mul_inv,inv_q]
    ring
  rw [he]
  have h7e := mul_le_mul_of_nonneg_right (hpoly 7 (by omega)) (Real.exp_pos (τ^3)).le
  have h2 := hpoly 2 (by omega)
  have h4 := hpoly 4 (by omega)
  have h0 := hpoly 0 (by omega)
  norm_num only [pow_zero] at h0
  nlinarith only [h7e,h2,h4,h0,h9e,h9,mul_nonneg h9 (Real.exp_pos (τ^3)).le]

lemma polynomial_exp_bound {τ : ℝ} (hτ : 0 ≤ τ) :
    1000000000*(1+τ)^9*Real.exp (τ^3) ≤ Real.exp (50*(1+τ)^3) := by
  have hc : (1000000000:ℝ) ≤ Real.exp 32 := by
    have hh := two_pow_le_exp 32
    norm_num at hh
    linarith only [hh]
  have hB0 : (0:ℝ) ≤ 1+τ := by linarith
  have hBe : 1+τ ≤ Real.exp (1+τ) := by linarith only [Real.add_one_le_exp (1+τ)]
  have hp := pow_le_pow_left₀ hB0 hBe 9
  calc
    _ ≤ Real.exp 32*(Real.exp (1+τ))^9*Real.exp (τ^3) :=
      mul_le_mul_of_nonneg_right (mul_le_mul hc hp (pow_nonneg hB0 9) (Real.exp_pos 32).le)
        (Real.exp_pos (τ^3)).le
    _ = Real.exp (32+9*(1+τ)+τ^3) := by rw [← Real.exp_nat_mul,← Real.exp_add,← Real.exp_add]; norm_num
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      nlinarith only [hτ,sq_nonneg τ,pow_nonneg hτ 3]

lemma penalty_exp_bound {τ : ℝ} (hτ : 0 ≤ τ) : fixedPenalty τ ≤ Real.exp (50*(1+τ)^3) :=
  (penalty_polynomial hτ).trans (polynomial_exp_bound hτ)

lemma speed_exp_bound {τ : ℝ} (hτ : 0 ≤ τ) : fixedSpeed τ ≤ Real.exp (20*(1+τ)^3) := by
  have hc : (16030:ℝ) ≤ Real.exp 14 := by
    have hh := two_pow_le_exp 14
    norm_num at hh
    linarith only [hh]
  have hB0 : (0:ℝ) ≤ 1+τ := by linarith
  have hBe : 1+τ ≤ Real.exp (1+τ) := by linarith only [Real.add_one_le_exp (1+τ)]
  have hp := pow_le_pow_left₀ hB0 hBe 4
  have he : fixedSpeed τ = 16030*(1+τ)^4 := by dsimp [fixedSpeed,speed,params]; norm_num
  rw [he]
  calc
    _ ≤ Real.exp 14*(Real.exp (1+τ))^4 := mul_le_mul hc hp (pow_nonneg hB0 4) (Real.exp_pos 14).le
    _ = Real.exp (14+4*(1+τ)) := by rw [← Real.exp_nat_mul,← Real.exp_add]; norm_num
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      nlinarith only [hτ,sq_nonneg τ,pow_nonneg hτ 3]

lemma auxiliary_exp_bound {τ : ℝ} (hτ : 0 ≤ τ) : auxNumerator τ ≤ Real.exp (20*(1+τ)^3) := by
  have hc : (576:ℝ) ≤ Real.exp 10 := by
    have hh := two_pow_le_exp 10
    norm_num at hh
    linarith only [hh]
  have hte : τ ≤ Real.exp τ := by linarith only [Real.add_one_le_exp τ]
  have hp := pow_le_pow_left₀ hτ hte 3
  have he : auxNumerator τ = 576*τ^3*(Real.exp (τ^3))^3 := by
    rw [auxNumerator,div_eq_mul_inv,← inv_pow,inv_q]
  rw [he]
  calc
    _ ≤ Real.exp 10*(Real.exp τ)^3*(Real.exp (τ^3))^3 :=
      mul_le_mul_of_nonneg_right (mul_le_mul hc hp (pow_nonneg hτ 3) (Real.exp_pos 10).le) (by positivity)
    _ = Real.exp (10+3*τ+3*τ^3) := by
      rw [← Real.exp_nat_mul,← Real.exp_nat_mul,← Real.exp_add,← Real.exp_add]
      norm_num
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      nlinarith only [hτ,sq_nonneg τ,pow_nonneg hτ 3]

lemma budget_large {τ : ℝ} (hτ : 0 ≤ τ) :
    17 ≤ horizonBudget τ ∧ τ ≤ horizonBudget τ := by
  have hp : (1:ℝ) ≤ (1+τ)^3 := one_le_pow₀ (by linarith only [hτ] : (1:ℝ) ≤ 1+τ)
  have hh := Real.add_one_le_exp (10000*(1+τ)^3)
  have hτpow : τ ≤ (1+τ)^3 := by nlinarith only [hτ,sq_nonneg τ,pow_nonneg hτ 3]
  constructor <;> dsimp [horizonBudget] <;> linarith only [hp,hh,hτpow]

lemma factor_bounds {τ : ℝ} (hτ : 0 ≤ τ) :
    fixedPenalty τ ≤ horizonBudget τ ∧ fixedSpeed τ ≤ horizonBudget τ ∧
    auxNumerator τ ≤ horizonBudget τ ∧ 4/q τ ≤ horizonBudget τ ∧
    4*τ/q τ ≤ horizonBudget τ := by
  have hB3 : 0 ≤ (1+τ)^3 := pow_nonneg (by linarith only [hτ]) 3
  have h20 : Real.exp (20*(1+τ)^3) ≤ horizonBudget τ := by
    apply Real.exp_le_exp.mpr
    nlinarith only [hB3]
  have h50 : Real.exp (50*(1+τ)^3) ≤ horizonBudget τ := by
    apply Real.exp_le_exp.mpr
    nlinarith only [hB3]
  refine ⟨(penalty_exp_bound hτ).trans h50,(speed_exp_bound hτ).trans h20,
    (auxiliary_exp_bound hτ).trans h20,?_,?_⟩
  · have hc : (4:ℝ) ≤ Real.exp 2 := by have hh := two_pow_le_exp 2; norm_num at hh; exact hh
    calc
      _ = 4*Real.exp (τ^3) := by rw [div_eq_mul_inv,inv_q]
      _ ≤ Real.exp 2*Real.exp (τ^3) := mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le
      _ = Real.exp (2+τ^3) := (Real.exp_add _ _).symm
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        nlinarith only [hτ,sq_nonneg τ,pow_nonneg hτ 3]
  · have hc : (4:ℝ) ≤ Real.exp 2 := by have hh := two_pow_le_exp 2; norm_num at hh; exact hh
    have ht : τ ≤ Real.exp τ := by linarith only [Real.add_one_le_exp τ]
    calc
      _ = 4*τ*Real.exp (τ^3) := by rw [div_eq_mul_inv,inv_q]
      _ ≤ Real.exp 2*Real.exp τ*Real.exp (τ^3) :=
        mul_le_mul_of_nonneg_right (mul_le_mul hc ht hτ (Real.exp_pos 2).le) (Real.exp_pos _).le
      _ = Real.exp (2+τ+τ^3) := by rw [← Real.exp_add,← Real.exp_add]
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        nlinarith only [hτ,sq_nonneg τ,pow_nonneg hτ 3]

#print axioms penalty_exp_bound
#print axioms speed_exp_bound
#print axioms auxiliary_exp_bound
#print axioms factor_bounds
end
end Erdos773.GreedyHorizonFactors
