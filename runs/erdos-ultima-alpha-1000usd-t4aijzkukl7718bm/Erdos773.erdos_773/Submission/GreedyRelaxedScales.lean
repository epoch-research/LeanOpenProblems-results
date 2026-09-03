import Submission.GreedyRelaxedBudget

/-! Nonlinear numerical scales with the relaxed twenty-fifth-power budget. -/
namespace Erdos773.GreedyRelaxedScales
open Finset GreedyProfileRecords GreedyProfileGuard GreedyCodegreeGuardControls
open GreedyTrajectoryCalculus GreedyScaledTrajectory GreedyEnvelopeCalculus
open GreedyHorizonFactors GreedyPolynomialFailure GreedyUniformMoments GreedyUniformCosts
open GreedyCodegreeScales GreedyRelaxedBudget
set_option maxHeartbeats 2500000
set_option exponentiation.threshold 1024
noncomputable section

/-- The original uniform analytic bounds apply at d=m^100, rho=m^-25,
    C=16m^21. Their use is purely numerical, not a linearity assumption. -/
theorem uniform_bounds {m : ℕ} {V τ : ℝ} (hτ : 0 ≤ τ)
    (hm : horizonBudget τ ≤ (m:ℝ)^25) (hV : (m:ℝ)^300 ≤ V) :
    GreedyUniformHorizon.Bounds V ((m:ℝ)^100) (1/(m:ℝ)^25) 4000 τ (16*m^21) := by
  have hm1 : (1:ℝ) ≤ m := base_one hτ hm
  have hC : ((16*m^21:ℕ):ℝ) ≤ 16*(m:ℝ)^25 := by
    push_cast
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hm1 (by omega : 21 ≤ 25)) (by norm_num)
  have hh := GreedyUniformHorizon.exponential_threshold ((m:ℝ)^25) V τ (16*m^21)
    hτ hm (by simpa only [← pow_mul] using hV) hC
  simpa only [← pow_mul] using hh

lemma promotion_scales {m : ℕ} {V τ : ℝ} (hτ : 0 ≤ τ) (hm : horizonBudget τ ≤ (m:ℝ)^25) :
    ((288*m^133:ℕ):ℝ) ≤ (GreedyCodegreeScales.params m V).d^2*(GreedyCodegreeScales.params m V).rho*q τ ∧
    ((54*m^274:ℕ):ℝ) ≤ (GreedyCodegreeScales.params m V).d^3*(GreedyCodegreeScales.params m V).rho*(q τ)^2 := by
  have hm1 : (1:ℝ) ≤ m := base_one hτ hm
  have hm0 : (0:ℝ) < m := by linarith only [hm1]
  have h2 := (div_le_iff₀ (q_pos τ)).mp (small_factor_bounds hτ hm).2.2.2.2.1
  have h3 := (div_le_iff₀ (sq_pos_of_pos (q_pos τ))).mp (small_factor_bounds hτ hm).2.2.2.2.2
  have he2 : (GreedyCodegreeScales.params m V).d^2*(GreedyCodegreeScales.params m V).rho = (m:ℝ)^175 := by
    dsimp [GreedyCodegreeScales.params]
    field_simp
  have he3 : (GreedyCodegreeScales.params m V).d^3*(GreedyCodegreeScales.params m V).rho = (m:ℝ)^275 := by
    dsimp [GreedyCodegreeScales.params]
    field_simp
  rw [he2,he3]
  push_cast
  constructor
  · have hh := mul_le_mul_of_nonneg_left h2 (pow_nonneg hm0.le 133)
    have hp := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hm1 (by omega : 134 ≤ 175)) (q_pos τ).le
    nlinarith only [hh,hp]
  · have hh := mul_le_mul_of_nonneg_left h3 (pow_nonneg hm0.le 274)
    nlinarith only [hh]

/-- Uniform profile-failure bound with the actual codegree factor included.
    The large spare powers are weakened to an exponential in m. -/
theorem profile_failure_bound {m k : ℕ} {τ : ℝ} (hτ : 0 ≤ τ)
    (hm : horizonBudget τ ≤ (m:ℝ)^25) (hk : k ≤ m^3) (V : ℝ) :
    GreedyCodegreeUniformCosts.failure (GreedyCodegreeScales.params m V) k (16*m^21) τ ≤
      6*Real.exp (-(m:ℝ)/204) := by
  have hm1 : (1:ℝ) ≤ m := base_one hτ hm
  have hm0 : (0:ℝ) < m := by linarith only [hm1]
  have hZ := fixedPenalty_pos hτ
  have hZm : fixedPenalty τ ≤ (m:ℝ) := (small_factor_bounds hτ hm).1
  have hkR : (k:ℝ) ≤ (m:ℝ)^3 := by exact_mod_cast hk
  have hm3 := one_le_pow₀ hm1 (n := 3)
  have hm21 := one_le_pow₀ hm1 (n := 21)
  have hfactor : (k:ℝ)+2 ≤ 3*(m:ℝ)^3 := by linarith only [hkR,hm3]
  have hC : (16:ℝ)*(m:ℝ)^21+1 ≤ 17*(m:ℝ)^21 := by linarith only [hm21]
  have hden : 4*(((k:ℝ)+2)*fixedPenalty τ)*(16*(m:ℝ)^21+1) ≤ 204*(m:ℝ)^25 := by
    have h₀ := mul_le_mul hfactor hZm hZ.le (by positivity : (0:ℝ) ≤ 3*(m:ℝ)^3)
    have h₁ := mul_le_mul h₀ hC (by positivity : (0:ℝ) ≤ 16*(m:ℝ)^21+1) (by positivity : (0:ℝ) ≤ 3*(m:ℝ)^3*(m:ℝ))
    nlinarith only [h₁]
  have he : (GreedyCodegreeScales.params m V).d*(GreedyCodegreeScales.params m V).rho^2 = (m:ℝ)^50 := by
    dsimp [GreedyCodegreeScales.params]
    field_simp
  have hratio : (m:ℝ)/204 ≤ (m:ℝ)^50/(4*(((k:ℝ)+2)*fixedPenalty τ)*(16*(m:ℝ)^21+1)) := by
    apply (div_le_div_iff₀ (by norm_num) (by positivity)).mpr
    have hh := mul_le_mul_of_nonneg_left hden hm0.le
    have hp := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hm1 (by omega : 26 ≤ 50)) (by norm_num : (0:ℝ) ≤ 204)
    nlinarith only [hh,hp]
  unfold GreedyCodegreeUniformCosts.failure
  rw [he,GreedyCodegreeScales.penalty_params]
  push_cast
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.mpr
  simpa only [neg_div,neg_le_neg_iff] using hratio

#print axioms uniform_bounds
#print axioms promotion_scales
#print axioms profile_failure_bound
end
end Erdos773.GreedyRelaxedScales
