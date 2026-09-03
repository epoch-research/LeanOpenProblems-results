import Submission.GreedyCodegreeUniformCosts
import Submission.GreedyHorizonFactors

/-! Polynomial nonlinear scales compatible with every witness guard. -/
namespace Erdos773.GreedyCodegreeScales
open Finset GreedyProfileRecords GreedyProfileGuard GreedyCodegreeGuardControls
open GreedyTrajectoryCalculus GreedyScaledTrajectory GreedyEnvelopeCalculus
open GreedyHorizonFactors GreedyPolynomialFailure GreedyUniformMoments GreedyUniformCosts
set_option maxHeartbeats 2500000
set_option exponentiation.threshold 1024
noncomputable section

def params (m : ℕ) (V : ℝ) : Parameters := ⟨V,(m:ℝ)^100,1/(m:ℝ)^25,4000⟩

@[simp] lemma speed_params (m : ℕ) (V τ : ℝ) : speed (params m V) τ = fixedSpeed τ := rfl
@[simp] lemma penalty_params (m : ℕ) (V τ : ℝ) : penalty (params m V) τ = fixedPenalty τ := rfl

/-- Terminal bounds on q and the two promotion thresholds suffice throughout
    the horizon, since the two-degree error envelope grows. -/
theorem promotion_bounds_of_uniform {p : Parameters} {L T C B2 B3 : ℕ} {τ : ℝ}
    (hh : Horizon p L T C τ)
    (hB2 : (B2:ℝ) ≤ p.d^2*p.rho*q τ)
    (hB3 : (B3:ℝ) ≤ p.d^3*p.rho*(q τ)^2) : PromotionBounds p T B2 B3 := by
  intro n hn
  have hc := hh.conditions hn.le
  have htτ := (time_mono hc.d_pos.le hc.V_pos.le hn.le).trans hh.time_bound
  have hq := q_antitone hc.time_nonneg htτ
  have hg : 1 ≤ growth p.K 0 (time p n) := by
    have hK : 0 ≤ p.K := by linarith only [hh.bounds.K_large]
    simpa only [growth_zero] using growth_monotone hK hK (by norm_num : (0:ℝ) ≤ 0) hc.time_nonneg
  have he : p.d*p.rho ≤ E2 p.d p.rho p.K (time p n) := by
    dsimp [E2]
    exact le_mul_of_one_le_right (mul_nonneg hc.d_pos.le hc.rho_nonneg) hg
  have hA : p.d*q τ ≤ p.d*q (time p n) := mul_le_mul_of_nonneg_left hq hc.d_pos.le
  have hA0 : 0 ≤ p.d*q τ := mul_nonneg hc.d_pos.le (q_pos τ).le
  have he0 := mul_nonneg hc.d_pos.le hc.rho_nonneg
  constructor
  · apply hB2.trans
    convert mul_le_mul hA he he0 (hA0.trans hA) using 1; ring
  · apply hB3.trans
    convert mul_le_mul (pow_le_pow_left₀ hA0 hA 2) he he0 (sq_nonneg _) using 1; ring

lemma promotion_factors {τ : ℝ} (hτ : 0 ≤ τ) :
    288/q τ ≤ horizonBudget τ ∧ 54/(q τ)^2 ≤ horizonBudget τ := by
  have h288 : (288:ℝ) ≤ Real.exp 9 := by have hh := two_pow_le_exp 9; norm_num at hh; linarith only [hh]
  have h54 : (54:ℝ) ≤ Real.exp 6 := by have hh := two_pow_le_exp 6; norm_num at hh; linarith only [hh]
  constructor
  · calc
      _ = 288*Real.exp (τ^3) := by rw [div_eq_mul_inv,inv_q]
      _ ≤ Real.exp 9*Real.exp (τ^3) := mul_le_mul_of_nonneg_right h288 (Real.exp_pos _).le
      _ = Real.exp (9+τ^3) := (Real.exp_add _ _).symm
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        nlinarith only [hτ,sq_nonneg τ,pow_nonneg hτ 3]
  · calc
      _ = 54*(Real.exp (τ^3))^2 := by rw [div_eq_mul_inv,← inv_pow,inv_q]
      _ ≤ Real.exp 6*(Real.exp (τ^3))^2 := mul_le_mul_of_nonneg_right h54 (sq_nonneg _)
      _ = Real.exp (6+2*τ^3) := by rw [← Real.exp_nat_mul,← Real.exp_add]; norm_num
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        nlinarith only [hτ,sq_nonneg τ,pow_nonneg hτ 3]

/-- The original uniform analytic bounds apply at d=m^100, rho=m^-25,
    C=16m^21. Their use is purely numerical, not a linearity assumption. -/
theorem uniform_bounds {m : ℕ} {V τ : ℝ} (hτ : 0 ≤ τ)
    (hm : horizonBudget τ ≤ (m:ℝ)) (hV : (m:ℝ)^300 ≤ V) :
    GreedyUniformHorizon.Bounds V ((m:ℝ)^100) (1/(m:ℝ)^25) 4000 τ (16*m^21) := by
  have hm1 : (1:ℝ) ≤ m := by linarith only [(budget_large hτ).1,hm]
  have hpow : (m:ℝ) ≤ (m:ℝ)^25 := by simpa only [pow_one] using pow_le_pow_right₀ hm1 (by omega : 1 ≤ 25)
  have hC : ((16*m^21:ℕ):ℝ) ≤ 16*(m:ℝ)^25 := by
    push_cast
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hm1 (by omega : 21 ≤ 25)) (by norm_num)
  have hh := GreedyUniformHorizon.exponential_threshold ((m:ℝ)^25) V τ (16*m^21)
    hτ (hm.trans hpow) (by simpa only [← pow_mul] using hV) hC
  simpa only [← pow_mul] using hh

lemma promotion_scales {m : ℕ} {V τ : ℝ} (hτ : 0 ≤ τ) (hm : horizonBudget τ ≤ (m:ℝ)) :
    ((288*m^133:ℕ):ℝ) ≤ (params m V).d^2*(params m V).rho*q τ ∧
    ((54*m^274:ℕ):ℝ) ≤ (params m V).d^3*(params m V).rho*(q τ)^2 := by
  have hm1 : (1:ℝ) ≤ m := by linarith only [(budget_large hτ).1,hm]
  have hm0 : (0:ℝ) < m := by linarith only [hm1]
  have h2 := (div_le_iff₀ (q_pos τ)).mp ((promotion_factors hτ).1.trans hm)
  have h3 := (div_le_iff₀ (sq_pos_of_pos (q_pos τ))).mp ((promotion_factors hτ).2.trans hm)
  have he2 : (params m V).d^2*(params m V).rho = (m:ℝ)^175 := by
    dsimp [params]
    field_simp
  have he3 : (params m V).d^3*(params m V).rho = (m:ℝ)^275 := by
    dsimp [params]
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
    (hm : horizonBudget τ ≤ (m:ℝ)) (hk : k ≤ m^3) (V : ℝ) :
    GreedyCodegreeUniformCosts.failure (params m V) k (16*m^21) τ ≤
      6*Real.exp (-(m:ℝ)/204) := by
  have hm1 : (1:ℝ) ≤ m := by linarith only [(budget_large hτ).1,hm]
  have hm0 : (0:ℝ) < m := by linarith only [hm1]
  have hZ := fixedPenalty_pos hτ
  have hZm : fixedPenalty τ ≤ (m:ℝ) := (factor_bounds hτ).1.trans hm
  have hkR : (k:ℝ) ≤ (m:ℝ)^3 := by exact_mod_cast hk
  have hm3 := one_le_pow₀ hm1 (n := 3)
  have hm21 := one_le_pow₀ hm1 (n := 21)
  have hfactor : (k:ℝ)+2 ≤ 3*(m:ℝ)^3 := by linarith only [hkR,hm3]
  have hC : (16:ℝ)*(m:ℝ)^21+1 ≤ 17*(m:ℝ)^21 := by linarith only [hm21]
  have hden : 4*(((k:ℝ)+2)*fixedPenalty τ)*(16*(m:ℝ)^21+1) ≤ 204*(m:ℝ)^25 := by
    have h₀ := mul_le_mul hfactor hZm hZ.le (by positivity : (0:ℝ) ≤ 3*(m:ℝ)^3)
    have h₁ := mul_le_mul h₀ hC (by positivity : (0:ℝ) ≤ 16*(m:ℝ)^21+1) (by positivity : (0:ℝ) ≤ 3*(m:ℝ)^3*(m:ℝ))
    nlinarith only [h₁]
  have he : (params m V).d*(params m V).rho^2 = (m:ℝ)^50 := by
    dsimp [params]
    field_simp
  have hratio : (m:ℝ)/204 ≤ (m:ℝ)^50/(4*(((k:ℝ)+2)*fixedPenalty τ)*(16*(m:ℝ)^21+1)) := by
    apply (div_le_div_iff₀ (by norm_num) (by positivity)).mpr
    have hh := mul_le_mul_of_nonneg_left hden hm0.le
    have hp := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hm1 (by omega : 26 ≤ 50)) (by norm_num : (0:ℝ) ≤ 204)
    nlinarith only [hh,hp]
  unfold GreedyCodegreeUniformCosts.failure
  rw [he,penalty_params]
  push_cast
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.mpr
  simpa only [neg_div,neg_le_neg_iff] using hratio

#print axioms promotion_bounds_of_uniform
#print axioms promotion_factors
#print axioms uniform_bounds
#print axioms promotion_scales
#print axioms profile_failure_bound
end
end Erdos773.GreedyCodegreeScales
