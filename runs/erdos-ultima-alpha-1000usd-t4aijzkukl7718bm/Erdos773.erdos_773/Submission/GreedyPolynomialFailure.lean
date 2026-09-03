import Submission.GreedyRoundedHorizon

/-!
Failure estimates on the family d=m^4, rho=1/m, C=16*m. For each fixed
normalized horizon and each fixed polynomial volume bound, the total
probability bound tends to zero.
-/
namespace Erdos773.GreedyPolynomialFailure
open Finset Filter GreedyProfileRecords GreedyProfileGuard GreedyGuardControls
open GreedyUniformMoments GreedyIntegratedVariance GreedyUniformCosts GreedyRoundedHorizon
open GreedyTrajectoryCalculus GreedyScaledTrajectory GreedyEnvelopeCalculus
set_option maxHeartbeats 2500000
noncomputable section

def params (m : ℕ) (V : ℝ) : Parameters := ⟨V,(m:ℝ)^4,1/(m:ℝ),4000⟩
def fixedSpeed (τ : ℝ) : ℝ := speed (params 1 1) τ
def fixedPenalty (τ : ℝ) : ℝ := penalty (params 1 1) τ
def auxNumerator (τ : ℝ) : ℝ := 576*τ^3/(q τ)^3

def totalBound (A m : ℕ) (τ : ℝ) : ℝ :=
  (m:ℝ)^(2*A)*(1/2:ℝ)^(m+1)+6*(m:ℝ)^A*Real.exp (-(m:ℝ)/(68*fixedPenalty τ))

@[simp] lemma speed_params (m : ℕ) (V τ : ℝ) : speed (params m V) τ = fixedSpeed τ := rfl
@[simp] lemma penalty_params (m : ℕ) (V τ : ℝ) : penalty (params m V) τ = fixedPenalty τ := rfl

lemma fixedSpeed_pos {τ : ℝ} (hτ : 0 ≤ τ) : 0 < fixedSpeed τ := by
  have ht : 0 < 1+τ := by linarith
  dsimp [fixedSpeed,speed,params]
  positivity

lemma fixedPenalty_pos {τ : ℝ} (hτ : 0 ≤ τ) : 0 < fixedPenalty τ := by
  have hF := (factor_pos (p := params 1 1) hτ).2
  have hS := fixedSpeed_pos hτ
  change 0 < integratedFactor (params 1 1) τ+5*(1+τ)^2+fixedSpeed τ+2
  positivity

lemma profile_failure_bound {m : ℕ} {τ : ℝ} (hm : 1 ≤ (m:ℝ)) (hτ : 0 ≤ τ) (V : ℝ) :
    failure (params m V) (16*m) τ ≤
      6*Real.exp (-(m:ℝ)/(68*fixedPenalty τ)) := by
  have hmpos : (0:ℝ) < m := by linarith
  have hZ := fixedPenalty_pos hτ
  have hnum : (m:ℝ)^4*(1/(m:ℝ))^2 = (m:ℝ)^2 := by field_simp
  have hh : (m:ℝ)/(68*fixedPenalty τ) ≤
      (m:ℝ)^2/(4*fixedPenalty τ*(16*(m:ℝ)+1)) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hm1 : (0:ℝ) ≤ (m:ℝ)-1 := sub_nonneg.mpr hm
    have hn : 0 ≤ fixedPenalty τ*(m:ℝ)*((m:ℝ)-1) := by positivity
    nlinarith only [hn]
  unfold GreedyUniformCosts.failure
  rw [penalty_params]
  change 6*Real.exp (-((m:ℝ)^4*(1/(m:ℝ))^2)/(4*fixedPenalty τ*((16*m:ℕ)+1))) ≤ _
  rw [hnum]
  norm_num only [Nat.cast_mul,Nat.cast_ofNat]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.mpr
  simpa only [neg_div,neg_le_neg_iff] using hh

lemma auxiliary_base_bound {m : ℕ} {V τ : ℝ} (hm : 0 < (m:ℝ)) (hV : 0 < V)
    (hτ : 0 ≤ τ) (hq : 4 ≤ V*q τ) :
    9*(m:ℝ)^12*((steps V ((m:ℝ)^4) τ:ℝ)/(stop V τ:ℝ))^3/((m:ℝ)+1) ≤
      auxNumerator τ/((m:ℝ)+1) := by
  have hqpos := q_pos τ
  have hr := ratio_bound hV (pow_pos hm 4) hτ hq
  have hpow := pow_le_pow_left₀ (by positivity) hr 3
  have hmul := mul_le_mul_of_nonneg_left hpow (show 0 ≤ 9*(m:ℝ)^12 by positivity)
  apply (div_le_div_of_nonneg_right hmul (by positivity)).trans_eq
  dsimp [auxNumerator]
  field_simp
  ring

lemma failure_bound {m A : ℕ} {V τ : ℝ} (hm : 1 ≤ (m:ℝ)) (hV : 0 < V)
    (hτ : 0 ≤ τ) (hq : 4 ≤ V*q τ) (hVA : V ≤ (m:ℝ)^A)
    (haux : 2*auxNumerator τ ≤ (m:ℝ)+1) :
    V^2*(9*(m^12:ℕ)*((steps V ((m:ℝ)^4) τ:ℝ)/(stop V τ:ℝ))^3/((m:ℝ)+1))^(m+1)+
      V*failure (params m V) (16*m) τ ≤ totalBound A m τ := by
  have hmpos : (0:ℝ) < m := by linarith
  have hbase := auxiliary_base_bound hmpos hV hτ hq
  have hhalf : auxNumerator τ/((m:ℝ)+1) ≤ (1/2:ℝ) :=
    (div_le_iff₀ (by positivity)).mpr (by linarith only [haux])
  have hbase' : 9*(m^12:ℕ)*((steps V ((m:ℝ)^4) τ:ℝ)/(stop V τ:ℝ))^3/((m:ℝ)+1) ≤ (1/2:ℝ) := by
    simpa only [Nat.cast_pow] using hbase.trans hhalf
  have h1 := mul_le_mul (pow_le_pow_left₀ hV.le hVA 2)
    (pow_le_pow_left₀ (by positivity) hbase' (m+1)) (by positivity) (by positivity)
  have h2 := mul_le_mul hVA (profile_failure_bound hm hτ V)
    (by unfold GreedyUniformCosts.failure; positivity) (pow_nonneg hmpos.le A)
  unfold totalBound
  have he : ((m:ℝ)^A)^2 = (m:ℝ)^(2*A) := by rw [← pow_mul,Nat.mul_comm A 2]
  rw [he] at h1
  nlinarith only [h1,h2]

/-- The explicit total failure budget vanishes for every fixed polynomial
    volume exponent. No bound on an actual process is assumed here. -/
theorem totalBound_tendsto (A : ℕ) {τ : ℝ} (hτ : 0 ≤ τ) :
    Tendsto (fun m : ℕ => totalBound A m τ) atTop (nhds 0) := by
  have hZ := fixedPenalty_pos hτ
  have hneg : -(1:ℝ)/(68*fixedPenalty τ) < 0 := div_neg_of_neg_of_pos (by norm_num) (by positivity)
  have hr0 : 0 ≤ Real.exp (-(1:ℝ)/(68*fixedPenalty τ)) := (Real.exp_pos _).le
  have hr1 : Real.exp (-(1:ℝ)/(68*fixedPenalty τ)) < 1 := Real.exp_lt_one_iff.mpr hneg
  have ha := (tendsto_pow_const_mul_const_pow_of_lt_one (2*A)
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1)).mul_const (1/2:ℝ)
  have hb := (tendsto_pow_const_mul_const_pow_of_lt_one A hr0 hr1).const_mul 6
  have hexp (m : ℕ) : Real.exp (-(m:ℝ)/(68*fixedPenalty τ)) =
      Real.exp (-(1:ℝ)/(68*fixedPenalty τ))^m := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  convert ha.add hb using 1
  · funext m
    simp only [totalBound,hexp,pow_succ]
    ring
  · norm_num

theorem eventually_totalBound_lt_one (A : ℕ) {τ : ℝ} (hτ : 0 ≤ τ) :
    ∀ᶠ m : ℕ in atTop, totalBound A m τ < 1 :=
  (totalBound_tendsto A hτ).eventually_lt_const (by norm_num)

#print axioms profile_failure_bound
#print axioms auxiliary_base_bound
#print axioms failure_bound
#print axioms totalBound_tendsto
#print axioms eventually_totalBound_lt_one
end
end Erdos773.GreedyPolynomialFailure
