import Submission.GreedyBatchVolume

/-! The total failure penalty is smaller than the spare p/m in the
continuation profile, uniformly over all forward stage volumes. -/
namespace Erdos773.GreedyBatchFailurePenalty
open GreedyBatchProfiles GreedyBatchProfileStep GreedyBatchProfileConditions
open GreedyBatchCertificate GreedyBatchScaleTails GreedyBatchVolume
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option exponentiation.threshold 2048
noncomputable section

lemma probability_lower (m A : ℕ) (d t : ℝ) (C P : ℕ) (h : Range m d t C P) (hd : d≤ (m:ℝ)^A) :
    1/(2*(m:ℝ)^(A+5))≤ probability m d t/(m:ℝ) := by
  have hm := h.m_pos
  have hd0 := h.d_pos
  have ht0 : 0≤ t := by have := h.t_one; linarith
  have ht2 := pow_le_pow_left₀ ht0 h.t_upper 2
  have hm2 : (1:ℝ)≤ (m:ℝ)^2 := one_le_pow₀ h.m_one
  have hden : (m:ℝ)^2*(1+t^2)≤ 2*(m:ℝ)^4 := by
    have hh := mul_le_mul_of_nonneg_left (show 1+t^2≤ 2*(m:ℝ)^2 by linarith only [ht2,hm2]) (sq_nonneg (m:ℝ))
    nlinarith only [hh]
  have hs : 1/(2*(m:ℝ)^4)≤ step m t :=
    one_div_le_one_div_of_le (by positivity) hden
  have hp1 := div_le_div_of_nonneg_right hs hd0.le
  have hp2 := div_le_div_of_nonneg_left (by positivity : (0:ℝ)≤ 1/(2*(m:ℝ)^4)) hd0 hd
  have hp := div_le_div_of_nonneg_right (hp2.trans hp1) hm.le
  have he : (1/(2*(m:ℝ)^4))/(m:ℝ)^A/(m:ℝ)=1/(2*(m:ℝ)^(A+5)) := by
    rw [pow_add]
    field_simp
  simpa only [he,probability] using hp

lemma tests_exp (m V : ℕ) (hV : (V:ℝ)≤ Real.exp ((m:ℝ)^5)) :
    tests V≤ 14*Real.exp (2*(m:ℝ)^5) := by
  have hE : 1≤ Real.exp ((m:ℝ)^5) := Real.one_le_exp_iff.mpr (by positivity)
  have hE0 := (Real.exp_pos ((m:ℝ)^5)).le
  have hV0 : (0:ℝ)≤ V := Nat.cast_nonneg V
  have hV2 := pow_le_pow_left₀ hV0 hV 2
  have hE2 : Real.exp ((m:ℝ)^5)≤ (Real.exp ((m:ℝ)^5))^2 := by nlinarith only [hE]
  have hh : tests V≤ 14*(Real.exp ((m:ℝ)^5))^2 := by
    unfold tests
    nlinarith only [hV,hV2,hE2]
  have he : (Real.exp ((m:ℝ)^5))^2=Real.exp (2*(m:ℝ)^5) := by rw [← Real.exp_nat_mul]; norm_num
  rwa [he] at hh

lemma penalty_exp (m V : ℕ) (hV : (V:ℝ)≤ Real.exp ((m:ℝ)^5)) :
    tests V*GreedyBatchScaleTails.failure m≤ 28*Real.exp (2*(m:ℝ)^5-(m:ℝ)^7) := by
  have hf : 0≤ GreedyBatchScaleTails.failure m := by unfold GreedyBatchScaleTails.failure; positivity
  have hh := mul_le_mul_of_nonneg_right (tests_exp m V hV) hf
  apply hh.trans_eq
  unfold GreedyBatchScaleTails.failure
  calc
    _ = 28*(Real.exp (2*(m:ℝ)^5)*Real.exp (-(m:ℝ)^7)) := by ring
    _ = _ := by rw [← Real.exp_add]; congr 2 <;> ring

lemma logarithmic_budget (m A : ℕ) (hm : A+100≤ m) :
    Real.log 56+((A+5:ℕ):ℝ)*Real.log (m:ℝ)+2*(m:ℝ)^5≤ (m:ℝ)^7 := by
  have hm100 : 100≤ m := by omega
  have hmR : (100:ℝ)≤ m := by exact_mod_cast hm100
  have hm0 : (0:ℝ)< m := by linarith only [hmR]
  have hm1 : (1:ℝ)≤ m := by linarith only [hmR]
  have hA : ((A+5:ℕ):ℝ)≤ m := by exact_mod_cast (show A+5≤ m by omega)
  have hlog : Real.log (m:ℝ)≤ m := (Real.log_le_sub_one_of_pos hm0).trans (by linarith)
  have hlog56 : Real.log 56≤ 56 := (Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<56)).trans (by norm_num)
  have hh := mul_le_mul hA hlog (Real.log_nonneg hm1) hm0.le
  have hm2 : (56:ℝ)≤ (m:ℝ)^2 := by nlinarith only [hmR]
  have h25 := power_slack m 2 5 2 hm100 (by norm_num) (by decide)
  have h57 := power_slack m 5 7 3 hm100 (by norm_num) (by decide)
  nlinarith only [hlog56,hh,hm2,h25,h57]

lemma exponential_small (m A : ℕ) (hm : A+100≤ m) :
    28*Real.exp (2*(m:ℝ)^5-(m:ℝ)^7)≤ 1/(2*(m:ℝ)^(A+5)) := by
  have hm0 : (0:ℝ)< m := by exact_mod_cast (show 0< m by omega)
  have hh := logarithmic_budget m A hm
  have he : Real.exp (Real.log 56+((A+5:ℕ):ℝ)*Real.log (m:ℝ)+2*(m:ℝ)^5-(m:ℝ)^7)≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith only [hh])
  have hsum : Real.log 56+((A+5:ℕ):ℝ)*Real.log (m:ℝ)+2*(m:ℝ)^5-(m:ℝ)^7=
      (Real.log 56+((A+5:ℕ):ℝ)*Real.log (m:ℝ))+(2*(m:ℝ)^5-(m:ℝ)^7) := by ring
  rw [hsum,Real.exp_add,Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<56),
    Real.exp_nat_mul,Real.exp_log hm0] at he
  apply (le_div_iff₀ (by positivity : (0:ℝ)<2*(m:ℝ)^(A+5))).mpr
  nlinarith only [he]

/-- Explicit total failure control for an arbitrary volume up to exp(m^5). -/
theorem penalty (m A V : ℕ) (d t : ℝ) (C P : ℕ) (h : Range m d t C P)
    (hm : A+100≤ m) (hd : d≤ (m:ℝ)^A) (hV : (V:ℝ)≤ Real.exp ((m:ℝ)^5)) :
    tests V*GreedyBatchScaleTails.failure m≤ probability m d t/(m:ℝ) :=
  (penalty_exp m V hV).trans ((exponential_small m A hm).trans (probability_lower m A d t C P h hd))

/-- The prescribed forward-volume schedule supplies the failure control. -/
theorem volume_penalty (m A i : ℕ) (d t : ℝ) (C P : ℕ) (h : Range m d t C P)
    (hm : 3*increment A≤ m) (hi : i≤ 2*m^3) (hd : d≤ (m:ℝ)^A) :
    tests (volume m A i)*GreedyBatchScaleTails.failure m≤ probability m d t/(m:ℝ) := by
  apply penalty m A (volume m A i) d t C P h _ hd (volume_exp m A i hm hi)
  dsimp [increment] at hm
  omega

#print axioms probability_lower
#print axioms penalty_exp
#print axioms logarithmic_budget
#print axioms exponential_small
#print axioms penalty
#print axioms volume_penalty
end
end Erdos773.GreedyBatchFailurePenalty
