import Submission.FirstHitTwoScaleMain
import Submission.FirstHitTwoScaleCost

/-! A rigorously extended first-hit endpoint. The exponent improves slightly
from 54/25 to 539/250, which remains strictly greater than two. -/
namespace Erdos970.FiniteSelberg
open Finset Real

noncomputable def endpointPrimeCut (L : ℝ) : ℕ := ⌊exp (L/(539/250 : ℝ))⌋₊
noncomputable def endpointMainSum (L : ℝ) : ℝ :=
  ∑ p ∈ (endpointPrimeCut L+1).primesBelow,
    (1/(p : ℝ))/primeNormalizer p.primesBelow (twoScaleCutoff L p)
noncomputable def endpointTailError : ℝ :=
  (7/2 : ℝ)*(WeightedMertens.boundConstant+1)*(54/25 : ℝ)^2
noncomputable def endpointTotalError : ℝ :=
  saturatedHitTotalError+WeightedMertens.sharpMomentError+endpointTailError
noncomputable def endpointMainMargin : ℝ :=
  saturatedHitMainMargin-1/10000-7/1000

lemma endpointMainMargin_gt : (6/10000 : ℝ) < endpointMainMargin := by
  norm_num [endpointMainMargin,saturatedHitMainMargin,saturatedEarlyMain]

lemma endpointTotalError_nonneg : 0 ≤ endpointTotalError := by
  have h1 := saturatedHitTotalError_nonneg
  have h2 := WeightedMertens.sharpMomentError_pos
  have h3 := WeightedMertens.boundConstant_pos
  unfold endpointTotalError endpointTailError
  positivity

lemma saturated_zero_cut (L : ℝ) : saturatedHitPrimeCut L 0 = ⌊exp (L/(54/25 : ℝ))⌋₊ := by
  norm_num [saturatedHitPrimeCut,saturatedHitNode]

lemma old_cut_le_endpoint (L : ℝ) (hL : 0 ≤ L) :
    saturatedHitPrimeCut L 0 ≤ endpointPrimeCut L := by
  rw [saturated_zero_cut,endpointPrimeCut]
  apply Nat.floor_le_floor
  apply exp_le_exp.mpr
  linarith

lemma endpoint_log_bound (L : ℝ) (p : ℕ) (hp : 0 < p) (hbound : p ≤ endpointPrimeCut L) :
    log (p : ℝ) ≤ L/(539/250 : ℝ) := by
  have hh := log_le_log (show (0 : ℝ) < p by exact_mod_cast hp)
    ((show (p : ℝ) ≤ endpointPrimeCut L by exact_mod_cast hbound).trans
      (Nat.floor_le (exp_pos (L/(539/250 : ℝ))).le))
  rwa [log_exp] at hh

lemma endpoint_band_logs (L : ℝ) (p : ℕ)
    (hp : p ∈ (Ioc (saturatedHitPrimeCut L 0) (endpointPrimeCut L)).filter Nat.Prime) :
    p.Prime ∧ L/(54/25 : ℝ) < log (p : ℝ) ∧ log (p : ℝ) ≤ L/(539/250 : ℝ) := by
  obtain ⟨hpi,hpp⟩ := mem_filter.mp hp
  obtain ⟨hlo,hhi⟩ := mem_Ioc.mp hpi
  have he : exp (L/(54/25 : ℝ)) < (p : ℝ) := by
    rw [saturated_zero_cut] at hlo
    exact Nat.lt_of_floor_lt hlo
  have hh := log_lt_log (exp_pos _) he
  rw [log_exp] at hh
  exact ⟨hpp,hh,endpoint_log_bound L p hpp.pos hhi⟩

lemma endpoint_band_mean_le (L : ℝ) (hL : 0 < L)
    (hthreshold : 50000*firstHitProfileError ≤ L) (p : ℕ)
    (hp : p ∈ (Ioc (saturatedHitPrimeCut L 0) (endpointPrimeCut L)).filter Nat.Prime) :
    (1/(p : ℝ))/primeNormalizer p.primesBelow (twoScaleCutoff L p) ≤
      (7/4 : ℝ)*(1/((p : ℝ)*log p)) := by
  obtain ⟨hpp,hlo,hhi⟩ := endpoint_band_logs L p hp
  have hlp : 0 < log (p : ℝ) := log_pos (by exact_mod_cast hpp.one_lt)
  let u := (L/log (p : ℝ)-1)/2
  have he : (L/log (p : ℝ))*log (p : ℝ) = L := div_mul_cancel₀ _ hlp.ne'
  have hu : (289/500 : ℝ) ≤ u := by dsimp [u]; nlinarith only [he,hhi,hlp]
  have hu' : u ≤ 29/50 := by dsimp [u]; nlinarith only [he,hlo,hlp]
  have harg : (L-log (p : ℝ))/2 = u*log (p : ℝ) := by dsimp [u]; field_simp
  have hLp : 20000*firstHitProfileError ≤ log (p : ℝ) := by
    have hh := firstHitProfileError_ge_one
    linarith
  have hrec := (firstHitCutoff_reciprocal_upper_eleven_twentieths L u p hpp hLp
    (by linarith) (by linarith) harg).2
  have hu1 : u ≤ 1 := by linarith
  rw [firstHitFullProfile,if_pos hu1] at hrec
  have hcoeff : (10001/10000 : ℝ)*(1/u) ≤ 7/4 := by
    have hu0 : 0 < u := by linarith
    apply (mul_le_mul_iff_right₀ hu0).mp
    field_simp
    nlinarith only [hu]
  have hrec' := hrec.trans (div_le_div_of_nonneg_right hcoeff hlp.le)
  have hsmall : ¬log (p : ℝ) ≤ L/100 := by linarith
  simp only [twoScaleCutoff,twoScaleParameter,if_neg hsmall]
  have hh := mul_le_mul_of_nonneg_left hrec' (show 0 ≤ 1/(p : ℝ) by positivity)
  convert hh using 1 <;> ring

lemma endpoint_band_sum_le (L : ℝ) (hL : 100 ≤ L)
    (hthreshold : 50000*firstHitProfileError ≤ L) :
    (∑ p ∈ (Ioc (saturatedHitPrimeCut L 0) (endpointPrimeCut L)).filter Nat.Prime,
      (1/(p : ℝ))/primeNormalizer p.primesBelow (twoScaleCutoff L p)) ≤
        (7/1000 : ℝ)/L+endpointTailError/L^2 := by
  have hL0 : 0 < L := by linarith
  have ha : 2 ≤ exp (L/(54/25 : ℝ)) := by linarith [add_one_le_exp (L/(54/25 : ℝ))]
  have hab : exp (L/(54/25 : ℝ)) ≤ exp (L/(539/250 : ℝ)) := exp_le_exp.mpr (by linarith)
  have hh := (abs_le.mp (WeightedMertens.abs_inverseLogPrimeInterval_sub 0 ha hab)).2
  simp only [WeightedMertens.inverseLogPrimeInterval,Nat.cast_zero,
    zero_add,pow_one,div_one,log_exp,← saturated_zero_cut] at hh
  rw [← endpointPrimeCut] at hh
  have hs := sum_le_sum (fun p hp => endpoint_band_mean_le L hL0 hthreshold p hp)
  rw [← mul_sum] at hs
  have hm := mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 7/4)
  have he1 : (7/4 : ℝ)*(1/(L/(54/25 : ℝ))-1/(L/(539/250 : ℝ))) = (7/1000 : ℝ)/L := by ring
  have he2 : (7/4 : ℝ)*(2*(WeightedMertens.boundConstant+1)/(L/(54/25 : ℝ))^2) =
      endpointTailError/L^2 := by unfold endpointTailError; ring
  rw [mul_sub,he2] at hm
  linarith only [hs,hm,he1]

/-- Keep the original finite margin instead of its earlier coarse slack. -/
lemma exists_twoScale_full_margin : ∃ M : ℝ, 100 ≤ M ∧ ∀ L : ℝ, M ≤ L →
    twoScaleMainSum L ≤ 1-(saturatedHitMainMargin-1/10000)/L+
      (saturatedHitTotalError+WeightedMertens.sharpMomentError)/L^2 := by
  obtain ⟨W,hW2,hthreshold,hEuler⟩ := exists_saturatedHit_threshold_wheel
  have hW : 0 < W := by omega
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hlogW : 0 ≤ log (W : ℝ) := log_nonneg (by exact_mod_cast (show 1 ≤ W by omega))
  have hlogQ : 0 ≤ log (firstHitWheel W : ℝ) := log_nonneg (by exact_mod_cast firstHitWheel_pos W)
  have hlogW2 : 0 ≤ log ((W : ℝ)+2) := log_nonneg (by have := Nat.cast_nonneg (α := ℝ) W; linarith)
  let M := 100+9*log ((W : ℝ)+2)+4*log (firstHitWheel W : ℝ)+2*log (W : ℝ)
  have hM : 100 ≤ M := by dsimp [M]; linarith
  refine ⟨M,hM,?_⟩
  intro L hML
  have hL : 0 < L := by linarith
  have hlarge : 9*log ((W : ℝ)+2) ≤ L := by dsimp [M] at hML; linarith
  have hWheel : 2*log (firstHitWheel W : ℝ)+log (W : ℝ) ≤ L/2 := by dsimp [M] at hML; linarith
  have hsmall : 9*log (2 : ℝ) ≤ L := by
    have hh := log_le_log (by norm_num : (0 : ℝ) < 2)
      (show (2 : ℝ) ≤ (W : ℝ)+2 by have := Nat.cast_nonneg (α := ℝ) W; linarith)
    linarith
  have hWF : W ≤ firstHitFarCut L := by
    have hwlog := log_le_log hW0 (show (W : ℝ) ≤ (W : ℝ)+2 by linarith)
    have hh : (W : ℝ) ≤ exp (L/9) := by
      calc
        (W : ℝ) = exp (log (W : ℝ)) := (exp_log hW0).symm
        _ ≤ exp (L/9) := exp_le_exp.mpr (by linarith)
    exact Nat.le_floor hh
  have hs := saturatedHitMainSum_finite_bound L hL hsmall W hW hWF
    (by linarith : 2*log (firstHitWheel W : ℝ)+log (W : ℝ) ≤ L) hthreshold hEuler
  have ht := twoScale_small_excess_bound L hL W hW hWheel hthreshold
  have hu := twoScaleMainSum_le L
  linear_combination hs+ht+hu

/-- Positive slack at the larger endpoint exp(250L/539), with both the new
prime annulus and all earlier main-term errors retained. -/
theorem exists_endpointMainSum_slack : ∃ L₀ : ℝ, 100 ≤ L₀ ∧
    ∀ L : ℝ, L₀ ≤ L → endpointMainSum L ≤ 1-1/(2000*L) := by
  obtain ⟨M,hM,hmain⟩ := exists_twoScale_full_margin
  let L₀ := M+50000*firstHitProfileError+10000*endpointTotalError
  have hL₀ : 100 ≤ L₀ := by
    dsimp [L₀]
    have := firstHitProfileError_ge_one
    have := endpointTotalError_nonneg
    linarith
  refine ⟨L₀,hL₀,?_⟩
  intro L hLL
  have hM' : M ≤ L := by
    dsimp [L₀] at hLL
    have := firstHitProfileError_ge_one
    have := endpointTotalError_nonneg
    linarith
  have hL : 100 ≤ L := hM.trans hM'
  have hL0 : 0 < L := by linarith
  have hthreshold : 50000*firstHitProfileError ≤ L := by
    dsimp [L₀] at hLL
    have := endpointTotalError_nonneg
    linarith
  have herror : 10000*endpointTotalError ≤ L := by
    dsimp [L₀] at hLL
    have := firstHitProfileError_ge_one
    linarith
  have he : endpointMainSum L =
      (∑ p ∈ (Ioc (saturatedHitPrimeCut L 0) (endpointPrimeCut L)).filter Nat.Prime,
        (1/(p : ℝ))/primeNormalizer p.primesBelow (twoScaleCutoff L p))+twoScaleMainSum L :=
    sum_initial_primes_split _ _ (old_cut_le_endpoint L hL0.le) _
  have hs := endpoint_band_sum_le L hL hthreshold
  have ht := hmain L hM'
  have hfinite : endpointMainSum L ≤ 1-endpointMainMargin/L+endpointTotalError/L^2 := by
    rw [he]
    unfold endpointMainMargin endpointTotalError
    linear_combination hs+ht
  have herr : endpointTotalError/L^2 ≤ 1/(10000*L) := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hL0) (by positivity)).mpr
    nlinarith only [mul_nonneg hL0.le (sub_nonneg.mpr herror)]
  have hmargin := div_le_div_of_nonneg_right endpointMainMargin_gt.le hL0.le
  linear_combination hfinite+herr+hmargin

#print axioms endpoint_band_sum_le
#print axioms exists_twoScale_full_margin
#print axioms exists_endpointMainSum_slack
end Erdos970.FiniteSelberg
