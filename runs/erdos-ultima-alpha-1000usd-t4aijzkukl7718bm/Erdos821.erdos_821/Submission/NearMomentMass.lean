import Submission.NearMomentScales

/-!
# Reciprocal mass at the nearly sharp moment scales

One subset order is selected at each scale. The divisor-function order w+1
is fixed; only the selected subset order is allowed to vary with the scale.
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators
namespace Erdos821
open AnalyticSieve HigherDivisors
set_option maxHeartbeats 4000000

lemma nearMomentP_mass_upper (A m : ℕ) :
    poolTotientMass (nearMomentP A m) ≤ 1024+8*((A : ℝ)+20)*((m : ℝ)+5) := by
  let E := logMomentScale m
  have hE : 1 ≤ E := (by decide : 1 ≤ 32).trans (logMomentScale_ge m)
  have hsub : nearMomentP A m ⊆ (progressionScaleN (E^(A+20))+1).primesBelow := filter_subset _ _
  have hmass : poolTotientMass (nearMomentP A m) ≤ primeTotientMass (progressionScaleN (E^(A+20))) :=
    sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))
  have hup := primeTotientMass_scale_upper (E^(A+20)) (Nat.one_le_pow _ _ hE)
  rw [Nat.cast_pow,Real.log_pow] at hup
  have hlog : Real.log (E : ℝ) ≤ (m : ℝ)+5 := by
    simpa only [E,logMomentScale,Nat.cast_add,Nat.cast_ofNat] using log_two_pow_le (m+5)
  have h := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 8*((A+20 : ℕ) : ℝ) by positivity)
  push_cast at hup h
  nlinarith only [hmass,hup,h]

lemma nearMomentR_covers_mean (w A m : ℕ) :
    2*(w : ℝ)*poolTotientMass (nearMomentP A m) ≤ nearMomentR w A m := by
  have hmass := nearMomentP_mass_upper A m
  have hBz : (1 : ℝ) ≤ ((A : ℝ)+20)*((m : ℝ)+5) :=
    one_le_mul_of_one_le_of_one_le (by linarith [Nat.cast_nonneg (α := ℝ) A])
      (by linarith [Nat.cast_nonneg (α := ℝ) m])
  have h := mul_le_mul_of_nonneg_left hmass (show 0 ≤ 2*(w : ℝ) by positivity)
  have h' := mul_le_mul_of_nonneg_left hBz (show 0 ≤ 2048*(w : ℝ) by positivity)
  have hnon : 0 ≤ (w : ℝ)*((A : ℝ)+20)*((m : ℝ)+5) := by positivity
  simp only [nearMomentR,nearMomentC,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat]
  nlinarith only [h,h',hnon]

lemma eventually_nearMoment_large_mass (w A : ℕ) (hw : 1 ≤ w) :
    ∀ᶠ m : ℕ in atTop, ∃ r ≤ nearMomentR w A m,
      (logMomentScale m : ℝ)^(w*(A+9))/2 ≤
        (w : ℝ)^r*poolTotientMass (nearMomentPool A m r) := by
  have hevent := logMomentScale_tendsto.eventually (eventually_ge_atTop (2*w*(A+20)))
  filter_upwards [hevent,eventually_nearMomentR_add_one_le_scale w A,eventually_ge_atTop 2048]
    with m hEL hRE hm
  let E := logMomentScale m
  let P := nearMomentP A m
  let R := nearMomentR w A m
  let F : ℝ := ∏ p ∈ P, (1+(w : ℝ)*(p.totient : ℝ)⁻¹)
  have hE : (1 : ℝ) ≤ E := by exact_mod_cast ((by decide : 1 ≤ 32).trans (logMomentScale_ge m))
  have hL : 2*w*(A+20) ≤ progressionScaleN E := by
    apply hEL.trans
    exact Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hlogE : 1024 ≤ Real.log E := by
    have htwo : (1/2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hmR : (2048 : ℝ) ≤ m := by exact_mod_cast hm
    simp only [E,logMomentScale,Nat.cast_pow,Nat.cast_ofNat,Real.log_pow,Nat.cast_add]
    nlinarith only [mul_le_mul_of_nonneg_right htwo (show 0 ≤ (m : ℝ)+5 by positivity),hmR]
  have hF : (E : ℝ)^(w*(A+10)) ≤ F := by
    have h := powerPrimePool_euler_lower w (A+20) E hw (by omega) (by exact_mod_cast hE) hlogE hL
    simpa only [show A+20-10=A+10 by omega,P,nearMomentP,E,F] using h
  obtain ⟨r,hr,hmass⟩ := exists_large_primeSubset_mass P
    (fun p hp => (powerPrimePool_prime_bounds (A+20) E p hp).1) (w : ℝ) (Nat.cast_nonneg _)
    R (nearMomentR_pos w A m hw) (nearMomentR_covers_mean w A m)
  refine ⟨r,hr,le_trans ?_ hmass⟩
  change (E : ℝ)^(w*(A+9))/2 ≤ F/(2*((R : ℝ)+1))
  apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) (by positivity)).mpr
  have hREr : (R : ℝ)+1 ≤ E := by exact_mod_cast hRE
  have hEw : (E : ℝ) ≤ (E : ℝ)^w := by
    simpa only [pow_one] using pow_le_pow_right₀ hE hw
  have hh := mul_le_mul_of_nonneg_left (hREr.trans hEw)
    (show 0 ≤ (E : ℝ)^(w*(A+9)) by positivity)
  have he : (E : ℝ)^(w*(A+9))*(E : ℝ)^w = (E : ℝ)^(w*(A+10)) := by
    rw [← pow_add]
    congr 1
  rw [he] at hh
  nlinarith only [hh,hF]

/-- The resulting log-weighted moment has an arbitrarily large polynomial
power of the base scale as A increases. No order/scale quantifiers are exchanged. -/
theorem eventually_nearMoment_primeLog_lower (w A : ℕ) (hw : 1 ≤ w) :
    ∀ᶠ m : ℕ in atTop,
      (nearMomentX w A m : ℝ)*(logMomentScale m : ℝ)^(w*(A+8)) ≤
        primeLogDivisorMoment (w+1) (nearMomentX w A m) := by
  filter_upwards [eventually_nearMoment_large_mass w A hw,
    eventually_nearMoment_weighted_error_small w A hw] with m hmass herr
  obtain ⟨r,hr,hrmass⟩ := hmass
  let N := nearMomentX w A m
  let M := nearMomentPool A m r
  let E := logMomentScale m
  let W : ℝ := (w : ℝ)^r
  let S := poolTotientMass M
  let Z : ℝ := (E : ℝ)^(w*(A+8))
  have hN1 : 1 ≤ N := Nat.one_le_pow _ _ (by decide)
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hE32 : (32 : ℝ) ≤ E := by exact_mod_cast logMomentScale_ge m
  have hE1 : (1 : ℝ) ≤ E := by linarith
  have hEw : (E : ℝ) ≤ (E : ℝ)^w := by simpa only [pow_one] using pow_le_pow_right₀ hE1 hw
  have hZ : 1 ≤ Z := one_le_pow₀ hE1
  have hmainmass : 16*Z ≤ W*S := by
    have he : (E : ℝ)^(w*(A+9)) = Z*(E : ℝ)^w := by
      dsimp [Z]
      rw [← pow_add]
      congr 1
    change (E : ℝ)^(w*(A+9))/2 ≤ W*S at hrmass
    rw [he] at hrmass
    have hh := mul_le_mul_of_nonneg_left (hE32.trans hEw) (show 0 ≤ Z by linarith)
    nlinarith only [hrmass,hh]
  have hscale : 1 ≤ nearMomentT w A m*logMomentScale m :=
    Nat.mul_pos (nearMomentT_pos w A m hw) (by have := logMomentScale_ge m; omega)
  have hpsi : (N : ℝ)/8 ≤ mangoldtSum N := progression_scale_mangoldt_lower hscale
  have hmain : 2*(N : ℝ)*Z ≤ W*(mangoldtSum N*S) := by
    have h := mul_le_mul hpsi hmainmass (by positivity) (hpsi.trans' (by positivity))
    nlinarith only [h]
  have hp := composite_progression_total_lower M (fun d hd => (nearMomentPool_bounds w A m r hr d hd).1) N
  change mangoldtSum N*S-(∑ d ∈ M, compositeProgressionError d N) ≤ _ at hp
  have hpW := mul_le_mul_of_nonneg_left hp hW
  have hmoment := primeSubsetModuli_progression_le_moment (nearMomentP A m)
    (fun p hp => (powerPrimePool_prime_bounds _ _ p hp).1) w r (nearMomentQ w A m) N hN1
    (nearMomentPool_card_le w A m r hr)
  have he := herr r hr
  change W*((∑ d ∈ M, compositeProgressionError d N)+
    2*(nearMomentQ w A m : ℝ)*Real.sqrt N*Real.log N) ≤ (N : ℝ)/16 at he
  change W*(∑ d ∈ M, residueOneMangoldt d N) ≤
    primeLogDivisorMoment (w+1) N+W*(2*(nearMomentQ w A m : ℝ)*Real.sqrt N*Real.log N) at hmoment
  change (N : ℝ)*Z ≤ _
  have hNZ := mul_le_mul_of_nonneg_left hZ hN0
  nlinarith only [hmain,hpW,hmoment,he,hNZ]

end Erdos821
