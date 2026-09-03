import Submission.NearSharpMomentPowers

/-!
# Finite conditions for the near-critical moment construction

These statements make the dependence on the auxiliary parameter explicit.
They may therefore be used with a parameter that grows with the scale.
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators
namespace Erdos821
open AnalyticSieve HigherDivisors
set_option maxHeartbeats 4000000

def nearMomentBudget (w A m : ℕ) : ℕ :=
  16*1000000000000000*(64*nearMomentC w A+1)^6*
    (logMomentScale m+1)^(w*nearMomentC w A+6*(A+22))

lemma nearMoment_weighted_error_of_budget (w A m : ℕ) (hw : 1 ≤ w)
    (hbudget : nearMomentBudget w A m ≤ 2^(logMomentScale m)) :
    ∀ r ≤ nearMomentR w A m,
      (w : ℝ)^r*((∑ d ∈ nearMomentPool A m r, compositeProgressionError d (nearMomentX w A m))+
        2*(nearMomentQ w A m : ℝ)*Real.sqrt (nearMomentX w A m)*Real.log (nearMomentX w A m)) ≤
          (nearMomentX w A m : ℝ)/16 := by
  intro r hr
  let C := nearMomentC w A
  let D := 16*1000000000000000*(64*C+1)^6
  let n := w*C+6*(A+22)
  let E := logMomentScale m
  let F : ℝ := (2 : ℝ)^((64*nearMomentT w A m-1)*E)
  have hpoly : (D : ℝ)*((E : ℝ)+1)^n ≤ (2 : ℝ)^E := by
    exact_mod_cast (show D*(E+1)^n ≤ 2^E from hbudget)
  have hwR : (w : ℝ)^r ≤ ((E : ℝ)+1)^(w*C) := by
    have h : (w : ℝ)^r ≤ (E : ℝ)^(w*C) := by exact_mod_cast nearMoment_weight_bound w A m r hw hr
    exact h.trans (pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith) _)
  have herr := nearMoment_combined_error_bound w A m r hw hr
  have hscaled := mul_le_mul hwR herr (by
    exact add_nonneg (sum_nonneg (fun d hd => (abs_nonneg _).trans
      (composite_progression_discrepancy d (nearMomentX w A m)
        (nearMomentPool_bounds w A m r hr d hd).1))) (by positivity)) (by positivity)
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 16)).mpr
  calc
    _ ≤ (((E : ℝ)+1)^(w*C)*(1000000000000000*(64*(C : ℝ)+1)^6*
        ((E : ℝ)+1)^(6*(A+22))*F))*16 := mul_le_mul_of_nonneg_right hscaled (by norm_num)
    _ = ((D : ℝ)*((E : ℝ)+1)^n)*F := by
      simp only [D,n,Nat.cast_mul,Nat.cast_pow,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,pow_add]
      ring
    _ ≤ (2 : ℝ)^E*F := mul_le_mul_of_nonneg_right hpoly (by positivity)
    _ = _ := by
      simp only [F,nearMomentX,progressionScaleN,Nat.cast_pow,Nat.cast_ofNat,← pow_add]
      apply congrArg (fun e : ℕ => (2 : ℝ)^e)
      have ht := nearMomentT_pos w A m hw
      have hs := Nat.sub_add_cancel (show 1 ≤ 64*nearMomentT w A m by omega)
      change E+(64*nearMomentT w A m-1)*E = 64*(nearMomentT w A m*E)
      nlinarith only [hs]

lemma nearMoment_large_mass_of_conditions (w A m : ℕ) (hw : 1 ≤ w)
    (hEL : 2*w*(A+20) ≤ logMomentScale m)
    (hRE : nearMomentR w A m+1 ≤ logMomentScale m) (hm : 2048 ≤ m) :
    ∃ r ≤ nearMomentR w A m,
      (logMomentScale m : ℝ)^(w*(A+9))/2 ≤
        (w : ℝ)^r*poolTotientMass (nearMomentPool A m r) := by
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

lemma nearMoment_primeLog_lower_of_conditions (w A m : ℕ) (hw : 1 ≤ w)
    (hEL : 2*w*(A+20) ≤ logMomentScale m)
    (hRE : nearMomentR w A m+1 ≤ logMomentScale m) (hm : 2048 ≤ m)
    (hbudget : nearMomentBudget w A m ≤ 2^(logMomentScale m)) :
    (nearMomentX w A m : ℝ)*(logMomentScale m : ℝ)^(w*(A+8)) ≤
      primeLogDivisorMoment (w+1) (nearMomentX w A m) := by
  have hmass := nearMoment_large_mass_of_conditions w A m hw hEL hRE hm
  have herr := nearMoment_weighted_error_of_budget w A m hw hbudget
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

lemma log_nearMomentX_le_of_conditions (w A m : ℕ)
    (hR : nearMomentR w A m+1 ≤ logMomentScale m) (hE : 4096 ≤ logMomentScale m) :
    Real.log (nearMomentX w A m : ℝ) ≤ (logMomentScale m : ℝ)^(A+23) := by
  let E := logMomentScale m
  have hRR : (nearMomentR w A m : ℝ) ≤ E := by exact_mod_cast (show nearMomentR w A m ≤ E by omega)
  have hER : (4096 : ℝ) ≤ E := by exact_mod_cast hE
  have hlog := log_two_pow_le (64*(nearMomentT w A m*E))
  change Real.log (nearMomentX w A m : ℝ) ≤ _ at hlog
  simp only [nearMomentT,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] at hlog
  calc
    _ ≤ 4096*(nearMomentR w A m : ℝ)*(E : ℝ)^(A+21) := by
      convert hlog using 1
      rw [show A+21=(A+20)+1 by omega,pow_succ _ (A+20)]
      ring
    _ ≤ (E : ℝ)*(E : ℝ)*(E : ℝ)^(A+21) := by gcongr
    _ = _ := by
      change _ = (E : ℝ)^(A+23)
      rw [show A+23=(A+21)+2 by omega,pow_add _ (A+21) 2,pow_two]
      ring

end Erdos821
