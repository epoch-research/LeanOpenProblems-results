import Submission.RoughHalfMean

/-!
# Power-saving errors for arbitrary rough pools below the half level

A narrow-interval conductor cover removes the former 32*b<=t restriction.
The remaining condition 2*b+5<=t is a strict below-square-root condition.
-/
open Nat Finset Filter ArithmeticFunction
open scoped Classical BigOperators Topology
namespace Erdos821
open AnalyticSieve
set_option maxHeartbeats 3000000

theorem rough_pool_below_half_combined_error (D : Finset ℕ) (a b t E : ℕ)
    (ha : 1 ≤ a) (hab : a ≤ b) (ht : 22 ≤ t) (hE : 1 ≤ E) (hbt : 2*b+5 ≤ t)
    (hD : ∀ d ∈ D, 0 < d ∧ d ≤ progressionScaleN (b*E))
    (hrough : ∀ d ∈ D, ∀ c ∈ d.divisors.erase 1, progressionScaleN (a*E) ≤ c) :
    (∑ d ∈ D, compositeProgressionError d (progressionScaleN (t*E)))+
      2*(progressionScaleN (b*E) : ℝ)*Real.sqrt (progressionScaleN (t*E))*
        Real.log (progressionScaleN (t*E)) ≤
      1000000000000000*(((t : ℝ)+1)*((E : ℝ)+1))^7*(2 : ℝ)^((64*t-1)*E) := by
  let Q := progressionScaleN (b*E)
  let N := progressionScaleN (t*E)
  let L := progressionScaleN (a*E)
  let F : ℝ := (2 : ℝ)^((64*t-1)*E)
  let z : ℝ := ((t : ℝ)+1)*((E : ℝ)+1)
  have hz : 1 ≤ z := one_le_mul_of_one_le_of_one_le (by linarith [Nat.cast_nonneg (α := ℝ) t])
    (by linarith [Nat.cast_nonneg (α := ℝ) E])
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hL : 2 ≤ L := by
    change 2 ≤ 2^(64*(a*E))
    exact Nat.le_pow (Nat.mul_pos (by decide) (Nat.mul_pos ha hE))
  have hbt' : b ≤ t := by omega
  have hQF : (Q : ℝ) ≤ F := by
    simp only [Q,progressionScaleN,Nat.cast_pow,Nat.cast_ofNat,F]
    apply pow_le_pow_right₀ (by norm_num)
    simpa only [mul_assoc] using Nat.mul_le_mul_right E (by omega : 64*b ≤ 64*t-1)
  have hQsqrt : (Q : ℝ)*Real.sqrt N ≤ F := by
    change (Q : ℝ)*Real.sqrt (progressionScaleN (t*E)) ≤ F
    rw [sqrt_progressionScaleN]
    simp only [Q,progressionScaleN,Nat.cast_pow,Nat.cast_ofNat,← pow_add]
    apply pow_le_pow_right₀ (by norm_num)
    have h : 64*b+32*t ≤ 64*t-1 := by omega
    nlinarith only [Nat.mul_le_mul_right E h]
  have hQ1 : (1 : ℝ) ≤ Q := by
    simp only [Q,progressionScaleN,Nat.cast_pow,Nat.cast_ofNat]
    exact one_le_pow₀ (by norm_num)
  have hzprod : (t : ℝ)*(E : ℝ) ≤ z := by
    dsimp [z]
    nlinarith [Nat.cast_nonneg (α := ℝ) t,Nat.cast_nonneg (α := ℝ) E]
  have hlogN : Real.log N ≤ 64*z := by
    have h := log_two_pow_le (64*(t*E))
    change Real.log N ≤ _ at h
    push_cast at h
    nlinarith only [h,hzprod]
  have hlogQ : Real.log Q ≤ 64*z :=
    (log_nat_mono (progressionScaleN_monotone (Nat.mul_le_mul_right E hbt'))).trans hlogN
  have hlogNat : (Nat.log 2 N : ℝ) ≤ 64*z := by
    simp only [N,progressionScaleN,Nat.log_pow (by decide : 1 < 2),Nat.cast_mul,Nat.cast_ofNat]
    nlinarith only [hzprod]
  have hH : (harmonic Q : ℝ) ≤ 65*z := by
    have h := harmonic_le_one_add_log Q
    linarith only [h,hlogQ,hz]
  have hH0 : (0 : ℝ) ≤ harmonic Q := harmonic_real_nonneg Q
  have hmean := interval_primitive_mean_below_half a b t E ha hab ht hbt hE
  have hmean' : primitivePoolMean (Icc L Q) N ≤ 4000000000000*z^6*F := by
    have hzB : ((b+1 : ℕ) : ℝ) ≤ z := by
      have hbR : (b : ℝ) ≤ t := by exact_mod_cast hbt'
      dsimp [z]
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) E]
    apply hmean.trans
    have heq : (wideMeanConstant t : ℝ)*((E : ℝ)+1)^5 = 4000000000000*z^5 := by
      simp only [wideMeanConstant,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_add,
        Nat.cast_one,z,mul_pow]
      ring
    rw [mul_assoc (((b+1 : ℕ) : ℝ)) _ _,heq]
    have hh := mul_le_mul_of_nonneg_right hzB (show 0 ≤ 4000000000000*z^5*F by positivity)
    convert hh using 1 <;> ring
  have hmain : (2*(harmonic Q : ℝ))*primitivePoolMean (Icc L Q) N ≤
      520000000000000*z^7*F := by
    calc
      _ ≤ (2*(65*z))*(4000000000000*z^6*F) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hH (by norm_num)) hmean'
          (primitivePoolMean_nonneg _ _) (by positivity)
      _ = _ := by ring
  have hlift : 2*((Q : ℝ)+1)*(harmonic Q : ℝ)*(Nat.log 2 N : ℝ)*Real.log Q ≤
      1064960*z^3*F := by
    have hQ2 : (Q : ℝ)+1 ≤ 2*F := by linarith only [hQ1,hQF]
    calc
      _ ≤ 2*(2*F)*(65*z)*(64*z)*(64*z) := by
        gcongr
      _ = _ := by ring
  have hpower : 2*(Q : ℝ)*Real.sqrt N*Real.log N ≤ 128*z*F := by
    calc
      _ = 2*((Q : ℝ)*Real.sqrt N)*Real.log N := by ring
      _ ≤ 2*F*(64*z) := by gcongr
      _ = _ := by ring
  have herr := rough_composite_error_le D L Q N hL hD hrough
  have hz36 : z^3*F ≤ z^7*F := mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ hz (by decide)) hF
  have hz16 : z*F ≤ z^7*F := by
    simpa only [pow_one] using mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ hz (by decide : 1 ≤ 7)) hF
  have hnon : 0 ≤ z^7*F := by positivity
  change _ ≤ 1000000000000000*z^7*F
  nlinarith only [herr,hmain,hlift,hpower,hz36,hz16,hnon]

end Erdos821
