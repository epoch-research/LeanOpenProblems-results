import Submission.WidePrimePools

/-!
# Distribution in the wide two-prime modulus family

This is a below-square-root estimate with a fixed reciprocal mass.  The
one-prime conductor groups are controlled separately from the two-prime group.
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators
namespace Erdos821
open AnalyticSieve
set_option maxHeartbeats 3000000

def wideLiftConstant : ℕ := 8*64*40020*64*20004

def wideErrorConstant : ℕ :=
  2*(130*10003)*wideMeanConstant 40020+wideMeanConstant 40020+wideLiftConstant

lemma wide_pool_primitive_bounds (m : ℕ) :
    let E : ℝ := (wideMeanConstant 40020 : ℝ)*((m : ℝ)+1)^5*(2 : ℝ)^(2561279*m)
    primitivePoolMean (wideLeftPool m) (progressionScaleN (40020*m)) ≤ E ∧
    primitivePoolMean (wideRightPool m) (progressionScaleN (40020*m)) ≤ E ∧
    primitivePoolMean (wideProductPool m) (progressionScaleN (40020*m)) ≤ E := by
  dsimp only
  refine ⟨?_,?_,?_⟩
  · exact wide_primitive_mean_bound _ 10000 10002 40020 m (by decide) (by decide)
      (by decide) (by decide) (by decide) (fun p hp => widePrimePools_bounds m p (Or.inl hp))
  · exact wide_primitive_mean_bound _ 10000 10002 40020 m (by decide) (by decide)
      (by decide) (by decide) (by decide) (fun p hp => widePrimePools_bounds m p (Or.inr hp))
  · exact wide_primitive_mean_bound _ 20000 20004 40020 m (by decide) (by decide)
      (by decide) (by decide) (by decide) (wideProductPool_bounds m)

lemma wide_product_lift_bound (m : ℕ) :
    8*((wideProductPool m).card : ℝ)*(Nat.log 2 (progressionScaleN (40020*m)) : ℝ)*
      Real.log (progressionScaleN (20004*m)) ≤
    (wideLiftConstant : ℝ)*((m : ℝ)+1)^6*(2 : ℝ)^(2561279*m) := by
  have hc : ((wideProductPool m).card : ℝ) ≤ (2 : ℝ)^(2561279*m) := by
    apply (show ((wideProductPool m).card : ℝ) ≤ progressionScaleN (20004*m) by
      exact_mod_cast wideProductPool_card_le m).trans
    simp only [progressionScaleN, Nat.cast_pow, Nat.cast_ofNat]
    apply pow_le_pow_right₀ (by norm_num)
    omega
  have hlog := log_two_pow_le (64*(20004*m))
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hlog
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  have hz : 1 ≤ (m : ℝ)+1 := by linarith
  have hm26 : (m : ℝ)^2 ≤ ((m : ℝ)+1)^6 :=
    (pow_le_pow_left₀ hm (by linarith) 2).trans (pow_le_pow_right₀ hz (by decide))
  simp only [progressionScaleN, Nat.log_pow (by decide : 1 < 2), Nat.cast_mul, Nat.cast_ofNat]
  calc
    _ ≤ 8*((2 : ℝ)^(2561279*m))*(64*(40020*(m : ℝ)))*(64*(20004*(m : ℝ))) := by gcongr
    _ = (wideLiftConstant : ℝ)*(m : ℝ)^2*(2 : ℝ)^(2561279*m) := by norm_num [wideLiftConstant]; ring
    _ ≤ _ := by gcongr

lemma wide_composite_error_bound (m : ℕ) :
    (∑ d ∈ wideProductPool m, compositeProgressionError d (progressionScaleN (40020*m))) ≤
      (wideErrorConstant : ℝ)*((m : ℝ)+1)^6*(2 : ℝ)^(2561279*m) := by
  let z : ℝ := (m : ℝ)+1
  let F : ℝ := (2 : ℝ)^(2561279*m)
  let C : ℝ := wideMeanConstant 40020
  let W : ℝ := 130*10003
  have hz : 1 ≤ z := by dsimp [z]; linarith [Nat.cast_nonneg (α := ℝ) m]
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hC : 0 ≤ C := Nat.cast_nonneg _
  have hW : 0 ≤ W := by dsimp [W]; norm_num
  have hm := wide_pool_primitive_bounds m
  change primitivePoolMean (wideLeftPool m) _ ≤ C*z^5*F ∧
    primitivePoolMean (wideRightPool m) _ ≤ C*z^5*F ∧ primitivePoolMean (wideProductPool m) _ ≤ C*z^5*F at hm
  have hleft : poolTotientMass (wideLeftPool m) ≤ W*z := by
    have h := widePrimePool_mass_upper 10000 10001 m
    change poolTotientMass (wideLeftPool m) ≤ _ at h
    apply h.trans
    dsimp [W,z]
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  have hright : poolTotientMass (wideRightPool m) ≤ W*z := by
    simpa only [W,z,wideRightPool,Nat.cast_ofNat,show (10002 : ℝ)+1 = 10003 by norm_num] using widePrimePool_mass_upper 10001 10002 m
  have herror := pair_composite_error_le _ _ (wideLeftPool_prime m) (wideRightPool_prime m)
    (widePools_disjoint m) (progressionScaleN (40020*m)) (progressionScaleN (20004*m))
    (fun d hd => (wideProductPool_bounds m d hd).2.2)
  change (∑ d ∈ wideProductPool m, compositeProgressionError d (progressionScaleN (40020*m))) ≤ _ at herror
  rw [← wideProductPool] at herror
  have hmean56 := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hz (by decide : 5 ≤ 6)) hC) hF
  have h1 := mul_le_mul hright hm.1 (primitivePoolMean_nonneg _ _) (mul_nonneg hW (by linarith : 0 ≤ z))
  have h2 := mul_le_mul hleft hm.2.1 (primitivePoolMean_nonneg _ _) (mul_nonneg hW (by linarith : 0 ≤ z))
  have hlift := wide_product_lift_bound m
  change _ ≤ (wideLiftConstant : ℝ)*z^6*F at hlift
  have heq : W*z*(C*z^5*F) = W*C*z^6*F := by ring
  rw [heq] at h1 h2
  have heqC : (wideErrorConstant : ℝ) = 2*W*C+C+wideLiftConstant := by
    simp only [wideErrorConstant, W,C,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  change _ ≤ (wideErrorConstant : ℝ)*z^6*F
  rw [heqC]
  nlinarith only [herror,h1,h2,hm.2.2,hmean56,hlift]

lemma eventually_wide_composite_error_small :
    ∀ᶠ m : ℕ in atTop,
      (∑ d ∈ wideProductPool m, compositeProgressionError d (progressionScaleN (40020*m))) ≤
        (progressionScaleN (40020*m) : ℝ)/(64*wideMassDenominator) := by
  filter_upwards [eventually_nat_poly_le_two_pow 1 (64*wideMassDenominator*wideErrorConstant) 6] with m hpoly
  have hpolyR : (64*(wideMassDenominator : ℝ)*wideErrorConstant)*((m : ℝ)+1)^6 ≤ (2 : ℝ)^m := by
    exact_mod_cast (show (64*wideMassDenominator*wideErrorConstant)*(m+1)^6 ≤ 2^m by simpa only [one_mul] using hpoly)
  apply (wide_composite_error_bound m).trans
  apply (le_div_iff₀ (by norm_num [wideMassDenominator] : (0 : ℝ) < 64*wideMassDenominator)).mpr
  calc
    _ = ((64*(wideMassDenominator : ℝ)*wideErrorConstant)*((m : ℝ)+1)^6)*(2 : ℝ)^(2561279*m) := by ring
    _ ≤ (2 : ℝ)^m*(2 : ℝ)^(2561279*m) := mul_le_mul_of_nonneg_right hpolyR (by positivity)
    _ = _ := by simp only [progressionScaleN,Nat.cast_pow,Nat.cast_ofNat,← pow_add]; congr 1; omega

/-- Positive aggregate prime-progression weight with no logarithmic mass loss. -/
theorem eventually_wide_progression_lower :
    ∀ᶠ m : ℕ in atTop,
      (7/8 : ℝ)*(progressionScaleN (40020*m) : ℝ)*poolTotientMass (wideProductPool m) ≤
        ∑ d ∈ wideProductPool m, residueOneMangoldt d (progressionScaleN (40020*m)) := by
  filter_upwards [eventually_progression_mangoldt_nine_tenths 40020 (by decide),
    eventually_wide_composite_error_small, eventually_ge_atTop 1] with m hpsi he hm
  let N := progressionScaleN (40020*m)
  let W := poolTotientMass (wideProductPool m)
  have hW : 0 ≤ W := poolTotientMass_nonneg _
  have hmass := wideProductPool_mass_lower m hm
  have hmain := mul_le_mul_of_nonneg_right hpsi hW
  have hE : (∑ d ∈ wideProductPool m, compositeProgressionError d N) ≤ (N : ℝ)/64*W := by
    apply he.trans
    calc
      _ = (N : ℝ)/64*(1/(wideMassDenominator : ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hmass (by positivity)
  have htotal := composite_progression_total_lower (wideProductPool m)
    (fun d hd => by have := (wideProductPool_bounds m d hd).1; omega) N
  change mangoldtSum N*W-(∑ d ∈ wideProductPool m, compositeProgressionError d N) ≤ _ at htotal
  change (9/10 : ℝ)*(N : ℝ)*W ≤ mangoldtSum N*W at hmain
  change (7/8 : ℝ)*(N : ℝ)*W ≤ _
  have hNW : 0 ≤ (N : ℝ)*W := mul_nonneg (Nat.cast_nonneg _) hW
  linarith only [hmain,hE,htotal,hNW]

end Erdos821
