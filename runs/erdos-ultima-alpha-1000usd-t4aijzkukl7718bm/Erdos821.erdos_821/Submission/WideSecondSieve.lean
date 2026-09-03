import Submission.WideIncidences

/-!
# Retaining smooth shifted primes from the wide modulus family

The count loses only one logarithm.  The smoothness ratio is fixed, not
arbitrarily small, so this result does not settle the original conjecture.
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators
namespace Erdos821
open AnalyticSieve HigherDivisors
set_option maxHeartbeats 3000000

noncomputable def wideSieveMain (m : ℕ) : ℝ := independentSieveMain 40020 19396 620 m
noncomputable def wideSieveError (m : ℕ) : ℝ :=
  ((wideProductPool m).card : ℝ)*(2 : ℝ)^(64*620*m)*
    ((2 : ℝ)^(64*(19395*m))+(2 : ℝ)^(16*(19395*m))+1)

lemma wideProductPool_smooth_odd (m d : ℕ) (hm : 1 ≤ m) (hd : d ∈ wideProductPool m) :
    d ∈ Nat.smoothNumbers (progressionScaleN (19400*m)) ∧ Odd d := by
  obtain ⟨⟨p,q⟩,hpq,rfl⟩ := mem_image.mp hd
  obtain ⟨hp,hq⟩ := mem_product.mp hpq
  have hpb := widePrimePools_bounds m p (Or.inl hp)
  have hqb := widePrimePools_bounds m q (Or.inr hq)
  have hY : progressionScaleN (10002*m) < progressionScaleN (19400*m) := by
    unfold progressionScaleN
    apply Nat.pow_lt_pow_right (by decide)
    omega
  have hD : 2 < progressionScaleN (10000*m) := by
    change 2^1 < 2^(64*(10000*m))
    exact Nat.pow_lt_pow_right (by decide) (by omega)
  have hps := Nat.mem_smoothNumbers_of_lt (by omega : 0 < p) (hpb.2.2.trans_lt hY)
  have hqs := Nat.mem_smoothNumbers_of_lt (by omega : 0 < q) (hqb.2.2.trans_lt hY)
  refine ⟨Nat.mul_mem_smoothNumbers hps hqs,?_⟩
  exact ((wideLeftPool_prime m p hp).odd_of_ne_two (by omega)).mul
    ((wideRightPool_prime m q hq).odd_of_ne_two (by omega))

lemma wide_rough_count_le (m : ℕ) (hm : 1 ≤ m) (hend : EndpointPairAt (19395*m)) :
    (∑ d ∈ wideProductPool m,
      ((roughProgressionPrimes d (progressionScaleN (19400*m)) (progressionScaleN (40020*m))).card : ℝ)) ≤
      wideSieveMain m*poolTotientMass (wideProductPool m)+wideSieveError m := by
  have hM (d : ℕ) (hd : d ∈ wideProductPool m) :
      0 < d ∧ progressionScaleN (20000*m) ≤ d ∧ d ≤ progressionScaleN (20004*m) ∧
      d ∈ Nat.smoothNumbers (progressionScaleN (19400*m)) ∧ Odd d := by
    have hb := wideProductPool_bounds m d hd
    have hs := wideProductPool_smooth_odd m d hm hd
    exact ⟨by omega,hb.2.1,hb.2.2,hs⟩
  have hX : progressionScaleN (40020*m) ≤
      progressionScaleN (20000*m)*progressionScaleN (620*m)*progressionScaleN (19400*m) := by
    simp only [progressionScaleN,← pow_add]
    apply Nat.pow_le_pow_right (by decide)
    omega
  have hKX : progressionScaleN (20004*m)*progressionScaleN (620*m) ≤ progressionScaleN (40020*m) := by
    simp only [progressionScaleN,← pow_add]
    apply Nat.pow_le_pow_right (by decide)
    omega
  have hcap : progressionScaleN (20004*m)*progressionScaleN (620*m) ≤ 2^(256*(19395*m)) := by
    simp only [progressionScaleN,← pow_add]
    apply Nat.pow_le_pow_right (by decide)
    omega
  have h := rough_composite_family_reciprocal_count_endpoint (wideProductPool m)
    (progressionScaleN (20000*m)) (progressionScaleN (20004*m)) (progressionScaleN (40020*m))
    (progressionScaleN (620*m)) (progressionScaleN (19400*m)) (19395*m)
    hM hX hKX hcap (by omega) hend
  simpa only [wideSieveMain,wideSieveError,independentSieveMain,independentJ,independentN,
    poolTotientMass,progressionScaleN,Nat.cast_pow,Nat.cast_ofNat,mul_assoc,
    show 19396-1 = 19395 by decide] using h

lemma wide_sieve_main_small (m : ℕ) (hm : 2 ≤ m) :
    Real.log (progressionScaleN (40020*m))*wideSieveMain m ≤
      (27/32 : ℝ)*(progressionScaleN (40020*m) : ℝ) := by
  simpa only [wideSieveMain,independentN,progressionScaleN,mul_assoc] using
    chebyshev_independent_sieve_main_small 40020 19396 620 m (by decide) (by decide) hm (by norm_num)

lemma wide_sieve_error_pow_bound (m : ℕ) :
    wideSieveError m ≤ 3*(2 : ℝ)^(2561279*m) := by
  have hcard : ((wideProductPool m).card : ℝ) ≤ (2 : ℝ)^(64*(20004*m)) := by
    exact_mod_cast wideProductPool_card_le m
  have hsmall : (2 : ℝ)^(16*(19395*m)) ≤ (2 : ℝ)^(64*(19395*m)) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hone : (1 : ℝ) ≤ (2 : ℝ)^(64*(19395*m)) := one_le_pow₀ (by norm_num)
  have hsum : (2 : ℝ)^(64*(19395*m))+(2 : ℝ)^(16*(19395*m))+1 ≤
      3*(2 : ℝ)^(64*(19395*m)) := by linarith
  calc
    _ ≤ (2 : ℝ)^(64*(20004*m))*(2 : ℝ)^(64*620*m)*(3*(2 : ℝ)^(64*(19395*m))) := by
      unfold wideSieveError
      gcongr
    _ = 3*(2 : ℝ)^(2561216*m) := by
      rw [show (2 : ℝ)^(64*(20004*m))*(2 : ℝ)^(64*620*m)*(3*(2 : ℝ)^(64*(19395*m))) =
        3*((2 : ℝ)^(64*(20004*m))*(2 : ℝ)^(64*620*m)*(2 : ℝ)^(64*(19395*m))) by ring]
      simp only [← pow_add]
      congr 2
      omega
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) (by omega)) (by norm_num)

lemma wide_sieve_total_error_bound (m : ℕ) :
    Real.log (progressionScaleN (40020*m))*(wideSieveError m+32*Real.sqrt (progressionScaleN (40020*m))) ≤
      89644800*((m : ℝ)+1)*(2 : ℝ)^(2561279*m) := by
  have he := wide_sieve_error_pow_bound m
  have hs : Real.sqrt (progressionScaleN (40020*m)) ≤ (2 : ℝ)^(2561279*m) := by
    rw [sqrt_progressionScaleN]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hlog : Real.log (progressionScaleN (40020*m)) ≤ 2561280*((m : ℝ)+1) := by
    have h := independent_log_upper 40020 m
    simp only [independentN,mul_assoc,Nat.cast_ofNat] at h
    change Real.log (progressionScaleN (40020*m)) ≤ 64*(40020*((m : ℝ)+1)) at h
    linarith only [h]
  have hE : 0 ≤ wideSieveError m+32*Real.sqrt (progressionScaleN (40020*m)) := by
    unfold wideSieveError
    positivity
  have hsum : wideSieveError m+32*Real.sqrt (progressionScaleN (40020*m)) ≤ 35*(2 : ℝ)^(2561279*m) := by linarith
  calc
    _ ≤ (2561280*((m : ℝ)+1))*(35*(2 : ℝ)^(2561279*m)) :=
      mul_le_mul hlog hsum hE (by positivity)
    _ = _ := by ring

lemma eventually_wide_sieve_error_small :
    ∀ᶠ m : ℕ in atTop,
      Real.log (progressionScaleN (40020*m))*(wideSieveError m+32*Real.sqrt (progressionScaleN (40020*m))) ≤
        (progressionScaleN (40020*m) : ℝ)/64*poolTotientMass (wideProductPool m) := by
  filter_upwards [eventually_nat_poly_le_two_pow 1 (64*wideMassDenominator*89644800) 1,
    eventually_ge_atTop 1] with m hpoly hm
  have hp : (64*(wideMassDenominator : ℝ)*89644800)*((m : ℝ)+1) ≤ (2 : ℝ)^m := by
    exact_mod_cast (show (64*wideMassDenominator*89644800)*(m+1) ≤ 2^m by
      simpa only [one_mul,pow_one] using hpoly)
  have hb : 89644800*((m : ℝ)+1)*(2 : ℝ)^(2561279*m) ≤
      (progressionScaleN (40020*m) : ℝ)/(64*wideMassDenominator) := by
    apply (le_div_iff₀ (by norm_num [wideMassDenominator] : (0 : ℝ) < 64*wideMassDenominator)).mpr
    calc
      _ = ((64*(wideMassDenominator : ℝ)*89644800)*((m : ℝ)+1))*(2 : ℝ)^(2561279*m) := by ring
      _ ≤ (2 : ℝ)^m*(2 : ℝ)^(2561279*m) := mul_le_mul_of_nonneg_right hp (by positivity)
      _ = _ := by simp only [progressionScaleN,Nat.cast_pow,Nat.cast_ofNat,← pow_add]; congr 1; omega
  apply (wide_sieve_total_error_bound m).trans (hb.trans ?_)
  rw [show (progressionScaleN (40020*m) : ℝ)/(64*wideMassDenominator) =
      (progressionScaleN (40020*m) : ℝ)/64*(1/(wideMassDenominator : ℝ)) by ring]
  exact mul_le_mul_of_nonneg_left (wideProductPool_mass_lower m hm) (by positivity)

lemma eventually_wide_retained_weight :
    ∀ᶠ m : ℕ in atTop,
      (progressionScaleN (40020*m) : ℝ)/64*poolTotientMass (wideProductPool m) ≤
        16*Real.log (progressionScaleN (40020*m))*
          ((smoothPrimePool (progressionScaleN (40020*m)) (progressionScaleN (19400*m))).card : ℝ) := by
  have hend : ∀ᶠ m : ℕ in atTop, EndpointPairAt (19395*m) := by
    simpa only [independentJ,show 19396-1 = 19395 by decide] using eventually_independent_endpoint 19396 (by decide)
  filter_upwards [eventually_wide_progression_lower,eventually_wide_sieve_error_small,hend,
    eventually_ge_atTop 2] with m hweight herr hend hm
  have hr := wide_rough_count_le m (by omega) hend
  have hmain := wide_sieve_main_small m hm
  have hupper := family_progression_weight_le_smooth_count (wideProductPool m)
    (progressionScaleN (40020*m)) (progressionScaleN (19400*m)) 16
    (Nat.one_le_of_lt (by unfold progressionScaleN; positivity)) (fun n hn hN => wide_divisor_incidence_le m n (by omega) hn hN)
  have hrlog := mul_le_mul_of_nonneg_left hr (Real.log_natCast_nonneg (progressionScaleN (40020*m)))
  have hmW := mul_le_mul_of_nonneg_right hmain (poolTotientMass_nonneg (wideProductPool m))
  norm_num only [Nat.cast_ofNat] at hupper
  nlinarith only [hweight,herr,hupper,hrlog,hmW]

def wideCountConstant : ℕ := 64*16*(64*40020)*wideMassDenominator

/-- The logarithmic loss is exactly one power of the scale parameter. -/
theorem eventually_wide_smooth_prime_count :
    ∀ᶠ m : ℕ in atTop,
      (progressionScaleN (40020*m) : ℝ) ≤ (wideCountConstant : ℝ)*m*
        ((smoothPrimePool (progressionScaleN (40020*m)) (progressionScaleN (19400*m))).card : ℝ) := by
  filter_upwards [eventually_wide_retained_weight,eventually_ge_atTop 1] with m hw hm
  let N := progressionScaleN (40020*m)
  let S := smoothPrimePool N (progressionScaleN (19400*m))
  have hlower : (N : ℝ)/(64*wideMassDenominator) ≤ (N : ℝ)/64*poolTotientMass (wideProductPool m) := by
    have h := mul_le_mul_of_nonneg_left (wideProductPool_mass_lower m hm)
      (show 0 ≤ (N : ℝ)/64 by positivity)
    convert h using 1
    ring
  have hlog : Real.log (N : ℝ) ≤ 2561280*(m : ℝ) := by
    have h := log_two_pow_le (64*(40020*m))
    simpa [N,progressionScaleN,← mul_assoc] using h
  have hu : 16*Real.log (N : ℝ)*(S.card : ℝ) ≤ 16*(2561280*(m : ℝ))*(S.card : ℝ) := by gcongr
  have h := (div_le_iff₀ (by norm_num [wideMassDenominator] : (0 : ℝ) < 64*wideMassDenominator)).mp
    (hlower.trans (hw.trans hu))
  change (N : ℝ) ≤ (wideCountConstant : ℝ)*m*(S.card : ℝ)
  convert h using 1
  norm_num [wideCountConstant]
  ring

end Erdos821
