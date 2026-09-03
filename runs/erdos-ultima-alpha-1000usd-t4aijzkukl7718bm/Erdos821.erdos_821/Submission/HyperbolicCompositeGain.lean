import Submission.HyperbolicCompositeSieve

/-!
# A larger fixed multiplicity exponent from the hyperbolic denominator

The distribution range is unchanged. This is an unconditional improvement
of the fixed exponent, not exponents tending to one.
-/

open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators
namespace Erdos821
open AnalyticSieve
set_option maxHeartbeats 3000000

noncomputable def hyperbolicCompositeSecondSieveMajorant (r t b m J : ℕ) : ℝ :=
  Real.log (2 ^ (64 * t * m) : ℕ) *
    (((8/225 : ℝ) * Sieve.totientRatioAverageConstant * (2 : ℝ) ^ (64 * t * m) *
        (harmonic (2 ^ (64 * (t - r - b) * m)) : ℝ) / ((J : ℝ) * Real.log 2)^2) *
        primeProductReciprocalMass r m +
      ((primeProductModuli r m).card : ℝ) * (2 : ℝ) ^ (64 * (t - r - b) * m) *
        ((2 : ℝ) ^ (64 * J) + (2 : ℝ) ^ (16 * J) + 1))

theorem composite_second_sieve_rejected_weight_hyperbolic (r t b m J : ℕ)
    (hrb : r + b ≤ t) (hb : 2 ≤ b) (hm : 2 ≤ m) (hrm : r ≤ b * m)
    (hφ : 2^r ≤ progressionScaleN m) (hJ : 0 < J) (hhyperbolic : HyperbolicPairAt J) :
    Real.log (2 ^ (64 * t * m) : ℕ) *
      (∑ d ∈ primeProductModuli r m,
        ((roughProgressionPrimes d (2 ^ (64 * b * m)) (2 ^ (64 * t * m))).card : ℝ)) ≤
      hyperbolicCompositeSecondSieveMajorant r t b m J := by
  have heq : r + (t - r - b) + b = t := by omega
  have hD : progressionScaleN m ^ r = 2 ^ (64 * r * m) := by
    simp only [progressionScaleN, ← pow_mul]
    congr 1
    ring
  have hQ : progressionScaleN (m + 1) ^ r = 2 ^ (64 * r * (m + 1)) := by
    simp only [progressionScaleN, ← pow_mul]
    congr 1
    ring
  have hX : 2 ^ (64 * t * m) ≤
      2 ^ (64 * r * m) * 2 ^ (64 * (t - r - b) * m) * 2 ^ (64 * b * m) := by
    rw [← pow_add, ← pow_add]
    apply Nat.pow_le_pow_right (by decide)
    nlinarith only [congrArg (fun x : ℕ => 64 * x * m) heq]
  have hKX : 2 ^ (64 * r * (m + 1)) * 2 ^ (64 * (t - r - b) * m) ≤
      2 ^ (64 * t * m) := by
    rw [← pow_add]
    apply Nat.pow_le_pow_right (by decide)
    nlinarith only [hrm, congrArg (fun x : ℕ => 64 * x * m) heq]
  have hM (d : ℕ) (hd : d ∈ primeProductModuli r m) :
      0 < d ∧ 2 ^ (64 * r * m) ≤ d ∧ d ≤ 2 ^ (64 * r * (m + 1)) ∧
        d ∈ Nat.smoothNumbers (2 ^ (64 * b * m)) ∧ d ≤ 2 * d.totient := by
    have hp := primeProductModuli_properties hd
    refine ⟨hp.1, hD ▸ hp.2.2.2.1, hQ ▸ hp.2.2.2.2, ?_,
      prime_product_modulus_le_twice_totient r m d hd hφ⟩
    apply Nat.smoothNumbers_mono ?_ (primeProductModuli_smooth hm hd)
    apply Nat.pow_le_pow_right (by decide)
    nlinarith only [Nat.mul_le_mul_right m hb]
  have hbound := rough_composite_family_reciprocal_count_hyperbolic (primeProductModuli r m)
    (2 ^ (64 * r * m)) (2 ^ (64 * r * (m + 1))) (2 ^ (64 * t * m))
    (2 ^ (64 * (t - r - b) * m)) (2 ^ (64 * b * m)) J hM hX hKX hJ hhyperbolic
  have hw := mul_le_mul_of_nonneg_left hbound (Real.log_natCast_nonneg (2 ^ (64 * t * m)))
  simpa only [hyperbolicCompositeSecondSieveMajorant, primeProductReciprocalMass, Nat.cast_pow, Nat.cast_ofNat] using hw

noncomputable def hyperbolicStrictSieveMain (a m : ℕ) : ℝ :=
  (8/225 : ℝ) * Sieve.totientRatioAverageConstant * (strictStructuredN a m : ℝ) *
    (harmonic (2 ^ (64 * m)) : ℝ) / ((strictStructuredJ a m : ℝ) * Real.log 2)^2

lemma hyperbolic_strict_structured_rough_count_le (a m : ℕ) (ha : 1 ≤ a) (hm : max 2 a ≤ m) (hhyperbolic : HyperbolicPairAt (strictStructuredJ a m)) :
    (∑ d ∈ primeProductModuli (2 * a) m,
      ((roughProgressionPrimes d (strictStructuredY a m) (strictStructuredN a m)).card : ℝ)) ≤
        hyperbolicStrictSieveMain a m * primeProductReciprocalMass (2 * a) m + strictStructuredSieveError a m := by
  have hφ : 2 ^ (2 * a) ≤ progressionScaleN m := Nat.pow_le_pow_right (by decide) (by omega)
  have hJ : 0 < strictStructuredJ a m := Nat.mul_pos (by omega) (by omega)
  have h := composite_second_sieve_rejected_weight_hyperbolic (2 * a) (4 * a + 1) (2 * a) m (strictStructuredJ a m)
    (by omega) (by omega) (by omega) (by
      simpa only [mul_one] using Nat.mul_le_mul_left (2 * a) (show 1 ≤ m by omega)) hφ hJ hhyperbolic
  have hlog : 0 < Real.log (strictStructuredN a m : ℝ) := by
    have hlarge : (0 : ℝ) < ((4 * a + 1) * m : ℕ) := by exact_mod_cast Nat.mul_pos (by omega) (by omega : 0 < m)
    exact hlarge.trans_le (by simpa only [strictStructuredN, mul_assoc] using log_progression_scale_ge ((4 * a + 1) * m))
  have hY : 2 ^ (64 * (2 * a) * m) = strictStructuredY a m := by
    unfold strictStructuredY
    congr 1
    ring
  rw [hY] at h
  have h' : Real.log (strictStructuredN a m : ℝ) *
      (∑ d ∈ primeProductModuli (2 * a) m,
        ((roughProgressionPrimes d (strictStructuredY a m) (strictStructuredN a m)).card : ℝ)) ≤
      Real.log (strictStructuredN a m : ℝ) *
        (hyperbolicStrictSieveMain a m * primeProductReciprocalMass (2 * a) m + strictStructuredSieveError a m) := by
    simpa only [hyperbolicCompositeSecondSieveMajorant, strictStructuredN, hyperbolicStrictSieveMain, strictStructuredSieveError,
      show 4 * a + 1 - 2 * a - 2 * a = 1 by omega, mul_one, Nat.cast_pow, Nat.cast_ofNat] using h
  exact (mul_le_mul_iff_right₀ hlog).mp h'

lemma eventually_hyperbolic_strict_level (a : ℕ) (ha : 1 ≤ a) :
    ∀ᶠ m : ℕ in atTop, HyperbolicPairAt (strictStructuredJ a m) := by
  apply (show Tendsto (fun m : ℕ => strictStructuredJ a m) atTop atTop from ?_).eventually
    eventually_hyperbolic_pair_at
  apply tendsto_atTop_mono (fun m => ?_) tendsto_id
  change m ≤ (2*a-1)*m
  exact Nat.le_mul_of_pos_left _ (by omega)

lemma hyperbolic_structured_parameter_large (a : ℕ)
    (hC : 298 * Sieve.totientRatioAverageConstant ≤ (a : ℝ)) : 100 ≤ a := by
  have h := totientRatioAverageConstant_ge_one
  have ha : (100 : ℝ) ≤ a := by linarith
  exact_mod_cast ha

lemma hyperbolic_structured_coefficient_bound (a : ℕ)
    (hC : 298 * Sieve.totientRatioAverageConstant ≤ (a : ℝ)) :
    (13312/45 : ℝ) * Sieve.totientRatioAverageConstant * (4 * (a : ℝ) + 1) ≤
      (2 * (a : ℝ) - 1)^2 := by
  have hC1 := totientRatioAverageConstant_ge_one
  have hC0 : 0 ≤ Sieve.totientRatioAverageConstant := by linarith
  have ha : (74 : ℝ) ≤ a := by linarith
  have hCa := mul_le_mul_of_nonneg_right hC (Nat.cast_nonneg a)
  have hCa1 := mul_le_mul_of_nonneg_right hC1 (Nat.cast_nonneg a)
  have hCa2 := mul_le_mul_of_nonneg_left ha hC0
  nlinarith only [hCa, hCa1, hCa2]

lemma hyperbolic_structured_sieve_main_small (a m : ℕ) (hm : 2 ≤ m)
    (hC : 298 * Sieve.totientRatioAverageConstant ≤ (a : ℝ)) :
    Real.log (strictStructuredN a m : ℝ) * hyperbolicStrictSieveMain a m ≤
      (strictStructuredN a m : ℝ) / 2 := by
  let N := strictStructuredN a m
  let C := Sieve.totientRatioAverageConstant
  let H : ℝ := harmonic (2 ^ (64 * m))
  let D := ((strictStructuredJ a m : ℝ) * Real.log 2)^2
  have ha : 100 ≤ a := hyperbolic_structured_parameter_large a hC
  have haR : (100 : ℝ) ≤ a := by exact_mod_cast ha
  have hC0 : 0 ≤ C := (by norm_num : (0 : ℝ) ≤ 1).trans totientRatioAverageConstant_ge_one
  have hH0 : 0 ≤ H := harmonic_real_nonneg _
  have hlog0 : 0 ≤ Real.log (N : ℝ) := Real.log_natCast_nonneg _
  have hJ : 0 < strictStructuredJ a m := Nat.mul_pos (by omega) (by omega)
  have hD : 0 < D := sq_pos_of_pos (mul_pos (by exact_mod_cast hJ) (Real.log_pos (by norm_num)))
  have hlog : Real.log (N : ℝ) = 64 * (4 * (a : ℝ) + 1) * m * Real.log 2 := by
    simp only [N, strictStructuredN, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow,
      Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hDeq : D = (2 * (a : ℝ) - 1)^2 * ((m : ℝ) * Real.log 2)^2 := by
    simp only [D, strictStructuredJ, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ 2 * a),
      Nat.cast_ofNat, Nat.cast_one]
    ring
  have hnum : Real.log (N : ℝ) * ((8/225 : ℝ) * C * H) ≤ D / 2 := by
    calc
      _ ≤ Real.log (N : ℝ) * ((8/225 : ℝ) * C * (65 * (m : ℝ) * Real.log 2)) := by
        gcongr
        exact strict_structured_harmonic_upper m hm
      _ = ((13312/45 : ℝ) * C * (4 * (a : ℝ) + 1)) * ((m : ℝ) * Real.log 2)^2 / 2 := by
        rw [hlog]
        ring
      _ ≤ (2 * (a : ℝ) - 1)^2 * ((m : ℝ) * Real.log 2)^2 / 2 := by
        gcongr
        exact hyperbolic_structured_coefficient_bound a hC
      _ = _ := by rw [hDeq]
  have hcoeff : Real.log (N : ℝ) * ((8/225 : ℝ) * C * H / D) ≤ 1 / 2 := by
    rw [← mul_div_assoc]
    exact (div_le_iff₀ hD).mpr (by linarith only [hnum])
  calc
    _ = (N : ℝ) * (Real.log (N : ℝ) * ((8/225 : ℝ) * C * H / D)) := by
      dsimp only [hyperbolicStrictSieveMain, N, C, H, D]
      ring
    _ ≤ (N : ℝ) * (1 / 2) := mul_le_mul_of_nonneg_left hcoeff (Nat.cast_nonneg _)
    _ = _ := by ring

theorem eventually_hyperbolic_structured_retained_weight (a : ℕ)
    (hC : 298 * Sieve.totientRatioAverageConstant ≤ (a : ℝ)) :
    ∀ᶠ m : ℕ in atTop,
      (strictStructuredN a m : ℝ) / 32 * primeProductReciprocalMass (2 * a) m ≤
        ((4 * a).choose (2 * a) : ℝ) * Real.log (strictStructuredN a m : ℝ) *
          ((strictStructuredPrimes a m).card : ℝ) := by
  have ha : 1 ≤ a := (by norm_num : 1 ≤ 100).trans (hyperbolic_structured_parameter_large a hC)
  filter_upwards [eventually_product_mangoldt_weight_nine_sixteenths (2 * a) (4 * a + 1) (by omega),
    eventually_strict_structured_total_error_small a ha, eventually_ge_atTop (max 2 a),
    eventually_hyperbolic_strict_level a ha] with m hw he hm hhyperbolic
  have hNeq : progressionScaleN ((4 * a + 1) * m) = strictStructuredN a m := by
    simp only [progressionScaleN, strictStructuredN, mul_assoc]
  rw [hNeq] at hw
  have h := binomial_smooth_structured_weight_retained (2 * a) (4 * a + 1) m (strictStructuredY a m) (by omega)
    (hyperbolicStrictSieveMain a m) (strictStructuredSieveError a m)
    (by simpa only [strictStructuredN, Nat.cast_pow, Nat.cast_ofNat] using hw)
    (hyperbolic_strict_structured_rough_count_le a m ha hm hhyperbolic)
    (by simpa only [strictStructuredN, Nat.cast_pow, Nat.cast_ofNat] using hyperbolic_structured_sieve_main_small a m (by omega) hC)
    (by simpa only [strictStructuredN, Nat.cast_pow, Nat.cast_ofNat, Nat.add_sub_cancel] using he)
  simpa only [strictStructuredN, strictStructuredPrimes, Nat.cast_pow, Nat.cast_ofNat, Nat.add_sub_cancel] using h

theorem eventually_hyperbolic_structured_prime_count (a : ℕ)
    (hC : 298 * Sieve.totientRatioAverageConstant ≤ (a : ℝ)) :
    ∀ᶠ m : ℕ in atTop,
      strictStructuredN a m ≤ structuredPrimeCountConstant (2 * a) (4 * a + 1) *
        (m + 1) ^ (2 * a + 1) * (strictStructuredPrimes a m).card := by
  filter_upwards [eventually_product_reciprocal_supply (2 * a),
    eventually_hyperbolic_structured_retained_weight a hC] with m hm hw
  exact strict_structured_count_of_weight a m hm hw

theorem eventually_hyperbolic_structured_smooth_family (a : ℕ)
    (hC : 298 * Sieve.totientRatioAverageConstant ≤ (a : ℝ)) :
    ∀ᶠ m : ℕ in atTop, ∃ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ p ≤ 2 ^ (64 * (4 * a + 1) * m) ∧
        p - 1 ∈ Nat.smoothNumbers (2 ^ (128 * a * m)) ∧
        2 * a ≤ (blockPrimeDivisors m (p - 1)).card) ∧
      2 ^ (64 * (4 * a + 1) * m) ≤ structuredPrimeCountConstant (2 * a) (4 * a + 1) *
        (m + 1) ^ (2 * a + 1) * P.card := by
  filter_upwards [eventually_hyperbolic_structured_prime_count a hC] with m hm
  refine ⟨strictStructuredPrimes a m, ?_, hm⟩
  intro p hp
  obtain ⟨hpP, hps⟩ := mem_filter.mp hp
  obtain ⟨hpN, hpB⟩ := mem_filter.mp hpP
  have hpdata := Nat.mem_primesBelow.mp hpN
  exact ⟨hpdata.2, by change p ≤ strictStructuredN a m; omega, hps, hpB⟩

theorem infinite_g_gt_hyperbolic_composite_limit (a : ℕ)
    (hC : 298 * Sieve.totientRatioAverageConstant ≤ (a : ℝ))
    (γ : ℝ) (hγ : γ < 1 / 2 + 1 / (8 * (a : ℝ) + 2)) :
    {n : ℕ | (g n : ℝ) > (n : ℝ) ^ γ}.Infinite := by
  apply infinite_g_gt_of_eventual_polynomial_count (64 * (4 * a + 1)) (128 * a)
    1 (structuredPrimeCountConstant (2 * a) (4 * a + 1)) (2 * a + 1) (by omega) ?_ γ
      (by rw [composite_sieve_complementary_exponent]; exact hγ)
  filter_upwards [eventually_hyperbolic_structured_smooth_family a hC] with m hm
  obtain ⟨P, hP, hcount⟩ := hm
  refine ⟨P, ?_, hcount⟩
  intro p hp
  have h := hP p hp
  exact ⟨h.1, h.2.1, by simpa only [one_mul] using h.2.2.1⟩

/-- Eliminating the auxiliary natural parameter gives an explicit fixed
threshold. This remains bounded away from one. -/
theorem infinite_g_gt_hyperbolic_composite_uniform (γ : ℝ)
    (hγ : γ < 1 / 2 + 1 / (2384 * Sieve.totientRatioAverageConstant + 10)) :
    {n : ℕ | (g n : ℝ) > (n : ℝ) ^ γ}.Infinite := by
  let a := ⌈298 * Sieve.totientRatioAverageConstant⌉₊
  have hC0 : 0 ≤ Sieve.totientRatioAverageConstant :=
    (by norm_num : (0 : ℝ) ≤ 1).trans totientRatioAverageConstant_ge_one
  have hCa : 298 * Sieve.totientRatioAverageConstant ≤ (a : ℝ) := Nat.le_ceil _
  have haC : (a : ℝ) ≤ 298 * Sieve.totientRatioAverageConstant + 1 :=
    (Nat.ceil_lt_add_one (mul_nonneg (by norm_num) hC0)).le
  apply infinite_g_gt_hyperbolic_composite_limit a hCa γ
  apply hγ.trans_le
  apply _root_.add_le_add le_rfl
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  linarith only [haC]

/-- The portion of the original assertion currently obtained by this method. -/
theorem erdos_821_hyperbolic_composite_range (ε : ℝ)
    (hε : 1 / 2 - 1 / (2384 * Sieve.totientRatioAverageConstant + 10) < ε) :
    {n : ℕ | (g n : ℝ) > (n : ℝ) ^ (1 - ε)}.Infinite := by
  exact infinite_g_gt_hyperbolic_composite_uniform (1 - ε) (by linarith only [hε])


lemma hyperbolic_composite_gain_gt_fifty_five_sharp_gain :
    55 * (1/(133136*Sieve.totientRatioAverageConstant+10)) <
      1/(2384*Sieve.totientRatioAverageConstant+10) := by
  have hC := totientRatioAverageConstant_ge_one
  have hd : 0 < 133136*Sieve.totientRatioAverageConstant+10 := by linarith
  have hd' : 0 < 2384*Sieve.totientRatioAverageConstant+10 := by linarith
  rw [mul_one_div]
  apply (div_lt_div_iff₀ hd hd').mpr
  linarith only [hC]

lemma hyperbolic_composite_gain_gt_thousand_binomial_gain :
    1000 * (1/(2400000*Sieve.totientRatioAverageConstant+10)) <
      1/(2384*Sieve.totientRatioAverageConstant+10) := by
  have hC := totientRatioAverageConstant_ge_one
  have hd : 0 < 2400000*Sieve.totientRatioAverageConstant+10 := by linarith
  have hd' : 0 < 2384*Sieve.totientRatioAverageConstant+10 := by linarith
  rw [mul_one_div]
  apply (div_lt_div_iff₀ hd hd').mpr
  linarith only [hC]

end Erdos821
