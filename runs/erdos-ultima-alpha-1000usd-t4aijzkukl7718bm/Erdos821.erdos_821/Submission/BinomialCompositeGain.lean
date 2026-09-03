import Submission.CompositeMultiplicityGain
import Submission.BinomialMangoldtLower

/-!
# A better explicit fixed exponent using the binomial Mangoldt lower bound

This improves constants in the existing structured second-sieve argument.
The resulting multiplicity exponents still do not approach one.
-/

open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators
namespace Erdos821
open AnalyticSieve
set_option maxHeartbeats 3000000

lemma eventually_progression_mangoldt_five_eighths (t : ℕ) (ht : 1 ≤ t) :
    ∀ᶠ m : ℕ in atTop,
      (5/8 : ℝ)*(progressionScaleN (t*m) : ℝ) ≤ mangoldtSum (progressionScaleN (t*m)) := by
  have hlim : Tendsto (fun m : ℕ => 64*t*m) atTop atTop := by
    apply tendsto_atTop_mono (fun m => ?_) tendsto_id
    exact Nat.le_mul_of_pos_left m (by positivity)
  have h := hlim.eventually eventually_dyadic_mangoldt_five_eighths
  simpa only [progressionScaleN, mul_assoc] using h

theorem eventually_product_mangoldt_weight_nine_sixteenths (r t : ℕ)
    (hrt : 2 * r + 1 ≤ t) :
    ∀ᶠ m : ℕ in atTop,
      (9/16 : ℝ) * (progressionScaleN (t * m) : ℝ) * primeProductReciprocalMass r m ≤
        ∑ d ∈ primeProductModuli r m, residueOneMangoldt d (progressionScaleN (t * m)) := by
  filter_upwards [eventually_progression_mangoldt_five_eighths t (by omega),
    eventually_product_mangoldt_total_lower r t (r + 1) hrt,
    eventually_nat_poly_le_two_pow 1 (4096 * r) 1,
    eventually_ge_atTop (max 1 (16 * primeProductMassConstant r))] with m hpsi htotal hsmall hm
  let N := progressionScaleN (t * m)
  let C : ℝ := primeProductMassConstant r
  let z : ℝ := (m : ℝ) + 1
  have hC : 0 < C := by dsimp [C]; exact_mod_cast primeProductMassConstant_pos r
  have hz : 0 < z := by dsimp [z]; positivity
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hsmall' : 4096 * r * (m + 1) ≤ progressionScaleN m := by
    have hpow : 2 ^ m ≤ progressionScaleN m := Nat.pow_le_pow_right (by decide) (by omega)
    simpa only [one_mul, pow_one] using hsmall.trans hpow
  have hmass : 1 / (C * z ^ r) ≤ primeProductReciprocalMass r m :=
    primeProductModuli_reciprocal_lower r m hsmall'
  have hW : 0 ≤ primeProductReciprocalMass r m := (by positivity : 0 ≤ 1 / (C * z^r)).trans hmass
  change (5/8 : ℝ)*(N : ℝ) ≤ mangoldtSum N at hpsi
  have hmain := mul_le_mul_of_nonneg_right hpsi hW
  have hbudget : 16 * C ≤ z := by
    have hm' : 16 * primeProductMassConstant r ≤ m + 1 := by omega
    dsimp only [C, z]
    exact_mod_cast hm'
  have herr : (N : ℝ) / z ^ (r + 1) ≤ (N : ℝ) / 16 * primeProductReciprocalMass r m := by
    calc
      _ ≤ (N : ℝ) / (16 * C * z ^ r) := by
        apply div_le_div_of_nonneg_left hN (by positivity)
        rw [pow_succ]
        have h := mul_le_mul_of_nonneg_right hbudget (pow_nonneg hz.le r)
        nlinarith only [h]
      _ = (N : ℝ) / 16 * (1 / (C * z ^ r)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hmass (div_nonneg hN (by norm_num))
  change mangoldtSum N * primeProductReciprocalMass r m - (N : ℝ) / z ^ (r + 1) ≤ _ at htotal
  change (9/16 : ℝ) * (N : ℝ) * primeProductReciprocalMass r m ≤ _
  linarith only [hmain, herr, htotal]

lemma binomial_structured_parameter_large (a : ℕ)
    (hC : 300000 * Sieve.totientRatioAverageConstant ≤ (a : ℝ)) : 100 ≤ a := by
  have h := totientRatioAverageConstant_ge_one
  have ha : (100 : ℝ) ≤ a := by linarith
  exact_mod_cast ha

lemma binomial_structured_coefficient_bound (a : ℕ)
    (hC : 300000 * Sieve.totientRatioAverageConstant ≤ (a : ℝ)) :
    266240 * Sieve.totientRatioAverageConstant * (4 * (a : ℝ) + 1) ≤
      (2 * (a : ℝ) - 1)^2 := by
  have ha : (100 : ℝ) ≤ a := by exact_mod_cast binomial_structured_parameter_large a hC
  have hC0 : 0 ≤ Sieve.totientRatioAverageConstant :=
    (by norm_num : (0 : ℝ) ≤ 1).trans totientRatioAverageConstant_ge_one
  have hCa := mul_le_mul_of_nonneg_right hC (show (0 : ℝ) ≤ a by linarith)
  have hlin := mul_le_mul_of_nonneg_left (show 4 * (a : ℝ) + 1 ≤ (401 / 100 : ℝ) * a by linarith) hC0
  have hsq := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ (199 / 100 : ℝ) * a)
    (by linarith : (199 / 100 : ℝ) * a ≤ 2 * (a : ℝ) - 1) 2
  nlinarith only [hCa, hlin, hsq, sq_nonneg (a : ℝ)]

lemma binomial_structured_sieve_main_small (a m : ℕ) (hm : 2 ≤ m)
    (hC : 300000 * Sieve.totientRatioAverageConstant ≤ (a : ℝ)) :
    Real.log (strictStructuredN a m : ℝ) * strictStructuredSieveMain a m ≤
      (strictStructuredN a m : ℝ) / 2 := by
  let N := strictStructuredN a m
  let C := Sieve.totientRatioAverageConstant
  let H : ℝ := harmonic (2 ^ (64 * m))
  let D := ((strictStructuredJ a m : ℝ) * Real.log 2)^2
  have ha : 100 ≤ a := binomial_structured_parameter_large a hC
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
  have hnum : Real.log (N : ℝ) * (32 * C * H) ≤ D / 2 := by
    calc
      _ ≤ Real.log (N : ℝ) * (32 * C * (65 * (m : ℝ) * Real.log 2)) := by
        gcongr
        exact strict_structured_harmonic_upper m hm
      _ = (266240 * C * (4 * (a : ℝ) + 1)) * ((m : ℝ) * Real.log 2)^2 / 2 := by
        rw [hlog]
        ring
      _ ≤ (2 * (a : ℝ) - 1)^2 * ((m : ℝ) * Real.log 2)^2 / 2 := by
        gcongr
        exact binomial_structured_coefficient_bound a hC
      _ = _ := by rw [hDeq]
  have hcoeff : Real.log (N : ℝ) * (32 * C * H / D) ≤ 1 / 2 := by
    rw [← mul_div_assoc]
    exact (div_le_iff₀ hD).mpr (by linarith only [hnum])
  calc
    _ = (N : ℝ) * (Real.log (N : ℝ) * (32 * C * H / D)) := by
      dsimp only [strictStructuredSieveMain, N, C, H, D]
      ring
    _ ≤ (N : ℝ) * (1 / 2) := mul_le_mul_of_nonneg_left hcoeff (Nat.cast_nonneg _)
    _ = _ := by ring

theorem binomial_smooth_structured_weight_retained (r t m Y : ℕ) (hm : 1 ≤ m)
    (A E : ℝ)
    (hweight : (9/16 : ℝ) * (2 ^ (64 * t * m) : ℝ) * primeProductReciprocalMass r m ≤
      ∑ d ∈ primeProductModuli r m, residueOneMangoldt d (2 ^ (64 * t * m)))
    (hrough : (∑ d ∈ primeProductModuli r m,
      ((roughProgressionPrimes d Y (2 ^ (64 * t * m))).card : ℝ)) ≤
        A * primeProductReciprocalMass r m + E)
    (hmain : Real.log (2 ^ (64 * t * m) : ℕ) * A ≤ (2 ^ (64 * t * m) : ℝ) / 2)
    (herror : Real.log (2 ^ (64 * t * m) : ℕ) *
      (E + 2 * (((t - 1).choose r : ℕ) : ℝ) * Real.sqrt (2 ^ (64 * t * m) : ℕ)) ≤
        (2 ^ (64 * t * m) : ℝ) / 64 * primeProductReciprocalMass r m) :
    (2 ^ (64 * t * m) : ℝ) / 32 * primeProductReciprocalMass r m ≤
      (((t - 1).choose r : ℕ) : ℝ) * Real.log (2 ^ (64 * t * m) : ℕ) *
        ((smoothStructuredPrimes r m (2 ^ (64 * t * m)) Y).card : ℝ) := by
  have hW : 0 ≤ primeProductReciprocalMass r m :=
    sum_nonneg (fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))
  have hup := product_progression_weight_le_smooth_structured_count r t m Y hm
  have hr := mul_le_mul_of_nonneg_left hrough (Real.log_natCast_nonneg (2 ^ (64 * t * m)))
  have hma := mul_le_mul_of_nonneg_right hmain hW
  have hnW := mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (64*t*m)) hW
  linarith only [hweight, hup, hr, hma, herror, hnW]

theorem eventually_binomial_structured_retained_weight (a : ℕ)
    (hC : 300000 * Sieve.totientRatioAverageConstant ≤ (a : ℝ)) :
    ∀ᶠ m : ℕ in atTop,
      (strictStructuredN a m : ℝ) / 32 * primeProductReciprocalMass (2 * a) m ≤
        ((4 * a).choose (2 * a) : ℝ) * Real.log (strictStructuredN a m : ℝ) *
          ((strictStructuredPrimes a m).card : ℝ) := by
  have ha : 1 ≤ a := (by norm_num : 1 ≤ 100).trans (binomial_structured_parameter_large a hC)
  filter_upwards [eventually_product_mangoldt_weight_nine_sixteenths (2 * a) (4 * a + 1) (by omega),
    eventually_strict_structured_total_error_small a ha, eventually_ge_atTop (max 2 a)] with m hw he hm
  have hNeq : progressionScaleN ((4 * a + 1) * m) = strictStructuredN a m := by
    simp only [progressionScaleN, strictStructuredN, mul_assoc]
  rw [hNeq] at hw
  have h := binomial_smooth_structured_weight_retained (2 * a) (4 * a + 1) m (strictStructuredY a m) (by omega)
    (strictStructuredSieveMain a m) (strictStructuredSieveError a m)
    (by simpa only [strictStructuredN, Nat.cast_pow, Nat.cast_ofNat] using hw)
    (strict_structured_rough_count_le a m ha hm)
    (by simpa only [strictStructuredN, Nat.cast_pow, Nat.cast_ofNat] using binomial_structured_sieve_main_small a m (by omega) hC)
    (by simpa only [strictStructuredN, Nat.cast_pow, Nat.cast_ofNat, Nat.add_sub_cancel] using he)
  simpa only [strictStructuredN, strictStructuredPrimes, Nat.cast_pow, Nat.cast_ofNat, Nat.add_sub_cancel] using h

theorem eventually_binomial_structured_prime_count (a : ℕ)
    (hC : 300000 * Sieve.totientRatioAverageConstant ≤ (a : ℝ)) :
    ∀ᶠ m : ℕ in atTop,
      strictStructuredN a m ≤ structuredPrimeCountConstant (2 * a) (4 * a + 1) *
        (m + 1) ^ (2 * a + 1) * (strictStructuredPrimes a m).card := by
  filter_upwards [eventually_product_reciprocal_supply (2 * a),
    eventually_binomial_structured_retained_weight a hC] with m hm hw
  exact strict_structured_count_of_weight a m hm hw

theorem eventually_binomial_structured_smooth_family (a : ℕ)
    (hC : 300000 * Sieve.totientRatioAverageConstant ≤ (a : ℝ)) :
    ∀ᶠ m : ℕ in atTop, ∃ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ p ≤ 2 ^ (64 * (4 * a + 1) * m) ∧
        p - 1 ∈ Nat.smoothNumbers (2 ^ (128 * a * m)) ∧
        2 * a ≤ (blockPrimeDivisors m (p - 1)).card) ∧
      2 ^ (64 * (4 * a + 1) * m) ≤ structuredPrimeCountConstant (2 * a) (4 * a + 1) *
        (m + 1) ^ (2 * a + 1) * P.card := by
  filter_upwards [eventually_binomial_structured_prime_count a hC] with m hm
  refine ⟨strictStructuredPrimes a m, ?_, hm⟩
  intro p hp
  obtain ⟨hpP, hps⟩ := mem_filter.mp hp
  obtain ⟨hpN, hpB⟩ := mem_filter.mp hpP
  have hpdata := Nat.mem_primesBelow.mp hpN
  exact ⟨hpdata.2, by change p ≤ strictStructuredN a m; omega, hps, hpB⟩

theorem infinite_g_gt_binomial_composite_limit (a : ℕ)
    (hC : 300000 * Sieve.totientRatioAverageConstant ≤ (a : ℝ))
    (γ : ℝ) (hγ : γ < 1 / 2 + 1 / (8 * (a : ℝ) + 2)) :
    {n : ℕ | (g n : ℝ) > (n : ℝ) ^ γ}.Infinite := by
  apply infinite_g_gt_of_eventual_polynomial_count (64 * (4 * a + 1)) (128 * a)
    1 (structuredPrimeCountConstant (2 * a) (4 * a + 1)) (2 * a + 1) (by omega) ?_ γ
      (by rw [composite_sieve_complementary_exponent]; exact hγ)
  filter_upwards [eventually_binomial_structured_smooth_family a hC] with m hm
  obtain ⟨P, hP, hcount⟩ := hm
  refine ⟨P, ?_, hcount⟩
  intro p hp
  have h := hP p hp
  exact ⟨h.1, h.2.1, by simpa only [one_mul] using h.2.2.1⟩

/-- Eliminating the auxiliary natural parameter gives an explicit fixed
threshold. This remains bounded away from one. -/
theorem infinite_g_gt_binomial_composite_uniform (γ : ℝ)
    (hγ : γ < 1 / 2 + 1 / (2400000 * Sieve.totientRatioAverageConstant + 10)) :
    {n : ℕ | (g n : ℝ) > (n : ℝ) ^ γ}.Infinite := by
  let a := ⌈300000 * Sieve.totientRatioAverageConstant⌉₊
  have hC0 : 0 ≤ Sieve.totientRatioAverageConstant :=
    (by norm_num : (0 : ℝ) ≤ 1).trans totientRatioAverageConstant_ge_one
  have hCa : 300000 * Sieve.totientRatioAverageConstant ≤ (a : ℝ) := Nat.le_ceil _
  have haC : (a : ℝ) ≤ 300000 * Sieve.totientRatioAverageConstant + 1 :=
    (Nat.ceil_lt_add_one (mul_nonneg (by norm_num) hC0)).le
  apply infinite_g_gt_binomial_composite_limit a hCa γ
  apply hγ.trans_le
  apply _root_.add_le_add le_rfl
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  linarith only [haC]

/-- The portion of the original assertion currently obtained by this method. -/
theorem erdos_821_binomial_composite_range (ε : ℝ)
    (hε : 1 / 2 - 1 / (2400000 * Sieve.totientRatioAverageConstant + 10) < ε) :
    {n : ℕ | (g n : ℝ) > (n : ℝ) ^ (1 - ε)}.Infinite := by
  exact infinite_g_gt_binomial_composite_uniform (1 - ε) (by linarith only [hε])

lemma binomial_composite_gain_gt_thirty_three_old_gain :
    33 * (1 / (80000000 * Sieve.totientRatioAverageConstant + 10)) <
      1 / (2400000 * Sieve.totientRatioAverageConstant + 10) := by
  have hC := totientRatioAverageConstant_ge_one
  have hd : 0 < 80000000 * Sieve.totientRatioAverageConstant + 10 := by linarith
  have hd' : 0 < 2400000 * Sieve.totientRatioAverageConstant + 10 := by linarith
  rw [mul_one_div]
  apply (div_lt_div_iff₀ hd hd').mpr
  linarith only [hC]

end Erdos821
