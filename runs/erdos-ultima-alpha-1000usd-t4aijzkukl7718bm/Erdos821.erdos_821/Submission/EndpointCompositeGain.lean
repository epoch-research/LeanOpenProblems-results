import Submission.EndpointCompositeSieve

/-!
# A larger fixed multiplicity exponent without endpoint doubling

The distribution range is unchanged. The explicit exponent 53/105 follows
from the mixed root sieve and the bound sum_{n even} 1/phi(n) <= (4/3) H_K.
This is not a proof of exponents tending to one.
-/

open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators
namespace Erdos821
open AnalyticSieve
set_option maxHeartbeats 3000000

noncomputable def endpointCompositeSecondSieveMajorant (r t b m J : ℕ) : ℝ :=
  Real.log (2 ^ (64 * t * m) : ℕ) *
    (((2/675 : ℝ) * (2 : ℝ) ^ (64 * t * m) *
        (harmonic (2 ^ (64 * (t - r - b) * m)) : ℝ) / ((J : ℝ) * Real.log 2)^2) *
        primeProductReciprocalMass r m +
      ((primeProductModuli r m).card : ℝ) * (2 : ℝ) ^ (64 * (t - r - b) * m) *
        ((2 : ℝ) ^ (64 * J) + (2 : ℝ) ^ (16 * J) + 1))

theorem composite_second_sieve_rejected_weight_endpoint (r t b m J : ℕ)
    (hrb : r + b ≤ t) (hb : 2 ≤ b) (hm : 2 ≤ m) (hrm : r ≤ b * m)
    (hJ : 0 < J)
    (hcap : 2^(64*r*(m+1))*2^(64*(t-r-b)*m) ≤ 2^(256*J))
    (hendpoint : EndpointPairAt J) :
    Real.log (2 ^ (64 * t * m) : ℕ) *
      (∑ d ∈ primeProductModuli r m,
        ((roughProgressionPrimes d (2 ^ (64 * b * m)) (2 ^ (64 * t * m))).card : ℝ)) ≤
      endpointCompositeSecondSieveMajorant r t b m J := by
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
        d ∈ Nat.smoothNumbers (2 ^ (64 * b * m)) ∧ Odd d := by
    have hp := primeProductModuli_properties hd
    refine ⟨hp.1, hD ▸ hp.2.2.2.1, hQ ▸ hp.2.2.2.2, ?_,primeProductModuli_odd (by omega) hd⟩
    apply Nat.smoothNumbers_mono ?_ (primeProductModuli_smooth hm hd)
    apply Nat.pow_le_pow_right (by decide)
    nlinarith only [Nat.mul_le_mul_right m hb]
  have hbound := rough_composite_family_reciprocal_count_endpoint (primeProductModuli r m)
    (2 ^ (64 * r * m)) (2 ^ (64 * r * (m + 1))) (2 ^ (64 * t * m))
    (2 ^ (64 * (t - r - b) * m)) (2 ^ (64 * b * m)) J hM hX hKX hcap hJ hendpoint
  have hw := mul_le_mul_of_nonneg_left hbound (Real.log_natCast_nonneg (2 ^ (64 * t * m)))
  simpa only [endpointCompositeSecondSieveMajorant, primeProductReciprocalMass, Nat.cast_pow, Nat.cast_ofNat] using hw

noncomputable def endpointStrictSieveMain (a m : ℕ) : ℝ :=
  (2/675 : ℝ) * (strictStructuredN a m : ℝ) *
    (harmonic (2 ^ (64 * m)) : ℝ) / ((strictStructuredJ a m : ℝ) * Real.log 2)^2

lemma endpoint_strict_structured_rough_count_le (a m : ℕ) (ha : 1 ≤ a) (hm : max 2 a ≤ m) (hendpoint : EndpointPairAt (strictStructuredJ a m)) :
    (∑ d ∈ primeProductModuli (2 * a) m,
      ((roughProgressionPrimes d (strictStructuredY a m) (strictStructuredN a m)).card : ℝ)) ≤
        endpointStrictSieveMain a m * primeProductReciprocalMass (2 * a) m + strictStructuredSieveError a m := by
  have hJ : 0 < strictStructuredJ a m := Nat.mul_pos (by omega) (by omega)
  have hcap : 2^(64*(2*a)*(m+1))*2^(64*(4*a+1-2*a-2*a)*m) ≤
      2^(256*strictStructuredJ a m) := by
    rw [show 4*a+1-2*a-2*a = 1 by omega, mul_one, ← pow_add]
    apply Nat.pow_le_pow_right (by decide)
    unfold strictStructuredJ
    have hsub : (2*a-1)*m+m = 2*a*m := by
      have h := congrArg (fun x : ℕ => x*m) (Nat.sub_add_cancel (by omega : 1 ≤ 2*a))
      simpa only [Nat.add_mul,one_mul] using h
    have ham1 := Nat.mul_le_mul_right m ha
    have ham2 := Nat.mul_le_mul_left a (show 2 ≤ m by omega)
    nlinarith only [hsub,ham1,ham2]
  have h := composite_second_sieve_rejected_weight_endpoint (2 * a) (4 * a + 1) (2 * a) m (strictStructuredJ a m)
    (by omega) (by omega) (by omega) (by
      simpa only [mul_one] using Nat.mul_le_mul_left (2 * a) (show 1 ≤ m by omega)) hJ hcap hendpoint
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
        (endpointStrictSieveMain a m * primeProductReciprocalMass (2 * a) m + strictStructuredSieveError a m) := by
    simpa only [endpointCompositeSecondSieveMajorant, strictStructuredN, endpointStrictSieveMain, strictStructuredSieveError,
      show 4 * a + 1 - 2 * a - 2 * a = 1 by omega, mul_one, Nat.cast_pow, Nat.cast_ofNat] using h
  exact (mul_le_mul_iff_right₀ hlog).mp h'

lemma eventually_endpoint_strict_level (a : ℕ) (ha : 1 ≤ a) :
    ∀ᶠ m : ℕ in atTop, EndpointPairAt (strictStructuredJ a m) := by
  apply (show Tendsto (fun m : ℕ => strictStructuredJ a m) atTop atTop from ?_).eventually
    eventually_endpoint_pair_at
  apply tendsto_atTop_mono (fun m => ?_) tendsto_id
  change m ≤ (2*a-1)*m
  exact Nat.le_mul_of_pos_left _ (by omega)

lemma endpoint_structured_parameter_large (a : ℕ) (hC : 26 ≤ a) : 20 ≤ a := by omega

lemma endpoint_structured_coefficient_bound (a : ℕ) (hC : 26 ≤ a) :
    (3328/135 : ℝ) * (4 * (a : ℝ) + 1) ≤ (2 * (a : ℝ) - 1)^2 := by
  have ha : (26 : ℝ) ≤ a := by exact_mod_cast hC
  have haa := mul_le_mul_of_nonneg_right ha (Nat.cast_nonneg a)
  nlinarith only [ha,haa]

lemma endpoint_structured_sieve_main_small (a m : ℕ) (hm : 2 ≤ m)
    (hC : 26 ≤ a) :
    Real.log (strictStructuredN a m : ℝ) * endpointStrictSieveMain a m ≤
      (strictStructuredN a m : ℝ) / 2 := by
  let N := strictStructuredN a m
  let H : ℝ := harmonic (2 ^ (64 * m))
  let D := ((strictStructuredJ a m : ℝ) * Real.log 2)^2
  have ha : 20 ≤ a := endpoint_structured_parameter_large a hC
  have haR : (20 : ℝ) ≤ a := by exact_mod_cast ha
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
  have hnum : Real.log (N : ℝ) * ((2/675 : ℝ) * H) ≤ D / 2 := by
    calc
      _ ≤ Real.log (N : ℝ) * ((2/675 : ℝ) * (65 * (m : ℝ) * Real.log 2)) := by
        gcongr
        exact strict_structured_harmonic_upper m hm
      _ = ((3328/135 : ℝ) * (4 * (a : ℝ) + 1)) * ((m : ℝ) * Real.log 2)^2 / 2 := by
        rw [hlog]
        ring
      _ ≤ (2 * (a : ℝ) - 1)^2 * ((m : ℝ) * Real.log 2)^2 / 2 := by
        gcongr
        exact endpoint_structured_coefficient_bound a hC
      _ = _ := by rw [hDeq]
  have hcoeff : Real.log (N : ℝ) * ((2/675 : ℝ) * H / D) ≤ 1 / 2 := by
    rw [← mul_div_assoc]
    exact (div_le_iff₀ hD).mpr (by linarith only [hnum])
  calc
    _ = (N : ℝ) * (Real.log (N : ℝ) * ((2/675 : ℝ) * H / D)) := by
      dsimp only [endpointStrictSieveMain, N, H, D]
      ring
    _ ≤ (N : ℝ) * (1 / 2) := mul_le_mul_of_nonneg_left hcoeff (Nat.cast_nonneg _)
    _ = _ := by ring

theorem eventually_endpoint_structured_retained_weight (a : ℕ)
    (hC : 26 ≤ a) :
    ∀ᶠ m : ℕ in atTop,
      (strictStructuredN a m : ℝ) / 32 * primeProductReciprocalMass (2 * a) m ≤
        ((4 * a).choose (2 * a) : ℝ) * Real.log (strictStructuredN a m : ℝ) *
          ((strictStructuredPrimes a m).card : ℝ) := by
  have ha : 1 ≤ a := (by norm_num : 1 ≤ 20).trans (endpoint_structured_parameter_large a hC)
  filter_upwards [eventually_product_mangoldt_weight_nine_sixteenths (2 * a) (4 * a + 1) (by omega),
    eventually_strict_structured_total_error_small a ha, eventually_ge_atTop (max 2 a),
    eventually_endpoint_strict_level a ha] with m hw he hm hendpoint
  have hNeq : progressionScaleN ((4 * a + 1) * m) = strictStructuredN a m := by
    simp only [progressionScaleN, strictStructuredN, mul_assoc]
  rw [hNeq] at hw
  have h := binomial_smooth_structured_weight_retained (2 * a) (4 * a + 1) m (strictStructuredY a m) (by omega)
    (endpointStrictSieveMain a m) (strictStructuredSieveError a m)
    (by simpa only [strictStructuredN, Nat.cast_pow, Nat.cast_ofNat] using hw)
    (endpoint_strict_structured_rough_count_le a m ha hm hendpoint)
    (by simpa only [strictStructuredN, Nat.cast_pow, Nat.cast_ofNat] using endpoint_structured_sieve_main_small a m (by omega) hC)
    (by simpa only [strictStructuredN, Nat.cast_pow, Nat.cast_ofNat, Nat.add_sub_cancel] using he)
  simpa only [strictStructuredN, strictStructuredPrimes, Nat.cast_pow, Nat.cast_ofNat, Nat.add_sub_cancel] using h

theorem eventually_endpoint_structured_prime_count (a : ℕ)
    (hC : 26 ≤ a) :
    ∀ᶠ m : ℕ in atTop,
      strictStructuredN a m ≤ structuredPrimeCountConstant (2 * a) (4 * a + 1) *
        (m + 1) ^ (2 * a + 1) * (strictStructuredPrimes a m).card := by
  filter_upwards [eventually_product_reciprocal_supply (2 * a),
    eventually_endpoint_structured_retained_weight a hC] with m hm hw
  exact strict_structured_count_of_weight a m hm hw

theorem eventually_endpoint_structured_smooth_family (a : ℕ)
    (hC : 26 ≤ a) :
    ∀ᶠ m : ℕ in atTop, ∃ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ p ≤ 2 ^ (64 * (4 * a + 1) * m) ∧
        p - 1 ∈ Nat.smoothNumbers (2 ^ (128 * a * m)) ∧
        2 * a ≤ (blockPrimeDivisors m (p - 1)).card) ∧
      2 ^ (64 * (4 * a + 1) * m) ≤ structuredPrimeCountConstant (2 * a) (4 * a + 1) *
        (m + 1) ^ (2 * a + 1) * P.card := by
  filter_upwards [eventually_endpoint_structured_prime_count a hC] with m hm
  refine ⟨strictStructuredPrimes a m, ?_, hm⟩
  intro p hp
  obtain ⟨hpP, hps⟩ := mem_filter.mp hp
  obtain ⟨hpN, hpB⟩ := mem_filter.mp hpP
  have hpdata := Nat.mem_primesBelow.mp hpN
  exact ⟨hpdata.2, by change p ≤ strictStructuredN a m; omega, hps, hpB⟩

theorem infinite_g_gt_endpoint_composite_limit (a : ℕ)
    (hC : 26 ≤ a)
    (γ : ℝ) (hγ : γ < 1 / 2 + 1 / (8 * (a : ℝ) + 2)) :
    {n : ℕ | (g n : ℝ) > (n : ℝ) ^ γ}.Infinite := by
  apply infinite_g_gt_of_eventual_polynomial_count (64 * (4 * a + 1)) (128 * a)
    1 (structuredPrimeCountConstant (2 * a) (4 * a + 1)) (2 * a + 1) (by omega) ?_ γ
      (by rw [composite_sieve_complementary_exponent]; exact hγ)
  filter_upwards [eventually_endpoint_structured_smooth_family a hC] with m hm
  obtain ⟨P, hP, hcount⟩ := hm
  refine ⟨P, ?_, hcount⟩
  intro p hp
  have h := hP p hp
  exact ⟨h.1, h.2.1, by simpa only [one_mul] using h.2.2.1⟩

/-- An explicit unconditional exponent. This remains bounded away from one. -/
theorem infinite_g_gt_endpoint_composite_uniform (γ : ℝ)
    (hγ : γ < 53/105) :
    {n : ℕ | (g n : ℝ) > (n : ℝ)^γ}.Infinite := by
  apply infinite_g_gt_endpoint_composite_limit 26 (by norm_num) γ
  norm_num
  exact hγ

/-- The range of the original assertion provided by this estimate. -/
theorem erdos_821_endpoint_composite_range (ε : ℝ) (hε : 52/105 < ε) :
    {n : ℕ | (g n : ℝ) > (n : ℝ)^(1-ε)}.Infinite := by
  exact infinite_g_gt_endpoint_composite_uniform (1-ε) (by linarith only [hε])

lemma endpoint_composite_threshold_gt_even_threshold :
    (103/205 : ℝ) < 53/105 := by norm_num

end Erdos821
