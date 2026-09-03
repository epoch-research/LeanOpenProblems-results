import Submission.CompositeSecondSieveBarrier

/-!
# An unconditional structured prime family below square-root smoothness

The moduli have 2a small block-prime factors. At total exponent 4a+1,
the second sieve retains predecessors smooth to exponent 2a. All density
losses are fixed powers of the logarithm. The resulting gain is fixed;
these parameters do not approach arbitrary-root smoothness.
-/

open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators

namespace Erdos821

open AnalyticSieve

set_option maxHeartbeats 2000000

def strictStructuredN (a m : ℕ) : ℕ := 2 ^ (64 * (4 * a + 1) * m)
def strictStructuredY (a m : ℕ) : ℕ := 2 ^ (128 * a * m)
def strictStructuredJ (a m : ℕ) : ℕ := (2 * a - 1) * m

noncomputable def strictStructuredPrimes (a m : ℕ) : Finset ℕ :=
  smoothStructuredPrimes (2 * a) m (strictStructuredN a m) (strictStructuredY a m)

noncomputable def strictStructuredSieveMain (a m : ℕ) : ℝ :=
  32 * Sieve.totientRatioAverageConstant * (strictStructuredN a m : ℝ) *
    (harmonic (2 ^ (64 * m)) : ℝ) / ((strictStructuredJ a m : ℝ) * Real.log 2)^2

noncomputable def strictStructuredSieveError (a m : ℕ) : ℝ :=
  ((primeProductModuli (2 * a) m).card : ℝ) * (2 : ℝ) ^ (64 * m) *
    ((2 : ℝ) ^ (64 * strictStructuredJ a m) + (2 : ℝ) ^ (16 * strictStructuredJ a m) + 1)

lemma strict_structured_parameter_large (a : ℕ)
    (hC : 10000000 * Sieve.totientRatioAverageConstant ≤ (a : ℝ)) : 10 ≤ a := by
  have h := totientRatioAverageConstant_ge_one
  have ha : (10 : ℝ) ≤ a := by linarith
  exact_mod_cast ha

lemma strict_structured_coefficient_bound (a : ℕ)
    (hC : 10000000 * Sieve.totientRatioAverageConstant ≤ (a : ℝ)) :
    8519680 * Sieve.totientRatioAverageConstant * (4 * (a : ℝ) + 1) ≤
      (2 * (a : ℝ) - 1)^2 := by
  have ha : (10 : ℝ) ≤ a := by exact_mod_cast strict_structured_parameter_large a hC
  have hC0 : 0 ≤ Sieve.totientRatioAverageConstant :=
    (by norm_num : (0 : ℝ) ≤ 1).trans totientRatioAverageConstant_ge_one
  have hCa := mul_le_mul_of_nonneg_right hC (show (0 : ℝ) ≤ a by linarith)
  have hlin := mul_le_mul_of_nonneg_left (show 4 * (a : ℝ) + 1 ≤ (41 / 10 : ℝ) * a by linarith) hC0
  have hsq := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ (19 / 10 : ℝ) * a)
    (by linarith : (19 / 10 : ℝ) * a ≤ 2 * (a : ℝ) - 1) 2
  nlinarith only [hCa, hlin, hsq, sq_nonneg (a : ℝ)]

lemma strict_structured_harmonic_upper (m : ℕ) (hm : 2 ≤ m) :
    (harmonic (2 ^ (64 * m)) : ℝ) ≤ 65 * (m : ℝ) * Real.log 2 := by
  have h := harmonic_le_one_add_log (2 ^ (64 * m))
  simp only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow, Nat.cast_mul] at h
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hlog : (1 : ℝ) / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hprod := mul_le_mul_of_nonneg_right hlog (show (0 : ℝ) ≤ m by linarith)
  nlinarith only [h, hprod, hmR]

lemma strict_structured_sieve_main_small (a m : ℕ) (hm : 2 ≤ m)
    (hC : 10000000 * Sieve.totientRatioAverageConstant ≤ (a : ℝ)) :
    Real.log (strictStructuredN a m : ℝ) * strictStructuredSieveMain a m ≤
      (strictStructuredN a m : ℝ) / 64 := by
  let N := strictStructuredN a m
  let C := Sieve.totientRatioAverageConstant
  let H : ℝ := harmonic (2 ^ (64 * m))
  let D := ((strictStructuredJ a m : ℝ) * Real.log 2)^2
  have ha : 10 ≤ a := strict_structured_parameter_large a hC
  have haR : (10 : ℝ) ≤ a := by exact_mod_cast ha
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
  have hnum : Real.log (N : ℝ) * (32 * C * H) ≤ D / 64 := by
    calc
      _ ≤ Real.log (N : ℝ) * (32 * C * (65 * (m : ℝ) * Real.log 2)) := by
        gcongr
        exact strict_structured_harmonic_upper m hm
      _ = (8519680 * C * (4 * (a : ℝ) + 1)) * ((m : ℝ) * Real.log 2)^2 / 64 := by
        rw [hlog]
        ring
      _ ≤ (2 * (a : ℝ) - 1)^2 * ((m : ℝ) * Real.log 2)^2 / 64 := by
        gcongr
        exact strict_structured_coefficient_bound a hC
      _ = _ := by rw [hDeq]
  have hcoeff : Real.log (N : ℝ) * (32 * C * H / D) ≤ 1 / 64 := by
    rw [← mul_div_assoc]
    exact (div_le_iff₀ hD).mpr (by linarith only [hnum])
  calc
    _ = (N : ℝ) * (Real.log (N : ℝ) * (32 * C * H / D)) := by
      dsimp only [strictStructuredSieveMain, N, C, H, D]
      ring
    _ ≤ (N : ℝ) * (1 / 64) := mul_le_mul_of_nonneg_left hcoeff (Nat.cast_nonneg _)
    _ = _ := by ring

def strictStructuredErrorConstant (a : ℕ) : ℕ :=
  64 * (4 * a + 1) * (3 * 2 ^ (128 * a) + 2 * (4 * a).choose (2 * a))

lemma strict_structured_sieve_error_pow_bound (a m : ℕ) (ha : 1 ≤ a) :
    strictStructuredSieveError a m ≤
      (3 * (2 : ℝ) ^ (128 * a)) * (2 : ℝ) ^ ((256 * a + 63) * m) := by
  have hcard : ((primeProductModuli (2 * a) m).card : ℝ) ≤ (2 : ℝ) ^ (128 * a * (m + 1)) := by
    have h := primeProductModuli_card_le_upper (2 * a) m
    have he : progressionScaleN (m + 1) ^ (2 * a) = 2 ^ (128 * a * (m + 1)) := by
      simp only [progressionScaleN, ← pow_mul]
      congr 1
      ring
    rw [he] at h
    exact_mod_cast h
  have hJpow : (2 : ℝ) ^ (16 * strictStructuredJ a m) ≤ (2 : ℝ) ^ (64 * strictStructuredJ a m) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hJone : (1 : ℝ) ≤ (2 : ℝ) ^ (64 * strictStructuredJ a m) := one_le_pow₀ (by norm_num)
  have hE : (2 : ℝ) ^ (64 * strictStructuredJ a m) +
      (2 : ℝ) ^ (16 * strictStructuredJ a m) + 1 ≤ 3 * (2 : ℝ) ^ (64 * strictStructuredJ a m) := by
    linarith only [hJpow, hJone]
  have hexp : 128 * a * (m + 1) + 64 * m + 64 * strictStructuredJ a m =
      128 * a + 256 * a * m := by
    dsimp only [strictStructuredJ]
    have h := Nat.sub_add_cancel (by omega : 1 ≤ 2 * a)
    nlinarith only [congrArg (fun z : ℕ => z * m) h]
  have hpow : (2 : ℝ) ^ (128 * a * (m + 1)) * (2 : ℝ) ^ (64 * m) *
      (2 : ℝ) ^ (64 * strictStructuredJ a m) ≤
        (2 : ℝ) ^ (128 * a) * (2 : ℝ) ^ ((256 * a + 63) * m) := by
    simp only [← pow_add]
    apply pow_le_pow_right₀ (by norm_num)
    rw [hexp]
    nlinarith only [Nat.zero_le m]
  unfold strictStructuredSieveError
  calc
    _ ≤ (2 : ℝ) ^ (128 * a * (m + 1)) * (2 : ℝ) ^ (64 * m) *
        (3 * (2 : ℝ) ^ (64 * strictStructuredJ a m)) := by gcongr
    _ = 3 * ((2 : ℝ) ^ (128 * a * (m + 1)) * (2 : ℝ) ^ (64 * m) *
        (2 : ℝ) ^ (64 * strictStructuredJ a m)) := by ring
    _ ≤ 3 * ((2 : ℝ) ^ (128 * a) * (2 : ℝ) ^ ((256 * a + 63) * m)) := by gcongr
    _ = _ := by ring

lemma strict_structured_sqrt_pow_bound (a m : ℕ) (ha : 1 ≤ a) :
    Real.sqrt (strictStructuredN a m : ℝ) ≤ (2 : ℝ) ^ ((256 * a + 63) * m) := by
  have heq : strictStructuredN a m = progressionScaleN ((4 * a + 1) * m) := by
    simp only [strictStructuredN, progressionScaleN, mul_assoc]
  rw [heq, sqrt_progressionScaleN]
  apply pow_le_pow_right₀ (by norm_num)
  nlinarith only [Nat.mul_le_mul_right m ha]

lemma strict_structured_log_upper (a m : ℕ) :
    Real.log (strictStructuredN a m : ℝ) ≤ 64 * (4 * (a : ℝ) + 1) * ((m : ℝ) + 1) := by
  have h := log_two_pow_le (64 * (4 * a + 1) * m)
  change Real.log (strictStructuredN a m : ℝ) ≤ _ at h
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at h
  nlinarith only [h, Nat.cast_nonneg (α := ℝ) a]

lemma strict_structured_total_error_pow_bound (a m : ℕ) (ha : 1 ≤ a) :
    Real.log (strictStructuredN a m : ℝ) *
      (strictStructuredSieveError a m + 2 * ((4 * a).choose (2 * a) : ℝ) * Real.sqrt (strictStructuredN a m : ℝ)) ≤
        (strictStructuredErrorConstant a : ℝ) * ((m : ℝ) + 1) * (2 : ℝ) ^ ((256 * a + 63) * m) := by
  have hlog := strict_structured_log_upper a m
  have hE := strict_structured_sieve_error_pow_bound a m ha
  have hsqrt := strict_structured_sqrt_pow_bound a m ha
  have hlog0 := Real.log_natCast_nonneg (strictStructuredN a m)
  have hB0 : (0 : ℝ) ≤ (4 * a).choose (2 * a) := Nat.cast_nonneg _
  calc
    _ ≤ Real.log (strictStructuredN a m : ℝ) *
        ((3 * (2 : ℝ) ^ (128 * a)) * (2 : ℝ) ^ ((256 * a + 63) * m) +
          2 * ((4 * a).choose (2 * a) : ℝ) * (2 : ℝ) ^ ((256 * a + 63) * m)) := by gcongr
    _ ≤ (64 * (4 * (a : ℝ) + 1) * ((m : ℝ) + 1)) *
        ((3 * (2 : ℝ) ^ (128 * a)) * (2 : ℝ) ^ ((256 * a + 63) * m) +
          2 * ((4 * a).choose (2 * a) : ℝ) * (2 : ℝ) ^ ((256 * a + 63) * m)) := by gcongr
    _ = _ := by
      simp only [strictStructuredErrorConstant, Nat.cast_mul, Nat.cast_add, Nat.cast_pow,
        Nat.cast_ofNat, Nat.cast_one]
      ring

lemma strict_structured_rough_count_le (a m : ℕ) (ha : 1 ≤ a) (hm : max 2 a ≤ m) :
    (∑ d ∈ primeProductModuli (2 * a) m,
      ((roughProgressionPrimes d (strictStructuredY a m) (strictStructuredN a m)).card : ℝ)) ≤
        strictStructuredSieveMain a m * primeProductReciprocalMass (2 * a) m + strictStructuredSieveError a m := by
  have hφ : 2 ^ (2 * a) ≤ progressionScaleN m := Nat.pow_le_pow_right (by decide) (by omega)
  have hJ : 0 < strictStructuredJ a m := Nat.mul_pos (by omega) (by omega)
  have h := composite_second_sieve_rejected_weight_le (2 * a) (4 * a + 1) (2 * a) m (strictStructuredJ a m)
    (by omega) (by omega) (by omega) (by
      simpa only [mul_one] using Nat.mul_le_mul_left (2 * a) (show 1 ≤ m by omega)) hφ hJ
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
        (strictStructuredSieveMain a m * primeProductReciprocalMass (2 * a) m + strictStructuredSieveError a m) := by
    simpa only [compositeSecondSieveMajorant, strictStructuredN, strictStructuredSieveMain, strictStructuredSieveError,
      show 4 * a + 1 - 2 * a - 2 * a = 1 by omega, mul_one, Nat.cast_pow, Nat.cast_ofNat] using h
  exact (mul_le_mul_iff_right₀ hlog).mp h'

lemma eventually_product_reciprocal_supply (r : ℕ) :
    ∀ᶠ m : ℕ in atTop,
      1 / ((primeProductMassConstant r : ℝ) * ((m : ℝ) + 1)^r) ≤ primeProductReciprocalMass r m := by
  filter_upwards [eventually_nat_poly_le_two_pow 1 (4096 * r) 1] with m hm
  have hsmall : 4096 * r * (m + 1) ≤ progressionScaleN m := by
    have hpow : 2 ^ m ≤ progressionScaleN m := Nat.pow_le_pow_right (by decide) (by omega)
    simpa only [one_mul, pow_one] using hm.trans hpow
  exact primeProductModuli_reciprocal_lower r m hsmall

lemma eventually_strict_structured_total_error_small (a : ℕ) (ha : 1 ≤ a) :
    ∀ᶠ m : ℕ in atTop,
      Real.log (strictStructuredN a m : ℝ) *
        (strictStructuredSieveError a m +
          2 * ((4 * a).choose (2 * a) : ℝ) * Real.sqrt (strictStructuredN a m : ℝ)) ≤
        (strictStructuredN a m : ℝ) / 64 * primeProductReciprocalMass (2 * a) m := by
  filter_upwards [eventually_nat_poly_le_two_pow 1
      (64 * primeProductMassConstant (2 * a) * strictStructuredErrorConstant a) (2 * a + 1),
    eventually_product_reciprocal_supply (2 * a)] with m hpoly hmass
  let C : ℝ := primeProductMassConstant (2 * a)
  let E : ℝ := strictStructuredErrorConstant a
  let z : ℝ := (m : ℝ) + 1
  let R : ℝ := (2 : ℝ) ^ ((256 * a + 63) * m)
  let N := strictStructuredN a m
  have hC : 0 < C := by dsimp only [C]; exact_mod_cast primeProductMassConstant_pos (2 * a)
  have hz : 0 < z := by dsimp only [z]; positivity
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have hpolyR : 64 * C * E * z ^ (2 * a + 1) ≤ (2 : ℝ) ^ m := by
    dsimp only [C, E, z]
    simpa only [one_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat, Nat.cast_pow]
      using (show (((64 * primeProductMassConstant (2 * a) * strictStructuredErrorConstant a) *
        (1 * m + 1) ^ (2 * a + 1) : ℕ) : ℝ) ≤ ((2 ^ m : ℕ) : ℝ) from by exact_mod_cast hpoly)
  have hpow : (2 : ℝ) ^ m * R = (N : ℝ) := by
    simp only [R, N, strictStructuredN, Nat.cast_pow, Nat.cast_ofNat, ← pow_add]
    congr 1
    ring
  have hbudget : E * z * R ≤ (N : ℝ) / (64 * C * z ^ (2 * a)) := by
    apply (le_div_iff₀ (by positivity : 0 < 64 * C * z ^ (2 * a))).mpr
    calc
      _ = (64 * C * E * z ^ (2 * a + 1)) * R := by rw [pow_succ]; ring
      _ ≤ (2 : ℝ) ^ m * R := mul_le_mul_of_nonneg_right hpolyR hR
      _ = _ := hpow
  calc
    _ ≤ E * z * R := strict_structured_total_error_pow_bound a m ha
    _ ≤ (N : ℝ) / (64 * C * z ^ (2 * a)) := hbudget
    _ = (N : ℝ) / 64 * (1 / (C * z ^ (2 * a))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hmass (div_nonneg (Nat.cast_nonneg _) (by norm_num))

theorem eventually_strict_structured_retained_weight (a : ℕ)
    (hC : 10000000 * Sieve.totientRatioAverageConstant ≤ (a : ℝ)) :
    ∀ᶠ m : ℕ in atTop,
      (strictStructuredN a m : ℝ) / 32 * primeProductReciprocalMass (2 * a) m ≤
        ((4 * a).choose (2 * a) : ℝ) * Real.log (strictStructuredN a m : ℝ) *
          ((strictStructuredPrimes a m).card : ℝ) := by
  have ha : 1 ≤ a := (by norm_num : 1 ≤ 10).trans (strict_structured_parameter_large a hC)
  filter_upwards [eventually_product_mangoldt_weight_lower_reciprocal (2 * a) (4 * a + 1) (by omega),
    eventually_strict_structured_total_error_small a ha, eventually_ge_atTop (max 2 a)] with m hw he hm
  have hNeq : progressionScaleN ((4 * a + 1) * m) = strictStructuredN a m := by
    simp only [progressionScaleN, strictStructuredN, mul_assoc]
  rw [hNeq] at hw
  have h := smooth_structured_weight_retained (2 * a) (4 * a + 1) m (strictStructuredY a m) (by omega)
    (strictStructuredSieveMain a m) (strictStructuredSieveError a m)
    (by simpa only [strictStructuredN, Nat.cast_pow, Nat.cast_ofNat] using hw)
    (strict_structured_rough_count_le a m ha hm)
    (by simpa only [strictStructuredN, Nat.cast_pow, Nat.cast_ofNat] using strict_structured_sieve_main_small a m (by omega) hC)
    (by simpa only [strictStructuredN, Nat.cast_pow, Nat.cast_ofNat, Nat.add_sub_cancel] using he)
  simpa only [strictStructuredN, strictStructuredPrimes, Nat.cast_pow, Nat.cast_ofNat, Nat.add_sub_cancel] using h

lemma strict_structured_count_of_weight (a m : ℕ)
    (hmass : 1 / ((primeProductMassConstant (2 * a) : ℝ) * ((m : ℝ) + 1) ^ (2 * a)) ≤
      primeProductReciprocalMass (2 * a) m)
    (hweight : (strictStructuredN a m : ℝ) / 32 * primeProductReciprocalMass (2 * a) m ≤
      ((4 * a).choose (2 * a) : ℝ) * Real.log (strictStructuredN a m : ℝ) *
        ((strictStructuredPrimes a m).card : ℝ)) :
    strictStructuredN a m ≤ structuredPrimeCountConstant (2 * a) (4 * a + 1) *
      (m + 1) ^ (2 * a + 1) * (strictStructuredPrimes a m).card := by
  let N := strictStructuredN a m
  let C : ℝ := primeProductMassConstant (2 * a)
  let B : ℝ := (4 * a).choose (2 * a)
  let z : ℝ := (m : ℝ) + 1
  let G := strictStructuredPrimes a m
  have hC : 0 < C := by dsimp only [C]; exact_mod_cast primeProductMassConstant_pos (2 * a)
  have hB : 0 ≤ B := Nat.cast_nonneg _
  have hz : 0 < z := by dsimp only [z]; positivity
  have hlog : Real.log (N : ℝ) ≤ 64 * (4 * (a : ℝ) + 1) * z := strict_structured_log_upper a m
  have hgood : (N : ℝ) / (32 * C * z ^ (2 * a)) ≤ B * Real.log N * (G.card : ℝ) := by
    calc
      _ = (N : ℝ) / 32 * (1 / (C * z ^ (2 * a))) := by ring
      _ ≤ (N : ℝ) / 32 * primeProductReciprocalMass (2 * a) m :=
        mul_le_mul_of_nonneg_left hmass (div_nonneg (Nat.cast_nonneg _) (by norm_num))
      _ ≤ _ := hweight
  have hgood' := hgood.trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog hB) (Nat.cast_nonneg G.card))
  have hfinal := (div_le_iff₀ (by positivity : 0 < 32 * C * z ^ (2 * a))).mp hgood'
  have hfinal' : (N : ℝ) ≤ (structuredPrimeCountConstant (2 * a) (4 * a + 1) : ℝ) *
      z ^ (2 * a + 1) * (G.card : ℝ) := by
    simp only [structuredPrimeCountConstant, Nat.add_sub_cancel, Nat.cast_mul, Nat.cast_add,
      Nat.cast_ofNat, Nat.cast_one, pow_succ]
    dsimp only [C, B] at hfinal
    nlinarith only [hfinal]
  dsimp only [N, G, z] at hfinal'
  exact_mod_cast hfinal'

/-- The predecessor cutoff has exponent 2a/(4a+1), strictly below one half. -/
theorem eventually_strict_structured_prime_count (a : ℕ)
    (hC : 10000000 * Sieve.totientRatioAverageConstant ≤ (a : ℝ)) :
    ∀ᶠ m : ℕ in atTop,
      strictStructuredN a m ≤ structuredPrimeCountConstant (2 * a) (4 * a + 1) *
        (m + 1) ^ (2 * a + 1) * (strictStructuredPrimes a m).card := by
  filter_upwards [eventually_product_reciprocal_supply (2 * a),
    eventually_strict_structured_retained_weight a hC] with m hm hw
  exact strict_structured_count_of_weight a m hm hw

theorem eventually_strict_structured_smooth_family (a : ℕ)
    (hC : 10000000 * Sieve.totientRatioAverageConstant ≤ (a : ℝ)) :
    ∀ᶠ m : ℕ in atTop, ∃ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ p ≤ 2 ^ (64 * (4 * a + 1) * m) ∧
        p - 1 ∈ Nat.smoothNumbers (2 ^ (128 * a * m)) ∧
        2 * a ≤ (blockPrimeDivisors m (p - 1)).card) ∧
      2 ^ (64 * (4 * a + 1) * m) ≤ structuredPrimeCountConstant (2 * a) (4 * a + 1) *
        (m + 1) ^ (2 * a + 1) * P.card := by
  filter_upwards [eventually_strict_structured_prime_count a hC] with m hm
  refine ⟨strictStructuredPrimes a m, ?_, hm⟩
  intro p hp
  obtain ⟨hpP, hps⟩ := mem_filter.mp hp
  obtain ⟨hpN, hpB⟩ := mem_filter.mp hpP
  have hpdata := Nat.mem_primesBelow.mp hpN
  exact ⟨hpdata.2, by change p ≤ strictStructuredN a m; omega, hps, hpB⟩

end Erdos821
