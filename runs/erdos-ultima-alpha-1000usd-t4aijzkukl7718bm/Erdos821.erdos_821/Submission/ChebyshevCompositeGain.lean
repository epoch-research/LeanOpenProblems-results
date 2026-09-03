import Submission.ChebyshevFactorialLower
import Submission.IndependentCompositeGain

/-!
# A fixed multiplicity-exponent improvement from Chebyshev's factorial ratio

The stronger Mangoldt lower constant improves the retained prime weight.
The smoothness and distribution exponents are still bounded away from the
range required to settle the full conjecture.
-/

open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators
namespace Erdos821
open AnalyticSieve
set_option maxHeartbeats 3000000

lemma eventually_progression_mangoldt_nine_tenths (t : ℕ) (ht : 1 ≤ t) :
    ∀ᶠ m : ℕ in atTop,
      (9/10 : ℝ)*(progressionScaleN (t*m) : ℝ) ≤ mangoldtSum (progressionScaleN (t*m)) := by
  have hlim : Tendsto (fun m : ℕ => progressionScaleN (t*m)) atTop atTop := by
    apply tendsto_atTop_mono (fun m => ?_) tendsto_id
    apply Nat.lt_two_pow_self.le.trans
    apply Nat.pow_le_pow_right (by decide)
    change m ≤ 64*(t*m)
    exact (Nat.le_mul_of_pos_left m (by omega : 0 < t)).trans
      (Nat.le_mul_of_pos_left (t*m) (by decide))
  exact hlim.eventually eventually_mangoldt_nine_tenths

theorem eventually_product_mangoldt_weight_seven_eighths (r t : ℕ)
    (hrt : 2 * r + 1 ≤ t) :
    ∀ᶠ m : ℕ in atTop,
      (7/8 : ℝ) * (progressionScaleN (t * m) : ℝ) * primeProductReciprocalMass r m ≤
        ∑ d ∈ primeProductModuli r m, residueOneMangoldt d (progressionScaleN (t * m)) := by
  filter_upwards [eventually_progression_mangoldt_nine_tenths t (by omega),
    eventually_product_mangoldt_total_lower r t (r + 1) hrt,
    eventually_nat_poly_le_two_pow 1 (4096 * r) 1,
    eventually_ge_atTop (max 1 (64 * primeProductMassConstant r))] with m hpsi htotal hsmall hm
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
  change (9/10 : ℝ)*(N : ℝ) ≤ mangoldtSum N at hpsi
  have hmain := mul_le_mul_of_nonneg_right hpsi hW
  have hbudget : 64 * C ≤ z := by
    have hm' : 64 * primeProductMassConstant r ≤ m + 1 := by omega
    dsimp only [C, z]
    exact_mod_cast hm'
  have herr : (N : ℝ) / z ^ (r + 1) ≤ (N : ℝ) / 64 * primeProductReciprocalMass r m := by
    calc
      _ ≤ (N : ℝ) / (64 * C * z ^ r) := by
        apply div_le_div_of_nonneg_left hN (by positivity)
        rw [pow_succ]
        have h := mul_le_mul_of_nonneg_right hbudget (pow_nonneg hz.le r)
        nlinarith only [h]
      _ = (N : ℝ) / 64 * (1 / (C * z ^ r)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hmass (div_nonneg hN (by norm_num))
  change mangoldtSum N * primeProductReciprocalMass r m - (N : ℝ) / z ^ (r + 1) ≤ _ at htotal
  change (7/8 : ℝ) * (N : ℝ) * primeProductReciprocalMass r m ≤ _
  have hNW := mul_nonneg hN hW
  linarith only [hmain, herr, htotal, hNW]

lemma chebyshev_independent_sieve_main_small (t b h m : ℕ) (hb : 2 ≤ b)
    (hh : 1 ≤ h) (hm : 2 ≤ m)
    (hc : (8320/675 : ℝ)*(t : ℝ)*h ≤ (27/32 : ℝ)*((b : ℝ)-1)^2) :
    Real.log (independentN t m : ℝ)*independentSieveMain t b h m ≤
      (27/32 : ℝ)*(independentN t m : ℝ) := by
  let N := independentN t m
  let H : ℝ := harmonic (2^(64*h*m))
  let D : ℝ := ((independentJ b m : ℝ)*Real.log 2)^2
  have hJ : 0 < independentJ b m := Nat.mul_pos (by omega) (by omega)
  have hD : 0 < D := sq_pos_of_pos (mul_pos (by exact_mod_cast hJ)
    (Real.log_pos (by norm_num)))
  have hlog0 := Real.log_natCast_nonneg N
  have hlog : Real.log (N : ℝ) = 64*(t : ℝ)*m*Real.log 2 := by
    simp only [N, independentN, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow, Nat.cast_mul]
  have hDeq : D = ((b : ℝ)-1)^2*((m : ℝ)*Real.log 2)^2 := by
    simp only [D, independentJ, Nat.cast_mul,
      Nat.cast_sub (by omega : 1 ≤ b), Nat.cast_one]
    ring
  have hH : H ≤ 65*(h : ℝ)*m*Real.log 2 := by
    have hhm : 2 ≤ h*m := (by omega : 2 ≤ m).trans (Nat.le_mul_of_pos_left _ hh)
    simpa only [H, mul_assoc, Nat.cast_mul] using strict_structured_harmonic_upper (h*m) hhm
  have hnum : Real.log (N : ℝ)*((2/675 : ℝ)*H) ≤ (27/32 : ℝ)*D := by
    calc
      _ ≤ Real.log (N : ℝ)*((2/675 : ℝ)*(65*(h : ℝ)*m*Real.log 2)) := by gcongr
      _ = ((8320/675 : ℝ)*(t : ℝ)*h)*((m : ℝ)*Real.log 2)^2 := by rw [hlog]; ring
      _ ≤ ((27/32 : ℝ)*((b : ℝ)-1)^2)*((m : ℝ)*Real.log 2)^2 := by gcongr
      _ = _ := by rw [hDeq]; ring
  have hcoeff : Real.log (N : ℝ)*((2/675 : ℝ)*H/D) ≤ 27/32 := by
    rw [← mul_div_assoc]
    exact (div_le_iff₀ hD).mpr hnum
  calc
    _ = (N : ℝ)*(Real.log (N : ℝ)*((2/675 : ℝ)*H/D)) := by
      dsimp only [independentSieveMain, N, H, D]
      ring
    _ ≤ (N : ℝ)*(27/32) := mul_le_mul_of_nonneg_left hcoeff (Nat.cast_nonneg _)
    _ = _ := by ring

theorem chebyshev_independent_smooth_weight_retained (r t m Y : ℕ) (hm : 1 ≤ m)
    (A E : ℝ)
    (hweight : (7/8 : ℝ)*(2^(64*t*m) : ℝ)*primeProductReciprocalMass r m ≤
      ∑ d ∈ primeProductModuli r m, residueOneMangoldt d (2^(64*t*m)))
    (hrough : (∑ d ∈ primeProductModuli r m,
      ((roughProgressionPrimes d Y (2^(64*t*m))).card : ℝ)) ≤
        A*primeProductReciprocalMass r m+E)
    (hmain : Real.log (2^(64*t*m) : ℕ)*A ≤ (27/32 : ℝ)*(2^(64*t*m) : ℝ))
    (herror : Real.log (2^(64*t*m) : ℕ)*
      (E+2*((t-1).choose r : ℝ)*Real.sqrt (2^(64*t*m) : ℕ)) ≤
        (2^(64*t*m) : ℝ)/64*primeProductReciprocalMass r m) :
    (2^(64*t*m) : ℝ)/64*primeProductReciprocalMass r m ≤
      ((t-1).choose r : ℝ)*Real.log (2^(64*t*m) : ℕ)*
        ((smoothStructuredPrimes r m (2^(64*t*m)) Y).card : ℝ) := by
  have hW : 0 ≤ primeProductReciprocalMass r m :=
    sum_nonneg (fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))
  have hup := product_progression_weight_le_smooth_structured_count r t m Y hm
  have hr := mul_le_mul_of_nonneg_left hrough (Real.log_natCast_nonneg (2^(64*t*m)))
  have hma := mul_le_mul_of_nonneg_right hmain hW
  linarith only [hweight, hup, hr, hma, herror]

theorem eventually_chebyshev_independent_retained_weight (r t b h : ℕ)
    (heq : r+b+h=t) (hrt : 2*r+1 ≤ t) (hb : 2 ≤ b) (hh : 1 ≤ h)
    (hcap : t+5 ≤ 5*b)
    (hc : (8320/675 : ℝ)*(t : ℝ)*h ≤ (27/32 : ℝ)*((b : ℝ)-1)^2) :
    ∀ᶠ m : ℕ in atTop,
      (independentN t m : ℝ)/64*primeProductReciprocalMass r m ≤
        ((t-1).choose r : ℝ)*Real.log (independentN t m : ℝ)*
          ((smoothStructuredPrimes r m (independentN t m) (independentN b m)).card : ℝ) := by
  filter_upwards [eventually_product_mangoldt_weight_seven_eighths r t hrt,
    eventually_independent_total_error_small r t b h heq (by omega),
    eventually_ge_atTop (max 2 r), eventually_independent_endpoint b hb] with m hw he hm hend
  have hw' : (7/8 : ℝ)*(2^(64*t*m) : ℝ)*primeProductReciprocalMass r m ≤
      ∑ d ∈ primeProductModuli r m, residueOneMangoldt d (2^(64*t*m)) := by
    simpa only [progressionScaleN, mul_assoc, Nat.cast_pow, Nat.cast_ofNat] using hw
  have hr := independent_rough_count_le r t b h m heq hb hcap hm hend
  have hmain := chebyshev_independent_sieve_main_small t b h m hb hh (by omega) hc
  have hg := chebyshev_independent_smooth_weight_retained r t m (independentN b m) (by omega)
    (independentSieveMain t b h m) (independentSieveError r b h m) hw' hr
    (by simpa only [independentN, Nat.cast_pow, Nat.cast_ofNat] using hmain)
    (by simpa only [independentN, Nat.cast_pow, Nat.cast_ofNat] using he)
  simpa only [independentN, Nat.cast_pow, Nat.cast_ofNat] using hg

theorem eventually_chebyshev_independent_smooth_family (r t b h : ℕ)
    (heq : r+b+h=t) (hrt : 2*r+1 ≤ t) (hb : 2 ≤ b) (hh : 1 ≤ h)
    (hcap : t+5 ≤ 5*b)
    (hc : (8320/675 : ℝ)*(t : ℝ)*h ≤ (27/32 : ℝ)*((b : ℝ)-1)^2) :
    ∀ᶠ m : ℕ in atTop, ∃ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ p ≤ 2^(64*t*m) ∧
        p-1 ∈ Nat.smoothNumbers (2^(64*b*m))) ∧
      2^(64*t*m) ≤ (2*structuredPrimeCountConstant r t)*(m+1)^(r+1)*P.card := by
  filter_upwards [eventually_product_reciprocal_supply r,
    eventually_chebyshev_independent_retained_weight r t b h heq hrt hb hh hcap hc] with m hm hw
  refine ⟨smoothStructuredPrimes r m (independentN t m) (independentN b m), ?_,
    independent_count_of_weight r t b m hm hw⟩
  intro p hp
  obtain ⟨hpP, hps⟩ := mem_filter.mp hp
  obtain ⟨hpN, _⟩ := mem_filter.mp hpP
  have hpdata := Nat.mem_primesBelow.mp hpN
  exact ⟨hpdata.2, by change p ≤ independentN t m; omega, hps⟩

theorem infinite_g_gt_chebyshev_parameters (r t b h : ℕ)
    (heq : r+b+h=t) (hrt : 2*r+1 ≤ t) (hb : 2 ≤ b) (hh : 1 ≤ h)
    (hcap : t+5 ≤ 5*b)
    (hc : (8320/675 : ℝ)*(t : ℝ)*h ≤ (27/32 : ℝ)*((b : ℝ)-1)^2)
    (γ : ℝ) (hγ : γ < 1-(b : ℝ)/t) :
    {n : ℕ | (g n : ℝ) > (n : ℝ)^γ}.Infinite := by
  apply infinite_g_gt_of_eventual_polynomial_count (64*t) (64*b) 1
    (2*structuredPrimeCountConstant r t) (r+1) (by omega) ?_ γ ?_
  · filter_upwards [eventually_chebyshev_independent_smooth_family r t b h heq hrt hb hh hcap hc] with m hm
    simpa only [one_mul] using hm
  · simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_div_mul_left _ _ (by norm_num : (64 : ℝ) ≠ 0)] using hγ

/-- An explicit fixed exponent. No limiting iteration is asserted. -/
theorem infinite_g_gt_chebyshev_uniform (γ : ℝ) (hγ : γ < 2064/4001) :
    {n : ℕ | (g n : ℝ) > (n : ℝ)^γ}.Infinite := by
  apply infinite_g_gt_chebyshev_parameters 2000 4001 1937 64
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) γ
  norm_num
  exact hγ

/-- The corresponding range of the original inequality. -/
theorem erdos_821_chebyshev_range (ε : ℝ) (hε : 1937/4001 < ε) :
    {n : ℕ | (g n : ℝ) > (n : ℝ)^(1-ε)}.Infinite := by
  exact infinite_g_gt_chebyshev_uniform (1-ε) (by linarith only [hε])

theorem erdos_821_chebyshev_point_four_eight_five (ε : ℝ) (hε : 97/200 < ε) :
    {n : ℕ | (g n : ℝ) > (n : ℝ)^(1-ε)}.Infinite := by
  apply erdos_821_chebyshev_range ε
  exact lt_trans (by norm_num : (1937/4001 : ℝ) < 97/200) hε

end Erdos821
