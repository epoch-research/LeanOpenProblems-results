import Submission.IndependentCompositeScales

/-!
# A fixed exponent from independent structured parameters

The number of prescribed block-prime factors r and the smoothness exponent b
are not required to be equal. This improves a fixed exponent, not the full
Erdős 821 assertion.
-/

open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators
namespace Erdos821
open AnalyticSieve
set_option maxHeartbeats 3000000

lemma independent_sieve_main_small (t b h m : ℕ) (hb : 2 ≤ b)
    (hh : 1 ≤ h) (hm : 2 ≤ m)
    (hc : (8320/675 : ℝ)*(t : ℝ)*h ≤ (17/32 : ℝ)*((b : ℝ)-1)^2) :
    Real.log (independentN t m : ℝ)*independentSieveMain t b h m ≤
      (17/32 : ℝ)*(independentN t m : ℝ) := by
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
  have hnum : Real.log (N : ℝ)*((2/675 : ℝ)*H) ≤ (17/32 : ℝ)*D := by
    calc
      _ ≤ Real.log (N : ℝ)*((2/675 : ℝ)*(65*(h : ℝ)*m*Real.log 2)) := by gcongr
      _ = ((8320/675 : ℝ)*(t : ℝ)*h)*((m : ℝ)*Real.log 2)^2 := by rw [hlog]; ring
      _ ≤ ((17/32 : ℝ)*((b : ℝ)-1)^2)*((m : ℝ)*Real.log 2)^2 := by gcongr
      _ = _ := by rw [hDeq]; ring
  have hcoeff : Real.log (N : ℝ)*((2/675 : ℝ)*H/D) ≤ 17/32 := by
    rw [← mul_div_assoc]
    exact (div_le_iff₀ hD).mpr hnum
  calc
    _ = (N : ℝ)*(Real.log (N : ℝ)*((2/675 : ℝ)*H/D)) := by
      dsimp only [independentSieveMain, N, H, D]
      ring
    _ ≤ (N : ℝ)*(17/32) := mul_le_mul_of_nonneg_left hcoeff (Nat.cast_nonneg _)
    _ = _ := by ring

lemma independent_coefficient_cap (r t b h m : ℕ) (heq : r+b+h=t)
    (hb : 2 ≤ b) (hcap : t+5 ≤ 5*b) (hm : r ≤ m) :
    2^(64*r*(m+1))*2^(64*h*m) ≤ 2^(256*independentJ b m) := by
  rw [← pow_add]
  apply Nat.pow_le_pow_right (by decide)
  dsimp only [independentJ]
  have hsub := congrArg (fun z : ℕ => z*m)
    (Nat.sub_add_cancel (by omega : 1 ≤ b))
  have heqm := congrArg (fun z : ℕ => z*m) heq
  have hcapm := Nat.mul_le_mul_right m hcap
  nlinarith only [hsub, heqm, hcapm, hm]

lemma independent_rough_count_le (r t b h m : ℕ) (heq : r+b+h=t)
    (hb : 2 ≤ b) (hcap : t+5 ≤ 5*b) (hm : max 2 r ≤ m)
    (hendpoint : EndpointPairAt (independentJ b m)) :
    (∑ d ∈ primeProductModuli r m,
      ((roughProgressionPrimes d (independentN b m) (independentN t m)).card : ℝ)) ≤
        independentSieveMain t b h m*primeProductReciprocalMass r m +
          independentSieveError r b h m := by
  have hh : t-r-b=h := by omega
  have hJ : 0 < independentJ b m := Nat.mul_pos (by omega) (by omega)
  have hcap' := independent_coefficient_cap r t b h m heq hb hcap (by omega)
  have hrm : r ≤ b*m := (by omega : r ≤ m).trans (Nat.le_mul_of_pos_left _ (by omega))
  have hmain := composite_second_sieve_rejected_weight_endpoint r t b m (independentJ b m)
    (by omega) hb (by omega) hrm hJ (by simpa only [hh] using hcap') hendpoint
  have hlog : 0 < Real.log (independentN t m : ℝ) := by
    have hlarge : (0 : ℝ) < (t*m : ℕ) := by
      exact_mod_cast Nat.mul_pos (by omega : 0 < t) (by omega : 0 < m)
    exact hlarge.trans_le (by simpa only [independentN, mul_assoc] using log_progression_scale_ge (t*m))
  have hmain' : Real.log (independentN t m : ℝ)*
      (∑ d ∈ primeProductModuli r m,
        ((roughProgressionPrimes d (independentN b m) (independentN t m)).card : ℝ)) ≤
      Real.log (independentN t m : ℝ)*
        (independentSieveMain t b h m*primeProductReciprocalMass r m +
          independentSieveError r b h m) := by
    simpa only [endpointCompositeSecondSieveMajorant, independentN,
      independentSieveMain, independentSieveError, hh, Nat.cast_pow, Nat.cast_ofNat] using hmain
  exact (mul_le_mul_iff_right₀ hlog).mp hmain'

lemma eventually_independent_endpoint (b : ℕ) (hb : 2 ≤ b) :
    ∀ᶠ m : ℕ in atTop, EndpointPairAt (independentJ b m) := by
  apply (show Tendsto (fun m : ℕ => independentJ b m) atTop atTop from ?_).eventually
    eventually_endpoint_pair_at
  apply tendsto_atTop_mono (fun m => ?_) tendsto_id
  exact Nat.le_mul_of_pos_left _ (by omega)

theorem independent_smooth_weight_retained (r t m Y : ℕ) (hm : 1 ≤ m)
    (A E : ℝ)
    (hweight : (9/16 : ℝ)*(2^(64*t*m) : ℝ)*primeProductReciprocalMass r m ≤
      ∑ d ∈ primeProductModuli r m, residueOneMangoldt d (2^(64*t*m)))
    (hrough : (∑ d ∈ primeProductModuli r m,
      ((roughProgressionPrimes d Y (2^(64*t*m))).card : ℝ)) ≤
        A*primeProductReciprocalMass r m+E)
    (hmain : Real.log (2^(64*t*m) : ℕ)*A ≤ (17/32 : ℝ)*(2^(64*t*m) : ℝ))
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

theorem eventually_independent_retained_weight (r t b h : ℕ)
    (heq : r+b+h=t) (hrt : 2*r+1 ≤ t) (hb : 2 ≤ b) (hh : 1 ≤ h)
    (hcap : t+5 ≤ 5*b)
    (hc : (8320/675 : ℝ)*(t : ℝ)*h ≤ (17/32 : ℝ)*((b : ℝ)-1)^2) :
    ∀ᶠ m : ℕ in atTop,
      (independentN t m : ℝ)/64*primeProductReciprocalMass r m ≤
        ((t-1).choose r : ℝ)*Real.log (independentN t m : ℝ)*
          ((smoothStructuredPrimes r m (independentN t m) (independentN b m)).card : ℝ) := by
  filter_upwards [eventually_product_mangoldt_weight_nine_sixteenths r t hrt,
    eventually_independent_total_error_small r t b h heq (by omega),
    eventually_ge_atTop (max 2 r), eventually_independent_endpoint b hb] with m hw he hm hend
  have hw' : (9/16 : ℝ)*(2^(64*t*m) : ℝ)*primeProductReciprocalMass r m ≤
      ∑ d ∈ primeProductModuli r m, residueOneMangoldt d (2^(64*t*m)) := by
    simpa only [progressionScaleN, mul_assoc, Nat.cast_pow, Nat.cast_ofNat] using hw
  have hr := independent_rough_count_le r t b h m heq hb hcap hm hend
  have hmain := independent_sieve_main_small t b h m hb hh (by omega) hc
  have hg := independent_smooth_weight_retained r t m (independentN b m) (by omega)
    (independentSieveMain t b h m) (independentSieveError r b h m) hw' hr
    (by simpa only [independentN, Nat.cast_pow, Nat.cast_ofNat] using hmain)
    (by simpa only [independentN, Nat.cast_pow, Nat.cast_ofNat] using he)
  simpa only [independentN, Nat.cast_pow, Nat.cast_ofNat] using hg

theorem eventually_independent_smooth_family (r t b h : ℕ)
    (heq : r+b+h=t) (hrt : 2*r+1 ≤ t) (hb : 2 ≤ b) (hh : 1 ≤ h)
    (hcap : t+5 ≤ 5*b)
    (hc : (8320/675 : ℝ)*(t : ℝ)*h ≤ (17/32 : ℝ)*((b : ℝ)-1)^2) :
    ∀ᶠ m : ℕ in atTop, ∃ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ p ≤ 2^(64*t*m) ∧
        p-1 ∈ Nat.smoothNumbers (2^(64*b*m))) ∧
      2^(64*t*m) ≤ (2*structuredPrimeCountConstant r t)*(m+1)^(r+1)*P.card := by
  filter_upwards [eventually_product_reciprocal_supply r,
    eventually_independent_retained_weight r t b h heq hrt hb hh hcap hc] with m hm hw
  refine ⟨smoothStructuredPrimes r m (independentN t m) (independentN b m), ?_,
    independent_count_of_weight r t b m hm hw⟩
  intro p hp
  obtain ⟨hpP, hps⟩ := mem_filter.mp hp
  obtain ⟨hpN, _⟩ := mem_filter.mp hpP
  have hpdata := Nat.mem_primesBelow.mp hpN
  exact ⟨hpdata.2, by change p ≤ independentN t m; omega, hps⟩

theorem infinite_g_gt_independent_parameters (r t b h : ℕ)
    (heq : r+b+h=t) (hrt : 2*r+1 ≤ t) (hb : 2 ≤ b) (hh : 1 ≤ h)
    (hcap : t+5 ≤ 5*b)
    (hc : (8320/675 : ℝ)*(t : ℝ)*h ≤ (17/32 : ℝ)*((b : ℝ)-1)^2)
    (γ : ℝ) (hγ : γ < 1-(b : ℝ)/t) :
    {n : ℕ | (g n : ℝ) > (n : ℝ)^γ}.Infinite := by
  apply infinite_g_gt_of_eventual_polynomial_count (64*t) (64*b) 1
    (2*structuredPrimeCountConstant r t) (r+1) (by omega) ?_ γ ?_
  · filter_upwards [eventually_independent_smooth_family r t b h heq hrt hb hh hcap hc] with m hm
    simpa only [one_mul] using hm
  · simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_div_mul_left _ _ (by norm_num : (64 : ℝ) ≠ 0)] using hγ

/-- An explicit fixed exponent. No limiting iteration is asserted. -/
theorem infinite_g_gt_independent_uniform (γ : ℝ) (hγ : γ < 2041/4001) :
    {n : ℕ | (g n : ℝ) > (n : ℝ)^γ}.Infinite := by
  apply infinite_g_gt_independent_parameters 2000 4001 1960 41
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) γ
  norm_num
  exact hγ

/-- The corresponding range of the original inequality. -/
theorem erdos_821_independent_range (ε : ℝ) (hε : 1960/4001 < ε) :
    {n : ℕ | (g n : ℝ) > (n : ℝ)^(1-ε)}.Infinite := by
  exact infinite_g_gt_independent_uniform (1-ε) (by linarith only [hε])

theorem erdos_821_independent_point_four_nine (ε : ℝ) (hε : 49/100 < ε) :
    {n : ℕ | (g n : ℝ) > (n : ℝ)^(1-ε)}.Infinite := by
  apply erdos_821_independent_range ε
  exact lt_trans (by norm_num : (1960/4001 : ℝ) < 49/100) hε

end Erdos821
