import Submission.AlmostAllPrimeCofactorCurrents

/-! Simultaneously zero whole-multiple currents for almost all primes, with
cofactor range growing as any fixed sublinear power of log X. This is still
an exponent-one boundary result, not a natural-density theorem. -/
namespace Erdos371
open Finset Filter FiniteSieve DilationSpectrum
open scoped Topology

lemma logPower_bothAbove_linear_eventual_scaled_bound (a : ℝ) (ha : 0 ≤ a) :
    ∀ᶠ X : ℕ in atTop,
      ((bothAboveSet X ((2*logPowerCofactorCutoff a X+1)*X)).card : ℝ)*Real.log X/X ≤
        16*largePairConstant*(Real.log 2+a*Real.log (Real.log X)+1)^2/
          (Real.log X)^(1-a) +
        (4*(2 : ℝ)^65)*(Real.log X)^(a+1)/(X : ℝ)^(1/2 : ℝ) := by
  filter_upwards [logPowerCofactor_cutoff_data a ha,
    (logPowerCofactorExponent_tendsto_zero a).eventually_le_const
      (by norm_num : (0 : ℝ) < 1/16),eventually_ge_atTop (2 : ℕ)]
    with X hd hu hX
  obtain ⟨hL,hK,_,_,_⟩ := hd
  let K := logPowerCofactorCutoff a X
  let c := 2*K+1
  let W : ℝ := (Real.log X)^a
  let A : ℝ := Real.log 2+a*Real.log (Real.log X)+1
  have hc : 0 < c := by dsimp [c]; omega
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hX0 : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hL0 : 0 < Real.log X := by linarith
  have hLL : 0 ≤ Real.log (Real.log X) := Real.log_nonneg hL
  have h2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hW1 : 1 ≤ W := Real.one_le_rpow hL ha
  have hKW : (K : ℝ) ≤ W := Nat.floor_le (Real.rpow_nonneg hL0.le a)
  have hcW : (c : ℝ) ≤ 4*W := by dsimp [c]; push_cast; linarith
  have hlog4 : Real.log (4 : ℝ) = 2*Real.log 2 := by
    rw [show (4 : ℝ) = 2^2 by norm_num,Real.log_pow]
    norm_num
  have hlogc : Real.log c ≤ 2*(Real.log 2+a*Real.log (Real.log X)) := by
    have h := Real.log_le_log hcR hcW
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0)
      (Real.rpow_pos_of_pos hL0 a).ne',Real.log_rpow hL0,hlog4] at h
    nlinarith [mul_nonneg ha hLL]
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hlogc1 : Real.log c+1 ≤ 2*A := by dsimp only [A]; linarith
  have hXN : X ≤ c*X := by nlinarith
  have hlogXN : Real.log X ≤ Real.log (c*X : ℕ) :=
    Real.log_le_log hX0 (by exact_mod_cast hXN)
  have hcu : Real.log c/Real.log (c*X : ℕ) ≤ 1/8 := by
    have huform : logPowerCofactorExponent a X =
        (Real.log 2+a*Real.log (Real.log X))/Real.log X := by
      unfold logPowerCofactorExponent
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
        (Real.rpow_pos_of_pos hL0 a).ne',Real.log_rpow hL0]
    calc
      _ ≤ Real.log c/Real.log X :=
        div_le_div_of_nonneg_left (Real.log_natCast_nonneg c) hL0 hlogXN
      _ ≤ 2*(Real.log 2+a*Real.log (Real.log X))/Real.log X :=
        div_le_div_of_nonneg_right hlogc hL0.le
      _ = 2*logPowerCofactorExponent a X := by rw [huform]; ring
      _ ≤ 1/8 := by linarith
  have hC : 0 ≤ largePairConstant := by unfold largePairConstant; positivity
  have hmain : largePairConstant*c*(Real.log c+1)^2/Real.log X ≤
      16*largePairConstant*A^2/(Real.log X)^(1-a) := by
    have hsq := pow_le_pow_left₀ (by have := Real.log_natCast_nonneg c; positivity :
      0 ≤ Real.log c+1) hlogc1 2
    have hprod := mul_le_mul hcW hsq (sq_nonneg (Real.log c+1)) (by positivity)
    have hmul := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hprod hC) hL0.le
    apply (show largePairConstant*c*(Real.log c+1)^2/Real.log X ≤
      largePairConstant*(4*W)*(2*A)^2/Real.log X by
        simpa only [mul_assoc] using hmul).trans_eq
    rw [Real.rpow_sub hL0,Real.rpow_one]
    dsimp only [W]
    field_simp
    ring
  have herr : (2 : ℝ)^65*c*Real.log X/(X : ℝ)^(1/2 : ℝ) ≤
      (4*(2 : ℝ)^65)*(Real.log X)^(a+1)/(X : ℝ)^(1/2 : ℝ) := by
    have h := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcW (show 0 ≤ (2 : ℝ)^65 by positivity)) hL0.le)
      (Real.rpow_nonneg hX0.le (1/2 : ℝ))
    apply h.trans_eq
    rw [Real.rpow_add hL0,Real.rpow_one]
    dsimp only [W]
    ring
  exact (bothAbove_linear_scaled_log_bound c X hc hX hcu).trans
    (add_le_add hmain herr)

/-- The finite two-large-factor cover is o(X/log X), even when its
cofactor parameter grows as floor((log X)^a), for 0<=a<1. -/
theorem logPower_bothAbove_linear_scaled_count_tendsto (a : ℝ)
    (ha : 0 ≤ a) (ha1 : a < 1) :
    Tendsto (fun X : ℕ =>
      ((bothAboveSet X ((2*logPowerCofactorCutoff a X+1)*X)).card : ℝ)*Real.log X/X)
      atTop (𝓝 0) := by
  have hlog : Tendsto (fun X : ℕ => Real.log X) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hmain := ((affine_log_square_div_rpow_tendsto_zero a (1-a)
    (by linarith)).comp hlog).const_mul (16*largePairConstant)
  have herr := (log_nat_rpow_div_rpow_tendsto_zero (a+1) (1/2)
    (by norm_num)).const_mul (4*(2 : ℝ)^65)
  have ht := hmain.add herr
  simp only [mul_zero,add_zero] at ht
  apply squeeze_zero' (Eventually.of_forall (fun X => by
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg X))
      (Nat.cast_nonneg X))) _ ht
  simpa only [Function.comp_apply,mul_div_assoc] using
    logPower_bothAbove_linear_eventual_scaled_bound a ha

lemma logPower_badCofactorPrimes_eventual_scaled_bound (a : ℝ) (ha : 0 ≤ a) :
    ∀ᶠ X : ℕ in atTop,
      ((badCofactorPrimes (logPowerCofactorCutoff a X) X).card : ℝ)*Real.log X/X ≤
        16*largePairConstant*(Real.log 2+a*Real.log (Real.log X)+1)^2/
          (Real.log X)^(1-a) +
        (4*(2 : ℝ)^65)*(Real.log X)^(a+1)/(X : ℝ)^(1/2 : ℝ) := by
  filter_upwards [logPower_bothAbove_linear_eventual_scaled_bound a ha,
    eventually_gt_atTop (0 : ℕ)] with X hb hX
  apply le_trans ?_ hb
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
    ((Nat.cast_le (α := ℝ)).mpr
      (badCofactorPrimes_card_le (logPowerCofactorCutoff a X) X hX))
    (Real.log_natCast_nonneg X)) (Nat.cast_nonneg X)

theorem logPower_badCofactorPrimes_scaled_count_tendsto (a : ℝ)
    (ha : 0 ≤ a) (ha1 : a < 1) :
    Tendsto (fun X : ℕ =>
      ((badCofactorPrimes (logPowerCofactorCutoff a X) X).card : ℝ)*Real.log X/X)
      atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun X => by
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg X))
      (Nat.cast_nonneg X))) _ (logPower_bothAbove_linear_scaled_count_tendsto a ha ha1)
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with X hX
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
    ((Nat.cast_le (α := ℝ)).mpr
      (badCofactorPrimes_card_le (logPowerCofactorCutoff a X) X hX))
    (Real.log_natCast_nonneg X)) (Nat.cast_nonneg X)

/-- Almost every prime in the dyadic band has all these growing-range
whole-multiple currents exactly zero. -/
theorem logPower_badCofactorPrimes_prime_proportion_tendsto (a : ℝ)
    (ha : 0 ≤ a) (ha1 : a < 1) :
    Tendsto (fun X : ℕ =>
      ((badCofactorPrimes (logPowerCofactorCutoff a X) X).card : ℝ)/
        (narrowPrimeBand 1 2 X).card) atTop (𝓝 0) := by
  have hden := narrowPrimeBand_card_scaled_limit 1 2 (by norm_num) (by norm_num)
  norm_num only at hden
  have ht := (logPower_badCofactorPrimes_scaled_count_tendsto a ha ha1).div hden one_ne_zero
  simp only [zero_div] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with X hX
  have hx : (X : ℝ) ≠ 0 := by exact_mod_cast (show X ≠ 0 by omega)
  have hl : Real.log X ≠ 0 := (Real.log_pos (by exact_mod_cast hX)).ne'
  simp only [Pi.div_apply]
  field_simp

#print axioms logPower_badCofactorPrimes_eventual_scaled_bound
#print axioms logPower_badCofactorPrimes_scaled_count_tendsto
#print axioms logPower_badCofactorPrimes_prime_proportion_tendsto
end Erdos371
