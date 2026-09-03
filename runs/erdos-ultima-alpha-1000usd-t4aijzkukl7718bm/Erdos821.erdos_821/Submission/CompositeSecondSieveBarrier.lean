import Submission.StructuredSecondSieve

/-!
# Cutoff limitation of the explicit composite second-sieve bound

This concerns an upper-bound formula, NOT the true number of rejected primes.
At cube-root or smaller smoothness cutoffs, that formula cannot be made small
by changing the sieve cutoff. It is not a disproof of Erdős 821.
-/

open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators

namespace Erdos821

open AnalyticSieve

set_option maxHeartbeats 2000000

lemma totientRatioAverageConstant_ge_one : 1 ≤ Sieve.totientRatioAverageConstant := by
  unfold Sieve.totientRatioAverageConstant
  exact Real.one_le_exp (mul_nonneg (by norm_num) (tsum_nonneg (fun n => inv_nonneg.mpr (sq_nonneg _))))

lemma log_progression_scale_ge (a : ℕ) :
    (a : ℝ) ≤ Real.log (2 ^ (64 * a) : ℕ) := by
  simp only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow, Nat.cast_mul]
  have hlog : (1 : ℝ) ≤ 64 * Real.log 2 := by linarith [Real.log_two_gt_d9]
  nlinarith [mul_le_mul_of_nonneg_right hlog (Nat.cast_nonneg (α := ℝ) a)]

lemma harmonic_progression_scale_ge (a : ℕ) :
    (a : ℝ) ≤ (harmonic (2 ^ (64 * a)) : ℝ) := by
  exact (log_progression_scale_ge a).trans
    ((log_nat_mono (Nat.le_succ _)).trans (log_add_one_le_harmonic _))

/-- In the below-half modulus range, a cube-root smoothness cutoff leaves a
cofactor exponent whose product with the total exponent is not small. -/
lemma cube_root_cofactor_exponent_bound (r t b : ℕ)
    (hrt : 2 * r ≤ t) (hbt : 3 * b ≤ t) :
    b^2 ≤ 2 * t * (t - r - b) := by
  have hrb : r + b ≤ t := by omega
  have heq : t - r - b + r + b = t := by omega
  nlinarith [sq_nonneg (t - 3*b), Nat.mul_le_mul hbt (show b ≤ 2 * (t - r - b) by omega)]

/-- If the cutoff is not too large, the nonnegative main-term bound itself
exceeds the full scale, before multiplying by reciprocal-modulus mass. -/
theorem composite_second_sieve_main_ge_scale (r t b m J : ℕ)
    (hrt : 2 * r ≤ t) (hbt : 3 * b ≤ t) (hJ : 0 < J) (hJb : J ≤ b * m) :
    (2 : ℝ) ^ (64 * t * m) ≤
      Real.log (2 ^ (64 * t * m) : ℕ) *
        (32 * Sieve.totientRatioAverageConstant * (2 : ℝ) ^ (64 * t * m) *
          (harmonic (2 ^ (64 * (t - r - b) * m)) : ℝ) / ((J : ℝ) * Real.log 2)^2) := by
  let N : ℝ := (2 : ℝ) ^ (64 * t * m)
  let L := Real.log (2 ^ (64 * t * m) : ℕ)
  let H : ℝ := harmonic (2 ^ (64 * (t - r - b) * m))
  let D := ((J : ℝ) * Real.log 2)^2
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hL : 0 ≤ L := Real.log_natCast_nonneg _
  have hH : 0 ≤ H := harmonic_real_nonneg _
  have hD : 0 < D := sq_pos_of_pos (mul_pos (by exact_mod_cast hJ) (Real.log_pos (by norm_num)))
  have hJlog : (J : ℝ) * Real.log 2 ≤ (b : ℝ) * m := by
    have hJbR : (J : ℝ) ≤ (b : ℝ) * m := by exact_mod_cast hJb
    have hl : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
    nlinarith [Nat.cast_nonneg (α := ℝ) J]
  have hJD : D ≤ ((b : ℝ) * m)^2 :=
    pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num))) hJlog 2
  have hLlo : (t : ℝ) * m ≤ L := by
    simpa only [L, Nat.cast_mul, mul_assoc] using log_progression_scale_ge (t * m)
  have hHlo : ((t - r - b : ℕ) : ℝ) * m ≤ H := by
    simpa only [H, Nat.cast_mul, mul_assoc] using harmonic_progression_scale_ge ((t - r - b) * m)
  have hbc : (b : ℝ)^2 ≤ 2 * (t : ℝ) * ((t - r - b : ℕ) : ℝ) := by
    exact_mod_cast cube_root_cofactor_exponent_bound r t b hrt hbt
  have hDLH : D ≤ 2 * L * H := by
    calc
      D ≤ ((b : ℝ) * m)^2 := hJD
      _ = (b : ℝ)^2 * (m : ℝ)^2 := by ring
      _ ≤ (2 * (t : ℝ) * ((t - r - b : ℕ) : ℝ)) * (m : ℝ)^2 :=
        mul_le_mul_of_nonneg_right hbc (sq_nonneg _)
      _ = 2 * ((t : ℝ) * m) * (((t - r - b : ℕ) : ℝ) * m) := by ring
      _ ≤ 2 * L * H := by gcongr
  have hC : 2 ≤ 32 * Sieve.totientRatioAverageConstant := by
    linarith [totientRatioAverageConstant_ge_one]
  have hDmain : D ≤ L * (32 * Sieve.totientRatioAverageConstant) * H := by
    calc
      _ ≤ 2 * L * H := hDLH
      _ ≤ (32 * Sieve.totientRatioAverageConstant) * L * H := by gcongr
      _ = _ := by ring
  change N ≤ L * (32 * Sieve.totientRatioAverageConstant * N * H / D)
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hD).mpr
  calc
    _ ≤ N * (L * (32 * Sieve.totientRatioAverageConstant) * H) :=
      mul_le_mul_of_nonneg_left hDmain hN
    _ = _ := by ring

/-- Lower envelope of the explicit rejected-count majorant after dividing
out its reciprocal-totient mass. The true rejected count is not bounded below. -/
noncomputable def compositeSecondSieveCost (r t b m J : ℕ) : ℝ :=
  Real.log (2 ^ (64 * t * m) : ℕ) *
    (32 * Sieve.totientRatioAverageConstant * (2 : ℝ) ^ (64 * t * m) *
        (harmonic (2 ^ (64 * (t - r - b) * m)) : ℝ) / ((J : ℝ) * Real.log 2)^2 +
      (2 : ℝ) ^ (64 * r * m) * (2 : ℝ) ^ (64 * (t - r - b) * m) *
        ((2 : ℝ) ^ (64 * J) + (2 : ℝ) ^ (16 * J) + 1))

/-- No cutoff tuning makes this majorant smaller than the main scale at
cube-root (or smaller) smoothness. This is solely a limitation of the bound. -/
theorem composite_second_sieve_cost_ge_scale (r t b m J : ℕ)
    (hrt : 2 * r ≤ t) (hbt : 3 * b ≤ t) (ht : 1 ≤ t) (hm : 1 ≤ m) (hJ : 0 < J) :
    (2 : ℝ) ^ (64 * t * m) ≤ compositeSecondSieveCost r t b m J := by
  have hlog : 1 ≤ Real.log (2 ^ (64 * t * m) : ℕ) := by
    have htm : (1 : ℝ) ≤ (t * m : ℕ) := by exact_mod_cast Nat.mul_pos ht hm
    exact htm.trans (by simpa only [mul_assoc] using log_progression_scale_ge (t * m))
  have hH : 0 ≤ (harmonic (2 ^ (64 * (t - r - b) * m)) : ℝ) := harmonic_real_nonneg _
  have hC : 0 ≤ Sieve.totientRatioAverageConstant := le_trans (by norm_num) totientRatioAverageConstant_ge_one
  by_cases hJb : J ≤ b * m
  · apply (composite_second_sieve_main_ge_scale r t b m J hrt hbt hJ hJb).trans
    unfold compositeSecondSieveCost
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity)) (by linarith)
  · have heq : r + (t - r - b) + b = t := by omega
    have hpow : (2 : ℝ) ^ (64 * t * m) ≤
        (2 : ℝ) ^ (64 * r * m) * (2 : ℝ) ^ (64 * (t - r - b) * m) * (2 : ℝ) ^ (64 * J) := by
      rw [← pow_add, ← pow_add]
      apply pow_le_pow_right₀ (by norm_num)
      have heq' := congrArg (fun x : ℕ => 64 * x * m) heq
      nlinarith only [heq', show b * m ≤ J by omega]
    have hE : (2 : ℝ) ^ (64 * t * m) ≤
        (2 : ℝ) ^ (64 * r * m) * (2 : ℝ) ^ (64 * (t - r - b) * m) *
          ((2 : ℝ) ^ (64 * J) + (2 : ℝ) ^ (16 * J) + 1) := by
      apply hpow.trans
      gcongr
      linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (16 * J)]
    unfold compositeSecondSieveCost
    have hmain : 0 ≤ 32 * Sieve.totientRatioAverageConstant * (2 : ℝ) ^ (64 * t * m) *
        (harmonic (2 ^ (64 * (t - r - b) * m)) : ℝ) / ((J : ℝ) * Real.log 2)^2 := by positivity
    nlinarith only [hE, hlog, hmain, mul_nonneg (show 0 ≤ Real.log (2 ^ (64 * t * m) : ℕ) by linarith) hmain,
      mul_le_mul_of_nonneg_right hlog (show 0 ≤ (2 : ℝ) ^ (64 * r * m) * (2 : ℝ) ^ (64 * (t - r - b) * m) *
        ((2 : ℝ) ^ (64 * J) + (2 : ℝ) ^ (16 * J) + 1) by positivity)]

lemma prime_product_mass_mul_lower_le_card (r m : ℕ) :
    (2 : ℝ) ^ (64 * r * m) * primeProductReciprocalMass r m ≤
      ((primeProductModuli r m).card : ℝ) := by
  unfold primeProductReciprocalMass
  rw [mul_sum]
  calc
    _ ≤ ∑ _d ∈ primeProductModuli r m, (1 : ℝ) := by
      apply sum_le_sum
      intro d hd
      have hφ : (0 : ℝ) < d.totient := by
        exact_mod_cast Nat.totient_pos.mpr (primeProductModuli_properties hd).1
      have hlo : (2 : ℝ) ^ (64 * r * m) ≤ (d.totient : ℝ) := by
        have h := primeProductModuli_totient_lower hd
        have he : progressionScaleN m ^ r = 2 ^ (64 * r * m) := by
          simp only [progressionScaleN, ← pow_mul]
          congr 1
          ring
        rw [he] at h
        exact_mod_cast h
      rw [← div_eq_mul_inv]
      exact (div_le_one hφ).mpr hlo
    _ = _ := by simp

/-- The explicit majorant actually furnished by the composite prime-pair
sieve, including its full family-cardinality error. -/
noncomputable def compositeSecondSieveMajorant (r t b m J : ℕ) : ℝ :=
  Real.log (2 ^ (64 * t * m) : ℕ) *
    ((32 * Sieve.totientRatioAverageConstant * (2 : ℝ) ^ (64 * t * m) *
        (harmonic (2 ^ (64 * (t - r - b) * m)) : ℝ) / ((J : ℝ) * Real.log 2)^2) *
        primeProductReciprocalMass r m +
      ((primeProductModuli r m).card : ℝ) * (2 : ℝ) ^ (64 * (t - r - b) * m) *
        ((2 : ℝ) ^ (64 * J) + (2 : ℝ) ^ (16 * J) + 1))

lemma composite_second_sieve_cost_mul_mass_le (r t b m J : ℕ) :
    compositeSecondSieveCost r t b m J * primeProductReciprocalMass r m ≤
      compositeSecondSieveMajorant r t b m J := by
  have h := prime_product_mass_mul_lower_le_card r m
  unfold compositeSecondSieveCost compositeSecondSieveMajorant
  rw [mul_assoc, add_mul]
  apply mul_le_mul_of_nonneg_left _ (Real.log_natCast_nonneg _)
  apply _root_.add_le_add le_rfl
  calc
    _ = ((2 : ℝ) ^ (64 * r * m) * primeProductReciprocalMass r m) *
        (2 : ℝ) ^ (64 * (t - r - b) * m) * ((2 : ℝ) ^ (64 * J) + (2 : ℝ) ^ (16 * J) + 1) := by ring
    _ ≤ _ := by gcongr

theorem composite_second_sieve_majorant_ge_scale_mass (r t b m J : ℕ)
    (hrt : 2 * r ≤ t) (hbt : 3 * b ≤ t) (ht : 1 ≤ t) (hm : 1 ≤ m) (hJ : 0 < J) :
    (2 : ℝ) ^ (64 * t * m) * primeProductReciprocalMass r m ≤
      compositeSecondSieveMajorant r t b m J := by
  have hW : 0 ≤ primeProductReciprocalMass r m :=
    sum_nonneg (fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))
  exact (mul_le_mul_of_nonneg_right
    (composite_second_sieve_cost_ge_scale r t b m J hrt hbt ht hm hJ) hW).trans
      (composite_second_sieve_cost_mul_mass_le r t b m J)

/-- Under the geometric scale conditions, this is the actual upper bound
obtained by the composite-modulus second sieve. -/
theorem composite_second_sieve_rejected_weight_le (r t b m J : ℕ)
    (hrb : r + b ≤ t) (hb : 2 ≤ b) (hm : 2 ≤ m) (hrm : r ≤ b * m)
    (hφ : 2^r ≤ progressionScaleN m) (hJ : 0 < J) :
    Real.log (2 ^ (64 * t * m) : ℕ) *
      (∑ d ∈ primeProductModuli r m,
        ((roughProgressionPrimes d (2 ^ (64 * b * m)) (2 ^ (64 * t * m))).card : ℝ)) ≤
      compositeSecondSieveMajorant r t b m J := by
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
  have hbound := rough_composite_family_reciprocal_count_le (primeProductModuli r m)
    (2 ^ (64 * r * m)) (2 ^ (64 * r * (m + 1))) (2 ^ (64 * t * m))
    (2 ^ (64 * (t - r - b) * m)) (2 ^ (64 * b * m)) J hM hX hKX hJ
  have hw := mul_le_mul_of_nonneg_left hbound (Real.log_natCast_nonneg (2 ^ (64 * t * m)))
  simpa only [compositeSecondSieveMajorant, primeProductReciprocalMass, Nat.cast_pow, Nat.cast_ofNat] using hw

/-- The failure is in this sufficient estimate, not in the conjecture. -/
theorem composite_second_sieve_majorant_not_small (r t b m J : ℕ)
    (hrt : 2 * r ≤ t) (hbt : 3 * b ≤ t) (ht : 1 ≤ t) (hm : 1 ≤ m) (hJ : 0 < J)
    (hW : 0 < primeProductReciprocalMass r m) :
    ¬compositeSecondSieveMajorant r t b m J ≤
      (2 : ℝ) ^ (64 * t * m) / 16 * primeProductReciprocalMass r m := by
  intro h
  have hge := composite_second_sieve_majorant_ge_scale_mass r t b m J hrt hbt ht hm hJ
  have hpos := mul_pos (pow_pos (by norm_num : (0 : ℝ) < 2) (64 * t * m)) hW
  linarith only [h, hge, hpos]

end Erdos821
