import Submission.ProductConductorMean

/-!
# An exact cutoff audit of the existing Vaughan majorant

This concerns a particular nonnegative upper-bound formula, not the true
character sums. Its full-conductor contribution is already too large at the
square-root modulus scale, regardless of the two Vaughan cutoffs.
-/

open Nat Finset ArithmeticFunction
open scoped Classical BigOperators

namespace Erdos821

open AnalyticSieve

set_option maxHeartbeats 2000000

lemma log_dyadic_ge_one {a : ℕ} (ha : 2 ≤ a) :
    1 ≤ Real.log ((2 ^ a : ℕ) : ℝ) := by
  rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  have haR : (2 : ℝ) ≤ a := by exact_mod_cast ha
  nlinarith [Real.log_two_gt_d9]

lemma typeIIBlockMajorant_lower (Q X Y R : ℕ)
    (hXY : R ^ 2 ≤ X * Y) (hYlog : 1 ≤ Real.log (Y : ℝ)) :
    (Q : ℝ) ^ 2 * R ≤ typeIIBlockMajorant Q X Y := by
  have hXlog : 0 ≤ Real.log (X : ℝ) := Real.log_natCast_nonneg _
  have hXpow : (1 : ℝ) ≤ (1 + Real.log (X : ℝ)) ^ 3 :=
    one_le_pow₀ (by linarith)
  have hYpow : (1 : ℝ) ≤ Real.log (Y : ℝ) ^ 2 := one_le_pow₀ hYlog
  have hA : (Q : ℝ) ^ 2 ≤ 2 * (Q : ℝ) ^ 2 + 4 * (2 * Real.pi * X + 1) := by
    nlinarith [Real.pi_pos, Nat.cast_nonneg (α := ℝ) X, sq_nonneg (Q : ℝ)]
  have hB : (Q : ℝ) ^ 2 ≤ 2 * (Q : ℝ) ^ 2 + 4 * (2 * Real.pi * Y + 1) := by
    nlinarith [Real.pi_pos, Nat.cast_nonneg (α := ℝ) Y, sq_nonneg (Q : ℝ)]
  have hC : (X : ℝ) ≤ (X : ℝ) * (1 + Real.log (X : ℝ)) ^ 3 := by
    nlinarith [mul_le_mul_of_nonneg_left hXpow (Nat.cast_nonneg (α := ℝ) X)]
  have hD : (Y : ℝ) ≤ (Y : ℝ) * Real.log (Y : ℝ) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hYpow (Nat.cast_nonneg (α := ℝ) Y)]
  have hXYR : (R : ℝ) ^ 2 ≤ (X : ℝ) * Y := by exact_mod_cast hXY
  unfold typeIIBlockMajorant
  apply Real.le_sqrt_of_sq_le
  calc
    _ = ((Q : ℝ) ^ 2 * (Q : ℝ) ^ 2) * (R : ℝ) ^ 2 := by ring
    _ ≤ ((Q : ℝ) ^ 2 * (Q : ℝ) ^ 2) * ((X : ℝ) * Y) :=
      mul_le_mul_of_nonneg_left hXYR (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    _ = (((Q : ℝ) ^ 2 * (Q : ℝ) ^ 2) * X) * Y := by ring
    _ ≤ _ := mul_le_mul
      (mul_le_mul (mul_le_mul hA hB (sq_nonneg _) (by positivity)) hC
        (Nat.cast_nonneg _) (by positivity)) hD (Nat.cast_nonneg _) (by positivity)

lemma pvMajorant_ge_one {Q : ℕ} (hQ : 1 ≤ Q) : 1 ≤ pvMajorant Q := by
  have hsqrt : (1 : ℝ) ≤ Real.sqrt Q := Real.one_le_sqrt.mpr (by exact_mod_cast hQ)
  have hlog := Real.log_natCast_nonneg Q
  unfold pvMajorant
  nlinarith

/-- For dyadic square N, either a short-part term is already large, or the
central Type II block is active. This holds for every choice of cutoffs. -/
theorem vaughan_majorant_ge_central_scale (a U V Q : ℕ) (ha : 2 ≤ a) (hQ : 1 ≤ Q) :
    (Q : ℝ) ^ 2 * (2 ^ a : ℕ) ≤
      (Q : ℝ) ^ 2 * vaughanShortMajorant U V (2 ^ (2 * a)) Q +
      (6 + 2 * Real.log (((2 ^ (2 * a) : ℕ) : ℝ) + 1)) *
        ∑ j ∈ typeIILevels (2 ^ (2 * a)) U V,
          typeIIBlockMajorant Q (2 ^ (j + 1)) (2 ^ (2 * a) / 2 ^ j) := by
  let R := 2 ^ a
  let N := 2 ^ (2 * a)
  have hR : (0 : ℝ) < R := by dsimp [R]; positivity
  have hNlog : 1 ≤ Real.log (N : ℝ) := log_dyadic_ge_one (by omega)
  have hRlog : 1 ≤ Real.log (R : ℝ) := log_dyadic_ge_one ha
  have hPV := pvMajorant_ge_one hQ
  have hcoef : 1 ≤ 6 + 2 * Real.log ((N : ℝ) + 1) := by
    have hlog := Real.log_nonneg (show (1 : ℝ) ≤ (N : ℝ) + 1 by linarith [Nat.cast_nonneg (α := ℝ) N])
    linarith
  have hsum : 0 ≤ ∑ j ∈ typeIILevels N U V, typeIIBlockMajorant Q (2 ^ (j + 1)) (N / 2 ^ j) :=
    sum_nonneg (fun j _ => Real.sqrt_nonneg _)
  change (Q : ℝ) ^ 2 * R ≤ (Q : ℝ) ^ 2 * vaughanShortMajorant U V N Q +
    (6 + 2 * Real.log ((N : ℝ) + 1)) * _
  by_cases hUR : R ≤ U
  · have hURR : (R : ℝ) ≤ U := by exact_mod_cast hUR
    have hUlog : 1 ≤ Real.log (U : ℝ) := hRlog.trans (Real.log_le_log hR hURR)
    have hshort : (R : ℝ) ≤ vaughanShortMajorant U V N Q := by
      unfold vaughanShortMajorant
      have hbase : (R : ℝ) ≤ (U : ℝ) * Real.log U := by nlinarith
      have hrest : 0 ≤ ((U : ℝ) * V + 2 * V) * pvMajorant Q * Real.log N := by
        have := pvMajorant_nonneg Q
        have := Real.log_natCast_nonneg N
        positivity
      linarith
    have hmul := mul_le_mul_of_nonneg_left hshort (sq_nonneg (Q : ℝ))
    have hrest := mul_nonneg (show 0 ≤ 6 + 2 * Real.log ((N : ℝ) + 1) by linarith) hsum
    linarith
  by_cases hVR : 2 * R ≤ V
  · have hVRR : 2 * (R : ℝ) ≤ V := by exact_mod_cast hVR
    have hshort : (R : ℝ) ≤ vaughanShortMajorant U V N Q := by
      have hbase : (R : ℝ) ≤ (U : ℝ) * V + 2 * V := by
        nlinarith [Nat.cast_nonneg (α := ℝ) U, Nat.cast_nonneg (α := ℝ) V]
      have hmul := mul_le_mul hbase hPV (by norm_num : (0 : ℝ) ≤ 1) (by positivity : 0 ≤ (U : ℝ) * V + 2 * V)
      have hmul' := mul_le_mul hmul hNlog (by norm_num : (0 : ℝ) ≤ 1) (by
        have := pvMajorant_nonneg Q
        positivity : 0 ≤ ((U : ℝ) * V + 2 * V) * pvMajorant Q)
      have hfirst : 0 ≤ (U : ℝ) * Real.log U := mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)
      unfold vaughanShortMajorant
      nlinarith only [hmul', hfirst]
    have hmul := mul_le_mul_of_nonneg_left hshort (sq_nonneg (Q : ℝ))
    have hrest := mul_nonneg (show 0 ≤ 6 + 2 * Real.log ((N : ℝ) + 1) by linarith) hsum
    linarith
  · have hNR : N = R * R := by dsimp [N, R]; rw [← pow_add]; congr 1; omega
    have hlevel : a ∈ typeIILevels N U V := by
      apply mem_filter.mpr
      constructor
      · apply mem_range.mpr
        dsimp only [N]
        rw [Nat.log_pow (by decide : 1 < 2)]
        omega
      · constructor
        · change V < 2 ^ (a + 1)
          rw [pow_succ]
          change V < R * 2
          omega
        · change (U + 1) * R ≤ N
          rw [hNR]
          exact Nat.mul_le_mul_right R (by omega)
    have hdiv : N / 2 ^ a = R := by
      change N / R = R
      rw [hNR, Nat.mul_div_cancel_left R (by dsimp [R]; positivity)]
    have hblock : (Q : ℝ) ^ 2 * R ≤ typeIIBlockMajorant Q (2 ^ (a + 1)) (N / 2 ^ a) := by
      rw [hdiv]
      apply typeIIBlockMajorant_lower Q _ R R _ hRlog
      change R ^ 2 ≤ 2 ^ (a + 1) * R
      rw [pow_succ]
      change R ^ 2 ≤ R * 2 * R
      nlinarith
    have hlarge := hblock.trans (single_le_sum
      (f := fun j => typeIIBlockMajorant Q (2 ^ (j + 1)) (N / 2 ^ j))
      (fun j _ => Real.sqrt_nonneg _) hlevel)
    have hproduct : (Q : ℝ) ^ 2 * R ≤
        (6 + 2 * Real.log ((N : ℝ) + 1)) *
          ∑ j ∈ typeIILevels N U V, typeIIBlockMajorant Q (2 ^ (j + 1)) (N / 2 ^ j) := by
      have h := mul_le_mul_of_nonneg_right hcoef hsum
      nlinarith only [hlarge, h]
    have hfirst := mul_nonneg (sq_nonneg (Q : ℝ)) (vaughanShortMajorant_nonneg U V N Q)
    linarith

/-- A parameter-independent limitation of this particular upper-bound formula.
It does not give a lower bound on any actual prime-progression error. -/
theorem productVaughanMajorant_ge_dyadic_square (a U V s m : ℕ) (ha : 2 ≤ a)
    (hscale : 2 ^ a ≤ (progressionScaleN m) ^ s) :
    ((2 ^ (2 * a) : ℕ) : ℝ) ≤ productVaughanMajorant U V (2 ^ (2 * a)) s m := by
  let L := (progressionScaleN m) ^ s
  let Q := (progressionScaleN (m + 1)) ^ s
  have hL : (0 : ℝ) < L := by dsimp [L, progressionScaleN]; positivity
  have hQ : 1 ≤ Q := by
    have h : 0 < Q := by dsimp [Q, progressionScaleN]; positivity
    omega
  have hLQ : (L : ℝ) ≤ Q := by
    exact_mod_cast Nat.pow_le_pow_left (progressionScaleN_monotone (Nat.le_succ m)) s
  have hR : ((2 ^ a : ℕ) : ℝ) ≤ L := by exact_mod_cast hscale
  have hR0 : (0 : ℝ) ≤ (2 ^ a : ℕ) := Nat.cast_nonneg _
  have hQR : ((2 ^ (2 * a) : ℕ) : ℝ) * L ≤ (Q : ℝ) ^ 2 * (2 ^ a : ℕ) := by
    have hNR : ((2 ^ (2 * a) : ℕ) : ℝ) = ((2 ^ a : ℕ) : ℝ) ^ 2 := by
      rw [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul]
      congr 1
      omega
    rw [hNR]
    have hsq : ((2 ^ a : ℕ) : ℝ) * L ≤ (Q : ℝ) ^ 2 := by
      simpa only [pow_two] using
        mul_le_mul (hR.trans hLQ) hLQ hL.le (Nat.cast_nonneg (α := ℝ) Q)
    calc
      _ = (((2 ^ a : ℕ) : ℝ) * L) * (2 ^ a : ℕ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hsq hR0
  unfold productVaughanMajorant
  rw [← Nat.cast_pow]
  apply (le_div_iff₀ hL).mpr
  exact hQR.trans (vaughan_majorant_ge_central_scale a U V Q ha hQ)

lemma productVaughanMajorant_le_remainder (r m N : ℕ) (hr : 1 ≤ r)
    (U V : ℕ → ℕ) :
    productVaughanMajorant (U r) (V r) N r m ≤
      productConductorVaughanRemainder r m N U V := by
  have hsingle := single_le_sum
    (f := fun s => (((2 : ℝ) ^ 64 / ((m : ℝ) + 1)) ^ (r - s) / (r - s).factorial) *
      productVaughanMajorant (U s) (V s) N s m)
    (s := Icc 1 r)
    (fun s hs => mul_nonneg (by positivity) (productVaughanMajorant_nonneg _ _ _ _ _))
    (mem_Icc.mpr ⟨hr, le_rfl⟩)
  simp only [Nat.sub_self, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_mul] at hsingle
  have hlift : 0 ≤ (2 : ℝ) ^ (r + 1) * ((primeProductModuli r m).card : ℝ) *
      ((Nat.log 2 N : ℝ) * Real.log ((progressionScaleN (m + 1)) ^ r : ℕ)) := by
    exact mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) _) (Nat.cast_nonneg _))
      (mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _))
  unfold productConductorVaughanRemainder
  linarith only [hsingle, hlift]

/-- At all the cofinal-criterion scales with t>=4, this explicit error bound
is at least N, for every choice of cutoff functions. -/
theorem product_conductor_vaughan_remainder_ge_scale (t m : ℕ) (ht : 4 ≤ t)
    (hm : 1 ≤ m) (U V : ℕ → ℕ) :
    ((2 ^ (64 * t * m) : ℕ) : ℝ) ≤
      productConductorVaughanRemainder (t - 2) m (2 ^ (64 * t * m)) U V := by
  have ha : 2 ≤ 32 * t * m := by nlinarith
  have hscale : 2 ^ (32 * t * m) ≤ (progressionScaleN m) ^ (t - 2) := by
    unfold progressionScaleN
    rw [← pow_mul]
    apply Nat.pow_le_pow_right (by decide)
    have ht' : t ≤ 2 * (t - 2) := by omega
    nlinarith [Nat.mul_le_mul_right (32 * m) ht']
  have h := productVaughanMajorant_ge_dyadic_square (32 * t * m)
    (U (t - 2)) (V (t - 2)) (t - 2) m ha hscale
  have hexp : 2 * (32 * t * m) = 64 * t * m := by ring
  rw [hexp] at h
  exact h.trans (productVaughanMajorant_le_remainder (t - 2) m
    (2 ^ (64 * t * m)) (by omega) U V)

/-- This rules out obtaining the desired budget by making the current
majorant small. It does NOT rule out that budget for the true signed deficit. -/
theorem product_conductor_vaughan_remainder_not_small (t m : ℕ) (ht : 4 ≤ t)
    (hm : 1 ≤ m) (U V : ℕ → ℕ) :
    ¬ productConductorVaughanRemainder (t - 2) m (2 ^ (64 * t * m)) U V ≤
      ((2 ^ (64 * t * m) : ℕ) : ℝ) / ((m : ℝ) + 1) ^ t := by
  have hlarge := product_conductor_vaughan_remainder_ge_scale t m ht hm U V
  have hN : (0 : ℝ) < (2 ^ (64 * t * m) : ℕ) := by positivity
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hden : 1 < ((m : ℝ) + 1) ^ t := one_lt_pow₀ (by linarith) (by omega)
  have hsmall : (((2 ^ (64 * t * m) : ℕ) : ℝ) / ((m : ℝ) + 1) ^ t) <
      ((2 ^ (64 * t * m) : ℕ) : ℝ) := by
    exact (div_lt_self hN hden)
  intro h
  exact (hlarge.trans h).not_gt hsmall

end Erdos821
