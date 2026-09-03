import Submission.UnbalancedVaughanMajorant

/-!
# Below-square-root geometric scales for product conductors

The estimates in this file are unconditional. The factor-count range is
strictly below the square-root modulus level; no near-full-level estimate
is asserted.
-/

open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators

namespace Erdos821

open AnalyticSieve

set_option maxHeartbeats 2000000

lemma vaughanShortMajorant_mono_modulus (U V N : ℕ) {Q Q' : ℕ} (hQQ' : Q ≤ Q') :
    vaughanShortMajorant U V N Q ≤ vaughanShortMajorant U V N Q' := by
  unfold vaughanShortMajorant
  exact _root_.add_le_add le_rfl (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pvMajorant_mono hQQ') (by positivity)) (Real.log_natCast_nonneg _))

lemma product_modulus_below_sqrt (r t s m : ℕ) (hst : s ≤ r)
    (hrt : 2 * r + 1 ≤ t) (hm : 2 * r ≤ m) :
    (progressionScaleN (m + 1)) ^ s ≤ progressionScaleQ (t * m) 0 := by
  simp only [progressionScaleN, progressionScaleQ, Nat.mul_zero, Nat.sub_zero, ← pow_mul]
  apply Nat.pow_le_pow_right (by decide)
  have hst' : 2 * s + 1 ≤ t := by omega
  have hmul := Nat.mul_le_mul_right m hst'
  nlinarith

lemma unbalanced_majorant_scale_log_bound (l Q B : ℕ) :
    unbalancedTypeIIMajorant (progressionScaleN l) Q B ≤
      1000000000000 * ((l : ℝ) + 1) ^ 5 *
        ((Q : ℝ) ^ 2 * Real.sqrt (progressionScaleN l) +
          (Q : ℝ) * progressionScaleN l / B + progressionScaleN l) := by
  let a : ℝ := (l : ℝ) + 1
  have ha : 1 ≤ a := by dsimp [a]; linarith [Nat.cast_nonneg (α := ℝ) l]
  have hF : 6 + 2 * Real.log ((progressionScaleN l : ℝ) + 1) ≤ 136 * a := by
    have := log_progressionScaleN_add_one_le l
    dsimp [a]
    linarith [Nat.cast_nonneg (α := ℝ) l]
  have hJ : ((Nat.log 2 (progressionScaleN l) + 1 : ℕ) : ℝ) ≤ 65 * a := by
    simp only [progressionScaleN, Nat.log_pow (by decide : 1 < 2), Nat.cast_add,
      Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    dsimp [a]
    linarith [Nat.cast_nonneg (α := ℝ) l]
  have hH : 1 + Real.log (2 * (progressionScaleN l : ℝ) + 1) ≤ 67 * a := by
    have := log_two_progressionScaleN_add_one_le l
    dsimp [a]
    linarith [Nat.cast_nonneg (α := ℝ) l]
  have hF0 : 0 ≤ Real.log ((progressionScaleN l : ℝ) + 1) :=
    Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) (progressionScaleN l)])
  have hH0 : 0 ≤ Real.log (2 * (progressionScaleN l : ℝ) + 1) :=
    Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) (progressionScaleN l)])
  have hK : 0 ≤ (Q : ℝ) ^ 2 * Real.sqrt (progressionScaleN l) +
      (Q : ℝ) * progressionScaleN l / B + progressionScaleN l := by positivity
  unfold unbalancedTypeIIMajorant
  calc
    _ ≤ (136 * a) * (65 * a) * (288 * (67 * a) ^ 3 *
        ((Q : ℝ) ^ 2 * Real.sqrt (progressionScaleN l) +
          (Q : ℝ) * progressionScaleN l / B + progressionScaleN l)) := by gcongr
    _ ≤ _ := by
      have hnon := mul_nonneg (pow_nonneg (show 0 ≤ a by linarith) 5) hK
      change _ ≤ 1000000000000 * a ^ 5 * _
      nlinarith only [hnon]

lemma product_conductor_scale_ratios (r t s m : ℕ) (hs : 1 ≤ s) (hsr : s ≤ r)
    (hrt : 2 * r + 1 ≤ t) :
    let Q := (progressionScaleN (m + 1)) ^ s
    let N := progressionScaleN (t * m)
    let L : ℝ := (progressionScaleN m : ℝ) ^ s
    let B : ℕ := 2 ^ (3 * (t * m))
    let F : ℝ := (2 : ℝ) ^ (128 * r) * (2 : ℝ) ^ ((64 * t - 1) * m)
    (Q : ℝ) ^ 2 * Real.sqrt N / L ≤ F ∧
      (Q : ℝ) * N / B / L ≤ F ∧ (N : ℝ) / L ≤ F := by
  dsimp only
  have ht : 1 ≤ t := by omega
  have hmain : 64 * t - 1 + 1 = 64 * t := Nat.sub_add_cancel (by omega)
  have hstep : 64 * s + 32 * t ≤ 64 * t - 1 := by omega
  have hstep2 : 61 * t ≤ 64 * t - 1 := by omega
  have hstep3 : 64 * (t - s) ≤ 64 * t - 1 := by omega
  have hratio1 : (((progressionScaleN (m + 1)) ^ s : ℕ) : ℝ) ^ 2 *
      Real.sqrt (progressionScaleN (t * m)) / (progressionScaleN m : ℝ) ^ s =
        (2 : ℝ) ^ (128 * s) * (2 : ℝ) ^ ((64 * s + 32 * t) * m) := by
    rw [sqrt_progressionScaleN]
    simp only [progressionScaleN, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul, ← pow_add]
    apply (div_eq_iff (by positivity : (2 : ℝ) ^ (64 * m * s) ≠ 0)).mpr
    rw [← pow_add]
    congr 1
    ring
  have hratio2 : (((progressionScaleN (m + 1)) ^ s : ℕ) : ℝ) *
      progressionScaleN (t * m) / ((2 ^ (3 * (t * m)) : ℕ) : ℝ) /
      (progressionScaleN m : ℝ) ^ s =
        (2 : ℝ) ^ (64 * s) * (2 : ℝ) ^ (61 * t * m) := by
    simp only [progressionScaleN, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul, ← pow_add]
    rw [div_div]
    apply (div_eq_iff (by positivity : (2 : ℝ) ^ (3 * (t * m)) * (2 : ℝ) ^ (64 * m * s) ≠ 0)).mpr
    simp only [← pow_add]
    congr 1
    ring
  have hratio3 : (progressionScaleN (t * m) : ℝ) / (progressionScaleN m : ℝ) ^ s =
      (2 : ℝ) ^ (64 * (t - s) * m) := by
    simp only [progressionScaleN, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul]
    apply (div_eq_iff (by positivity : (2 : ℝ) ^ (64 * m * s) ≠ 0)).mpr
    rw [← pow_add]
    congr 1
    have hts : t - s + s = t := Nat.sub_add_cancel (by omega)
    nlinarith only [congrArg (fun z : ℕ => 64 * z * m) hts]
  rw [hratio1, hratio2, hratio3]
  refine ⟨?_, ?_, ?_⟩
  · exact mul_le_mul
      (pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left 128 hsr))
      (pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_right m hstep)) (by positivity) (by positivity)
  · exact mul_le_mul
      (pow_le_pow_right₀ (by norm_num) (by omega : 64 * s ≤ 128 * r))
      (pow_le_pow_right₀ (by norm_num) (by nlinarith [Nat.mul_le_mul_right m hstep2]))
      (by positivity) (by positivity)
  · have h := pow_le_pow_right₀ (a := (2 : ℝ)) (by norm_num) (Nat.mul_le_mul_right m hstep3)
    have hK : (1 : ℝ) ≤ (2 : ℝ) ^ (128 * r) := one_le_pow₀ (by norm_num)
    exact h.trans (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hK (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _))

def belowHalfMeanConstant (r t : ℕ) : ℕ :=
  4000000000000 * 2 ^ (128 * r) * (t + 1) ^ 5

/-- A power saving for every conductor group strictly below square root. -/
theorem product_unbalanced_below_half_bound (r t s m : ℕ) (hs : 1 ≤ s) (hsr : s ≤ r)
    (hrt : 2 * r + 1 ≤ t) (hm : 2 * r ≤ m) :
    productUnbalancedMajorant (progressionScaleU (t * m)) (progressionScaleU (t * m))
      (progressionScaleN (t * m)) (2 ^ (3 * (t * m))) s m ≤
      (belowHalfMeanConstant r t : ℝ) * ((m : ℝ) + 1) ^ 5 * (2 : ℝ) ^ ((64 * t - 1) * m) := by
  let Q := (progressionScaleN (m + 1)) ^ s
  let N := progressionScaleN (t * m)
  let U := progressionScaleU (t * m)
  let B : ℕ := 2 ^ (3 * (t * m))
  let L : ℝ := (progressionScaleN m : ℝ) ^ s
  let a : ℝ := ((t * m : ℕ) : ℝ) + 1
  let F : ℝ := (2 : ℝ) ^ (128 * r) * (2 : ℝ) ^ ((64 * t - 1) * m)
  have ha : 1 ≤ a := by dsimp [a]; linarith [Nat.cast_nonneg (α := ℝ) (t * m)]
  have hL : 0 < L := by dsimp [L, progressionScaleN]; positivity
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hrat := product_conductor_scale_ratios r t s m hs hsr hrt
  change (Q : ℝ) ^ 2 * Real.sqrt N / L ≤ F ∧
    (Q : ℝ) * N / B / L ≤ F ∧ (N : ℝ) / L ≤ F at hrat
  have hshort : vaughanShortMajorant U U N Q ≤ 6400 * a ^ 2 * Real.sqrt N := by
    calc
      _ ≤ vaughanShortMajorant U U N (progressionScaleQ (t * m) 0) :=
        vaughanShortMajorant_mono_modulus U U N (product_modulus_below_sqrt r t s m hsr hrt hm)
      _ ≤ _ := by
        dsimp only [U, N, a]
        rw [sqrt_progressionScaleN]
        exact progression_scales_short_bound (t * m) 0
  have hshortDiv : (Q : ℝ) ^ 2 * vaughanShortMajorant U U N Q / L ≤ 6400 * a ^ 2 * F := by
    calc
      _ ≤ (Q : ℝ) ^ 2 * (6400 * a ^ 2 * Real.sqrt N) / L :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hshort (sq_nonneg _)) hL.le
      _ = 6400 * a ^ 2 * ((Q : ℝ) ^ 2 * Real.sqrt N / L) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hrat.1 (by positivity)
  have hIIDiv : unbalancedTypeIIMajorant N Q B / L ≤ 3000000000000 * a ^ 5 * F := by
    calc
      _ ≤ (1000000000000 * a ^ 5 *
          ((Q : ℝ) ^ 2 * Real.sqrt N + (Q : ℝ) * N / B + N)) / L :=
        div_le_div_of_nonneg_right (unbalanced_majorant_scale_log_bound (t * m) Q B) hL.le
      _ = 1000000000000 * a ^ 5 *
          ((Q : ℝ) ^ 2 * Real.sqrt N / L + (Q : ℝ) * N / B / L + (N : ℝ) / L) := by ring
      _ ≤ 1000000000000 * a ^ 5 * (F + F + F) :=
        mul_le_mul_of_nonneg_left
          (_root_.add_le_add (_root_.add_le_add hrat.1 hrat.2.1) hrat.2.2) (by positivity)
      _ = _ := by ring
  have ha25 : a ^ 2 ≤ a ^ 5 := pow_le_pow_right₀ ha (by decide)
  have hraw : productUnbalancedMajorant U U N B s m ≤ 4000000000000 * a ^ 5 * F := by
    unfold productUnbalancedMajorant
    change ((Q : ℝ) ^ 2 * vaughanShortMajorant U U N Q + unbalancedTypeIIMajorant N Q B) / L ≤ _
    rw [add_div]
    have h := mul_le_mul_of_nonneg_right ha25 hF
    have hnon := mul_nonneg (pow_nonneg (show 0 ≤ a by linarith) 5) hF
    nlinarith only [hshortDiv, hIIDiv, h, hnon]
  apply hraw.trans
  have haUp : a ≤ ((t : ℝ) + 1) * ((m : ℝ) + 1) := by
    dsimp [a]
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) t, Nat.cast_nonneg (α := ℝ) m]
  calc
    _ ≤ 4000000000000 * (((t : ℝ) + 1) * ((m : ℝ) + 1)) ^ 5 * F := by
      gcongr
    _ = _ := by
      dsimp only [F, belowHalfMeanConstant]
      simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one, mul_pow]
      ring

theorem primitive_product_below_half_bound (r t s m : ℕ) (hs : 1 ≤ s) (hsr : s ≤ r)
    (hrt : 2 * r + 1 ≤ t) (hm : 2 * r ≤ m) :
    primitiveProductMangoldtMean s m (progressionScaleN (t * m)) ≤
      (belowHalfMeanConstant r t : ℝ) * ((m : ℝ) + 1) ^ 5 * (2 : ℝ) ^ ((64 * t - 1) * m) := by
  have hB : 1 ≤ 2 ^ (3 * (t * m)) := Nat.one_le_of_lt (by positivity)
  have hBU : (2 ^ (3 * (t * m))) ^ 2 = progressionScaleU (t * m) := by
    unfold progressionScaleU
    rw [← pow_mul]
    congr 1
    ring
  exact (primitiveProductMangoldtMean_le_unbalanced _ _ _ _ s m hs hB
    (by rw [hBU]; omega) (by rw [hBU])).trans
    (product_unbalanced_below_half_bound r t s m hs hsr hrt hm)

lemma primeProductReciprocalMass_le_two_pow (r m : ℕ) (hm : 1 ≤ m) :
    primeProductReciprocalMass r m ≤ (2 : ℝ) ^ (64 * r) := by
  have hfac : (1 : ℝ) ≤ r.factorial := by exact_mod_cast Nat.factorial_pos r
  have hz : (1 : ℝ) ≤ (m : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) m]
  calc
    _ ≤ ((2 : ℝ) ^ 64 / ((m : ℝ) + 1)) ^ r / r.factorial := primeProductReciprocalMass_upper r m hm
    _ ≤ ((2 : ℝ) ^ 64 / ((m : ℝ) + 1)) ^ r := div_le_self (by positivity) hfac
    _ ≤ ((2 : ℝ) ^ 64) ^ r :=
      pow_le_pow_left₀ (by positivity) (div_le_self (by positivity) hz) r
    _ = _ := by rw [← pow_mul]

lemma primeProductModuli_card_le_upper (r m : ℕ) :
    (primeProductModuli r m).card ≤ (progressionScaleN (m + 1)) ^ r := by
  have hsub : primeProductModuli r m ⊆ Icc 1 ((progressionScaleN (m + 1)) ^ r) := by
    intro d hd
    have h := primeProductModuli_properties hd
    exact mem_Icc.mpr ⟨h.1, h.2.2.2.2⟩
  exact (card_le_card hsub).trans_eq (by simp)

def belowHalfLiftConstant (r t : ℕ) : ℕ :=
  2 ^ (r + 1) * 2 ^ (64 * r) * 4096 * r * t

lemma product_lift_below_half_bound (r t m : ℕ) (hrt : 2 * r + 1 ≤ t) :
    (∑ d ∈ primeProductModuli r m,
      (((d : ℝ) + 1) * characterLiftError d (progressionScaleN (t * m))) / d.totient) ≤
      (belowHalfLiftConstant r t : ℝ) * ((m : ℝ) + 1) ^ 5 * (2 : ℝ) ^ ((64 * t - 1) * m) := by
  let N := progressionScaleN (t * m)
  let Q := (progressionScaleN (m + 1)) ^ r
  let z : ℝ := (m : ℝ) + 1
  have hz : 1 ≤ z := by dsimp [z]; linarith [Nat.cast_nonneg (α := ℝ) m]
  have hcard : ((primeProductModuli r m).card : ℝ) ≤ Q := by
    exact_mod_cast primeProductModuli_card_le_upper r m
  have hlogN : (Nat.log 2 N : ℝ) ≤ 64 * (t : ℝ) * z := by
    dsimp [N, progressionScaleN, z]
    rw [Nat.log_pow (by decide : 1 < 2)]
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) t]
  have hlogQ : Real.log (Q : ℝ) ≤ 64 * (r : ℝ) * z := by
    have h := log_two_pow_le (64 * (m + 1) * r)
    have hQ : Q = 2 ^ (64 * (m + 1) * r) := by dsimp [Q, progressionScaleN]; rw [← pow_mul]
    rw [hQ]
    dsimp only [z]
    convert h using 1; push_cast; ring
  have hQeq : (Q : ℝ) = (2 : ℝ) ^ (64 * r) * (2 : ℝ) ^ (64 * r * m) := by
    dsimp [Q, progressionScaleN]
    simp only [Nat.cast_pow, Nat.cast_ofNat, ← pow_mul, ← pow_add]
    congr 1
    ring
  have hpow : (2 : ℝ) ^ (64 * r * m) ≤ (2 : ℝ) ^ ((64 * t - 1) * m) :=
    pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_right m (by omega : 64 * r ≤ 64 * t - 1))
  apply (prime_product_lift_remainder_le r m N).trans
  calc
    _ ≤ (2 : ℝ) ^ (r + 1) * Q * ((64 * (t : ℝ) * z) * (64 * (r : ℝ) * z)) := by
      have hlogQ0 : 0 ≤ Real.log (Q : ℝ) := Real.log_natCast_nonneg Q
      have hlogN0 : (0 : ℝ) ≤ Nat.log 2 N := Nat.cast_nonneg _
      have hQ0 : (0 : ℝ) ≤ Q := Nat.cast_nonneg _
      have hp0 : (0 : ℝ) ≤ (2 : ℝ) ^ (r + 1) := pow_nonneg (by norm_num) _
      have ht0 : (0 : ℝ) ≤ 64 * (t : ℝ) * z := by positivity
      exact mul_le_mul (mul_le_mul_of_nonneg_left hcard hp0)
        (mul_le_mul hlogN hlogQ hlogQ0 ht0)
        (mul_nonneg hlogN0 hlogQ0) (mul_nonneg hp0 hQ0)
    _ = (belowHalfLiftConstant r t : ℝ) * z ^ 2 * (2 : ℝ) ^ (64 * r * m) := by
      rw [hQeq]
      simp only [belowHalfLiftConstant, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      ring
    _ ≤ _ := by
      change _ ≤ (belowHalfLiftConstant r t : ℝ) * z ^ 5 * (2 : ℝ) ^ ((64 * t - 1) * m)
      exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hz (by decide : 2 ≤ 5))
        (Nat.cast_nonneg _)) hpow (by positivity) (by positivity)

def belowHalfCompositeConstant (r t : ℕ) : ℕ :=
  r * 2 ^ (64 * r) * belowHalfMeanConstant r t + belowHalfLiftConstant r t

/-- An explicit power-saving composite-modulus discrepancy estimate in the
strictly below-square-root range. -/
theorem composite_below_half_error_bound (r t m : ℕ) (hrt : 2 * r + 1 ≤ t)
    (hm : max 1 (2 * r) ≤ m) :
    (∑ d ∈ primeProductModuli r m, compositeProgressionError d (progressionScaleN (t * m))) ≤
      (belowHalfCompositeConstant r t : ℝ) * ((m : ℝ) + 1) ^ 5 * (2 : ℝ) ^ ((64 * t - 1) * m) := by
  let N := progressionScaleN (t * m)
  let F : ℝ := ((m : ℝ) + 1) ^ 5 * (2 : ℝ) ^ ((64 * t - 1) * m)
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hconductor : (∑ d ∈ primeProductModuli r m, primitiveConductorMangoldtMajorant d N / d.totient) ≤
      (r : ℝ) * (2 : ℝ) ^ (64 * r) * belowHalfMeanConstant r t * F := by
    apply (prime_product_conductor_majorant_le r m N).trans
    calc
      _ ≤ ∑ _s ∈ Icc 1 r, (2 : ℝ) ^ (64 * r) * ((belowHalfMeanConstant r t : ℝ) * F) := by
        apply sum_le_sum
        intro s hs
        have hW : primeProductReciprocalMass (r - s) m ≤ (2 : ℝ) ^ (64 * r) :=
          (primeProductReciprocalMass_le_two_pow (r - s) m (by omega)).trans
            (pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left 64 (Nat.sub_le r s)))
        have hM : primitiveProductMangoldtMean s m N ≤ (belowHalfMeanConstant r t : ℝ) * F := by
          simpa only [F, mul_assoc] using
            primitive_product_below_half_bound r t s m (mem_Icc.mp hs).1 (mem_Icc.mp hs).2 hrt (by omega)
        exact mul_le_mul hW hM (primitiveProductMangoldtMean_nonneg s m N) (by positivity)
      _ = _ := by simp only [sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel]; ring
  have hlift := product_lift_below_half_bound r t m hrt
  have hsplit : (∑ d ∈ primeProductModuli r m, compositeProgressionError d N) =
      (∑ d ∈ primeProductModuli r m, primitiveConductorMangoldtMajorant d N / d.totient) +
      (∑ d ∈ primeProductModuli r m, (((d : ℝ) + 1) * characterLiftError d N) / d.totient) := by
    simp only [compositeProgressionError, add_div, sum_add_distrib]
  change _ ≤ _ * ((m : ℝ) + 1) ^ 5 * _ at hlift
  change _ ≤ (belowHalfCompositeConstant r t : ℝ) * ((m : ℝ) + 1) ^ 5 * _
  rw [hsplit]
  have h := _root_.add_le_add hconductor hlift
  dsimp only [F, N] at h
  simp only [belowHalfCompositeConstant, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  nlinarith only [h]

/-- Every fixed inverse-logarithmic error budget holds eventually in the
below-square-root product-modulus range. -/
theorem eventually_composite_below_half_error (r t A : ℕ) (hrt : 2 * r + 1 ≤ t) :
    ∀ᶠ m : ℕ in atTop,
      (∑ d ∈ primeProductModuli r m, compositeProgressionError d (progressionScaleN (t * m))) ≤
        (progressionScaleN (t * m) : ℝ) / ((m : ℝ) + 1) ^ A := by
  filter_upwards [eventually_nat_poly_le_two_pow 1 (belowHalfCompositeConstant r t) (5 + A),
    eventually_ge_atTop (max 1 (2 * r))] with m hpoly hm
  have hpoly' : (belowHalfCompositeConstant r t : ℝ) * ((m : ℝ) + 1) ^ (5 + A) ≤ (2 : ℝ) ^ m := by
    simpa only [one_mul, Nat.cast_add, Nat.cast_one] using (show (belowHalfCompositeConstant r t : ℝ) *
      ((1 * m : ℕ) + 1 : ℕ) ^ (5 + A) ≤ (2 : ℝ) ^ m from by exact_mod_cast hpoly)
  apply (composite_below_half_error_bound r t m hrt hm).trans
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < ((m : ℝ) + 1) ^ A)).mpr
  calc
    _ = ((belowHalfCompositeConstant r t : ℝ) * ((m : ℝ) + 1) ^ (5 + A)) *
        (2 : ℝ) ^ ((64 * t - 1) * m) := by rw [pow_add]; ring
    _ ≤ (2 : ℝ) ^ m * (2 : ℝ) ^ ((64 * t - 1) * m) :=
      mul_le_mul_of_nonneg_right hpoly' (by positivity)
    _ = _ := by
      simp only [progressionScaleN, Nat.cast_pow, Nat.cast_ofNat, ← pow_add]
      congr 1
      have h : 64 * t - 1 + 1 = 64 * t := Nat.sub_add_cancel (by omega)
      nlinarith only [congrArg (fun z : ℕ => z * m) h]

theorem eventually_product_mangoldt_discrepancy (r t A : ℕ) (hrt : 2 * r + 1 ≤ t) :
    ∀ᶠ m : ℕ in atTop,
      (∑ d ∈ primeProductModuli r m,
        |residueOneMangoldt d (progressionScaleN (t * m)) -
          mangoldtSum (progressionScaleN (t * m)) / d.totient|) ≤
        (progressionScaleN (t * m) : ℝ) / ((m : ℝ) + 1) ^ A := by
  filter_upwards [eventually_composite_below_half_error r t A hrt] with m hm
  apply le_trans _ hm
  exact sum_le_sum (fun d hd => composite_progression_discrepancy d _
    (primeProductModuli_properties hd).1)

theorem eventually_product_mangoldt_total_lower (r t A : ℕ) (hrt : 2 * r + 1 ≤ t) :
    ∀ᶠ m : ℕ in atTop,
      mangoldtSum (progressionScaleN (t * m)) * primeProductReciprocalMass r m -
        (progressionScaleN (t * m) : ℝ) / ((m : ℝ) + 1) ^ A ≤
          ∑ d ∈ primeProductModuli r m, residueOneMangoldt d (progressionScaleN (t * m)) := by
  filter_upwards [eventually_composite_below_half_error r t A hrt] with m hm
  have h := composite_progression_total_lower (primeProductModuli r m)
    (fun d hd => (primeProductModuli_properties hd).1) (progressionScaleN (t * m))
  change mangoldtSum (progressionScaleN (t * m)) * primeProductReciprocalMass r m - _ ≤ _ at h
  linarith only [h, hm]

end Erdos821
