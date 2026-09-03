import Submission.PrimeProgressions

/-!
# Power-saving parameters for prime-modulus progression sums

We use N=2^(64s), U=V=2^(6s), Q=2^(32s-2L), D=2^(32s-3L).
For 1<=L<=s the progression error is bounded by a polynomial in s times
2^(64s-L). The interval [D,Q] is wide enough that an elementary lower
prime-count bound suffices to populate it.
-/

open scoped BigOperators
open Finset ArithmeticFunction

namespace Erdos821.AnalyticSieve

def progressionScaleN (s : ℕ) : ℕ := 2 ^ (64 * s)
def progressionScaleU (s : ℕ) : ℕ := 2 ^ (6 * s)
def progressionScaleQ (s L : ℕ) : ℕ := 2 ^ (32 * s - 2 * L)
def progressionScaleD (s L : ℕ) : ℕ := 2 ^ (32 * s - 3 * L)

lemma log_two_pow_le (k : ℕ) : Real.log ((2 ^ k : ℕ) : ℝ) ≤ k := by
  have h2 : Real.log 2 ≤ 1 := by
    simpa only [show (2 : ℝ) - 1 = 1 by norm_num] using Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg (α := ℝ) k)

lemma sqrt_progressionScaleN (s : ℕ) : Real.sqrt (progressionScaleN s) = (2 : ℝ) ^ (32 * s) := by
  have heq : (progressionScaleN s : ℝ) = ((2 : ℝ) ^ (32 * s)) ^ 2 := by
    simp only [progressionScaleN, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul]
    congr 1
    omega
  rw [heq, Real.sqrt_sq (by positivity)]

lemma sqrt_progressionScaleQ_le (s L : ℕ) : Real.sqrt (progressionScaleQ s L) ≤ (2 : ℝ) ^ (16 * s) := by
  have heq : ((2 : ℝ) ^ (16 * s)) ^ 2 = (2 : ℝ) ^ (32 * s) := by
    rw [← pow_mul]
    congr 1
    omega
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · rw [heq]
    simp only [progressionScaleQ, Nat.cast_pow, Nat.cast_ofNat]
    exact pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)

lemma log_progressionScaleQ_le (s L : ℕ) : Real.log (progressionScaleQ s L) ≤ 32 * (s : ℝ) := by
  have h := log_two_pow_le (32 * s - 2 * L)
  apply h.trans
  exact_mod_cast (show 32 * s - 2 * L ≤ 32 * s from Nat.sub_le _ _)

lemma log_progressionScaleN_add_one_le (s : ℕ) :
    Real.log ((progressionScaleN s : ℝ) + 1) ≤ 64 * (s : ℝ) + 1 := by
  have hN : (1 : ℝ) ≤ (2 : ℝ) ^ (64 * s) := one_le_pow₀ (by norm_num)
  calc
    _ ≤ Real.log ((2 ^ (64 * s + 1) : ℕ) : ℝ) := by
      apply Real.log_le_log (by positivity)
      simp only [progressionScaleN, Nat.cast_pow, Nat.cast_ofNat, pow_succ, Nat.cast_mul]
      linarith
    _ ≤ _ := by simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using log_two_pow_le (64 * s + 1)

lemma log_two_progressionScaleN_add_one_le (s : ℕ) :
    Real.log (2 * (progressionScaleN s : ℝ) + 1) ≤ 64 * (s : ℝ) + 2 := by
  have hN : (1 : ℝ) ≤ (2 : ℝ) ^ (64 * s) := one_le_pow₀ (by norm_num)
  calc
    _ ≤ Real.log ((2 ^ (64 * s + 2) : ℕ) : ℝ) := by
      apply Real.log_le_log (by positivity)
      simp only [progressionScaleN, Nat.cast_pow, Nat.cast_ofNat, pow_add]
      norm_num
      linarith
    _ ≤ _ := by simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using log_two_pow_le (64 * s + 2)

lemma progression_scales_balanced {s L : ℕ} (hL : 1 ≤ L) (hLs : L ≤ s) :
    2 * progressionScaleN s ≤ progressionScaleU s * (progressionScaleQ s L) ^ 2 := by
  simp only [progressionScaleN, progressionScaleU, progressionScaleQ, ← pow_mul, ← pow_add]
  rw [show 2 * 2 ^ (64 * s) = 2 ^ (64 * s + 1) by rw [pow_succ]; ring]
  apply Nat.pow_le_pow_right (by norm_num)
  omega

lemma progression_scales_mean_ratio {s L : ℕ} (hLs : L ≤ s) :
    (progressionScaleQ s L : ℝ) ^ 2 * (2 : ℝ) ^ (32 * s) / progressionScaleD s L =
      (2 : ℝ) ^ (64 * s - L) := by
  simp only [progressionScaleQ, progressionScaleD, Nat.cast_pow, Nat.cast_ofNat,
    ← pow_mul, ← pow_add, div_eq_mul_inv]
  rw [← pow_sub₀ (2 : ℝ) (by norm_num) (by omega)]
  congr 1
  omega

lemma progression_scales_omission_ratio {s L : ℕ} (hLs : L ≤ s) :
    (progressionScaleQ s L : ℝ) * progressionScaleN s / (progressionScaleD s L : ℝ) ^ 2 ≤
      (2 : ℝ) ^ (64 * s - L) := by
  simp only [progressionScaleQ, progressionScaleD, progressionScaleN, Nat.cast_pow, Nat.cast_ofNat,
    ← pow_mul, ← pow_add, div_eq_mul_inv]
  rw [← pow_sub₀ (2 : ℝ) (by norm_num) (by omega)]
  apply pow_le_pow_right₀ (by norm_num)
  omega

lemma progression_scales_short_bound (s L : ℕ) :
    vaughanShortMajorant (progressionScaleU s) (progressionScaleU s)
        (progressionScaleN s) (progressionScaleQ s L) ≤
      6400 * ((s : ℝ) + 1) ^ 2 * (2 : ℝ) ^ (32 * s) := by
  let u : ℝ := progressionScaleU s
  let t : ℝ := (2 : ℝ) ^ (32 * s)
  let r : ℝ := (2 : ℝ) ^ (16 * s)
  let a : ℝ := (s : ℝ) + 1
  have ha : 1 ≤ a := by dsimp [a]; linarith [Nat.cast_nonneg (α := ℝ) s]
  have hu : 1 ≤ u := by dsimp [u, progressionScaleU]; push_cast; exact one_le_pow₀ (by norm_num)
  have hu0 : 0 ≤ u := by positivity
  have ht0 : 0 ≤ t := by positivity
  have hr0 : 0 ≤ r := by positivity
  have hut : u ≤ t := by
    dsimp [u, t, progressionScaleU]
    push_cast
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hprod : u ^ 2 * r ≤ t := by
    dsimp [u, t, r, progressionScaleU]
    push_cast
    rw [← pow_mul, ← pow_add]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hlu : Real.log (progressionScaleU s) ≤ 6 * a ^ 2 := by
    have h := log_two_pow_le (6 * s)
    simp only [Nat.cast_mul, Nat.cast_ofNat] at h
    change Real.log (progressionScaleU s) ≤ 6 * (s : ℝ) at h
    dsimp [a]
    nlinarith [Nat.cast_nonneg (α := ℝ) s]
  have hln : Real.log (progressionScaleN s) ≤ 64 * a := by
    have h := log_two_pow_le (64 * s)
    simp only [Nat.cast_mul, Nat.cast_ofNat] at h
    change Real.log (progressionScaleN s) ≤ 64 * (s : ℝ) at h
    dsimp [a]
    linarith
  have hbq : pvMajorant (progressionScaleQ s L) ≤ 33 * a * r := by
    unfold pvMajorant
    calc
      _ ≤ r * (1 + 32 * (s : ℝ)) := mul_le_mul (sqrt_progressionScaleQ_le s L)
        (add_le_add le_rfl (log_progressionScaleQ_le s L))
        (by linarith [Real.log_natCast_nonneg (progressionScaleQ s L)]) hr0
      _ ≤ _ := by dsimp [a]; nlinarith [Nat.cast_nonneg (α := ℝ) s]
  have hfirst : u * Real.log (progressionScaleU s) ≤ 6 * a ^ 2 * t := by
    have h := mul_le_mul hut hlu (Real.log_natCast_nonneg _) ht0
    convert h using 1; ring
  have hco : u * u + 2 * u ≤ 3 * u ^ 2 := by nlinarith
  have hsecond : (u * u + 2 * u) * pvMajorant (progressionScaleQ s L) * Real.log (progressionScaleN s) ≤
      6336 * a ^ 2 * t := by
    calc
      _ ≤ (3 * u ^ 2) * (33 * a * r) * (64 * a) := mul_le_mul
        (mul_le_mul hco hbq (pvMajorant_nonneg _) (by positivity)) hln
        (Real.log_natCast_nonneg _) (by positivity)
      _ = 6336 * a ^ 2 * (u ^ 2 * r) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hprod (by positivity)
  change u * Real.log (progressionScaleU s) +
    (u * u + 2 * u) * pvMajorant (progressionScaleQ s L) * Real.log (progressionScaleN s) ≤ 6400 * a ^ 2 * t
  nlinarith [mul_nonneg (sq_nonneg a) ht0]

lemma progression_scales_balanced_bound {s L : ℕ} (hLs : L ≤ s) :
    balancedTypeIIMajorant (progressionScaleN s) (progressionScaleQ s L) / progressionScaleD s L ≤
      340319349760 * ((s : ℝ) + 1) ^ 5 * (2 : ℝ) ^ (64 * s - L) := by
  let a : ℝ := (s : ℝ) + 1
  have ha : 1 ≤ a := by dsimp [a]; linarith [Nat.cast_nonneg (α := ℝ) s]
  have hF : 6 + 2 * Real.log ((progressionScaleN s : ℝ) + 1) ≤ 136 * a := by
    have := log_progressionScaleN_add_one_le s
    dsimp [a]
    linarith [Nat.cast_nonneg (α := ℝ) s]
  have hJ : ((Nat.log 2 (progressionScaleN s) + 1 : ℕ) : ℝ) ≤ 65 * a := by
    simp only [progressionScaleN, Nat.log_pow (by norm_num : 1 < 2), Nat.cast_add,
      Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    dsimp [a]
    linarith [Nat.cast_nonneg (α := ℝ) s]
  have hH : 1 + Real.log (2 * (progressionScaleN s : ℝ) + 1) ≤ 67 * a := by
    have := log_two_progressionScaleN_add_one_le s
    dsimp [a]
    linarith [Nat.cast_nonneg (α := ℝ) s]
  have hF0 : 0 ≤ Real.log ((progressionScaleN s : ℝ) + 1) :=
    Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) (progressionScaleN s)])
  have hH0 : 0 ≤ Real.log (2 * (progressionScaleN s : ℝ) + 1) :=
    Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) (progressionScaleN s)])
  calc
    _ = (6 + 2 * Real.log ((progressionScaleN s : ℝ) + 1)) *
        ((Nat.log 2 (progressionScaleN s) + 1 : ℕ) : ℝ) * 128 *
        ((progressionScaleQ s L : ℝ) ^ 2 * Real.sqrt (progressionScaleN s) / progressionScaleD s L) *
        (1 + Real.log (2 * (progressionScaleN s : ℝ) + 1)) ^ 3 := by
      unfold balancedTypeIIMajorant
      ring
    _ = (6 + 2 * Real.log ((progressionScaleN s : ℝ) + 1)) *
        ((Nat.log 2 (progressionScaleN s) + 1 : ℕ) : ℝ) * 128 *
        (2 : ℝ) ^ (64 * s - L) * (1 + Real.log (2 * (progressionScaleN s : ℝ) + 1)) ^ 3 := by
      rw [sqrt_progressionScaleN, progression_scales_mean_ratio hLs]
    _ ≤ (136 * a) * (65 * a) * 128 * (2 : ℝ) ^ (64 * s - L) * (67 * a) ^ 3 := by
      gcongr
    _ = _ := by dsimp [a]; ring

lemma progression_scales_short_div_bound {s L : ℕ} (hLs : L ≤ s) :
    ((progressionScaleQ s L : ℝ) ^ 2 * vaughanShortMajorant (progressionScaleU s) (progressionScaleU s)
      (progressionScaleN s) (progressionScaleQ s L)) / progressionScaleD s L ≤
      6400 * ((s : ℝ) + 1) ^ 2 * (2 : ℝ) ^ (64 * s - L) := by
  calc
    _ ≤ ((progressionScaleQ s L : ℝ) ^ 2 * (6400 * ((s : ℝ) + 1) ^ 2 * (2 : ℝ) ^ (32 * s))) /
        progressionScaleD s L := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (progression_scales_short_bound s L) (sq_nonneg _)) (Nat.cast_nonneg _)
    _ = 6400 * ((s : ℝ) + 1) ^ 2 *
        ((progressionScaleQ s L : ℝ) ^ 2 * (2 : ℝ) ^ (32 * s) / progressionScaleD s L) := by ring
    _ = _ := by rw [progression_scales_mean_ratio hLs]

lemma progression_scales_omission_bound {s L : ℕ} (hLs : L ≤ s) :
    2 * (progressionScaleQ s L : ℝ) * progressionScaleN s / (progressionScaleD s L : ℝ) ^ 2 *
      Real.log (progressionScaleN s) ≤ 128 * ((s : ℝ) + 1) * (2 : ℝ) ^ (64 * s - L) := by
  have hlog : Real.log (progressionScaleN s) ≤ 64 * ((s : ℝ) + 1) := by
    have h := log_two_pow_le (64 * s)
    simp only [Nat.cast_mul, Nat.cast_ofNat] at h
    change Real.log (progressionScaleN s) ≤ 64 * (s : ℝ) at h
    linarith
  calc
    _ = 2 * ((progressionScaleQ s L : ℝ) * progressionScaleN s / (progressionScaleD s L : ℝ) ^ 2) *
        Real.log (progressionScaleN s) := by ring
    _ ≤ 2 * ((2 : ℝ) ^ (64 * s - L)) * (64 * ((s : ℝ) + 1)) := mul_le_mul
      (mul_le_mul_of_nonneg_left (progression_scales_omission_ratio hLs) (by norm_num))
      hlog (Real.log_natCast_nonneg _) (by positivity)
    _ = _ := by ring

/-- A concrete power-saving error bound. Along s=rL for each fixed r>=1,
its ratio to N decays exponentially, even after any fixed polynomial loss. -/
theorem progression_scales_error_bound {s L : ℕ} (hLs : L ≤ s) :
    primeProgressionError (progressionScaleU s) (progressionScaleU s)
        (progressionScaleN s) (progressionScaleQ s L) (progressionScaleD s L) ≤
      1000000000000 * ((s : ℝ) + 1) ^ 5 * (2 : ℝ) ^ (64 * s - L) := by
  let a : ℝ := (s : ℝ) + 1
  let p : ℝ := (2 : ℝ) ^ (64 * s - L)
  have ha : 1 ≤ a := by dsimp [a]; linarith [Nat.cast_nonneg (α := ℝ) s]
  have hp : 0 ≤ p := by positivity
  have h2 : a ^ 2 ≤ a ^ 5 := pow_le_pow_right₀ ha (by norm_num)
  have h1 : a ≤ a ^ 5 := by simpa only [pow_one] using pow_le_pow_right₀ ha (show 1 ≤ 5 by norm_num)
  unfold primeProgressionError
  rw [add_div]
  calc
    _ ≤ 6400 * a ^ 2 * p + 340319349760 * a ^ 5 * p + 128 * a * p :=
      add_le_add (add_le_add (progression_scales_short_div_bound hLs)
        (progression_scales_balanced_bound hLs)) (progression_scales_omission_bound hLs)
    _ ≤ 6400 * a ^ 5 * p + 340319349760 * a ^ 5 * p + 128 * a ^ 5 * p := by
      gcongr
    _ ≤ 1000000000000 * a ^ 5 * p := by
      have := mul_nonneg (pow_nonneg (by linarith : 0 ≤ a) 5) hp
      nlinarith

lemma progression_scales_error_div_bound {s L : ℕ} (hLs : L ≤ s) :
    primeProgressionError (progressionScaleU s) (progressionScaleU s)
        (progressionScaleN s) (progressionScaleQ s L) (progressionScaleD s L) /
        progressionScaleN s ≤ 1000000000000 * ((s : ℝ) + 1) ^ 5 / (2 : ℝ) ^ L := by
  have hn : (0 : ℝ) < progressionScaleN s := by unfold progressionScaleN; positivity
  apply (div_le_div_of_nonneg_right (progression_scales_error_bound hLs) hn.le).trans_eq
  rw [pow_sub₀ (2 : ℝ) (by norm_num) (show L ≤ 64 * s by omega)]
  simp only [progressionScaleN, Nat.cast_pow, Nat.cast_ofNat]
  field_simp

lemma eventually_nat_poly_le_two_pow (r C k : ℕ) :
    ∀ᶠ L : ℕ in Filter.atTop, C * (r * L + 1) ^ k ≤ 2 ^ L := by
  have ht := (tendsto_pow_const_div_const_pow_of_one_lt k (by norm_num : (1 : ℝ) < 2)).const_mul
    ((C : ℝ) * ((r : ℝ) + 1) ^ k)
  simp only [mul_zero] at ht
  have he : ∀ᶠ L : ℕ in Filter.atTop,
      (C : ℝ) * ((r : ℝ) + 1) ^ k * ((L : ℝ) ^ k / (2 : ℝ) ^ L) < 1 :=
    ht.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [he, Filter.eventually_ge_atTop 1] with L hL hL1
  have hL1' : (1 : ℝ) ≤ L := by exact_mod_cast hL1
  have hpoly : ((r * L + 1 : ℕ) : ℝ) ≤ ((r : ℝ) + 1) * L := by push_cast; nlinarith
  have hbound : (C : ℝ) * ((r * L + 1 : ℕ) : ℝ) ^ k ≤ (2 : ℝ) ^ L := by
    calc
      _ ≤ (C : ℝ) * (((r : ℝ) + 1) * L) ^ k :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hpoly k) (Nat.cast_nonneg C)
      _ ≤ _ := by
        rw [mul_pow]
        have hh : ((C : ℝ) * ((r : ℝ) + 1) ^ k * (L : ℝ) ^ k) / (2 : ℝ) ^ L < 1 := by
          simpa only [mul_div_assoc] using hL
        have h := (div_lt_one (by positivity : (0 : ℝ) < (2 : ℝ) ^ L)).mp hh
        simpa only [mul_assoc] using h.le
  exact_mod_cast hbound

end Erdos821.AnalyticSieve
