import Submission.Rankin

/-!
# A uniform limitation of the explicit Rankin majorant

This bounds the majorant from BELOW, not inverse-totient multiplicity from
below. It rules out extracting a fixed power saving by optimizing that
particular upper-bound expression. It does not settle Erdős 821.
-/

open Nat Filter
open scoped Classical

namespace Erdos821.RankinEnvelope

lemma smooth_constant_ge_one (s u : ℝ) (hs : 0 < s) (hu : 1 < u) :
    1 ≤ smoothRankinConstant s u := by
  have hr : (2 : ℝ) ^ (-s) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hden : 0 < 1 - (2 : ℝ) ^ (-s) := by linarith
  have hfactor : 1 ≤ (1 - (2 : ℝ) ^ (-s))⁻¹ :=
    (one_le_inv₀ hden).mpr (by have := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-s); linarith)
  have H : Summable (fun a : ℕ => (a : ℝ) ^ (-u)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hsum : 1 ≤ ∑' a : ℕ, (a : ℝ) ^ (-u) := by
    simpa using H.le_tsum 1 (fun a _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  exact one_le_mul_of_one_le_of_one_le hfactor hsum

/-- Abstract lower bound for the whole envelope. The parameters A, y, s,
and u are allowed to vary with n. -/
lemma envelope_ge_power (n A y C D s u δ : ℝ)
    (hn : 1 ≤ n) (hA : 1 ≤ A) (hy : 1 ≤ y) (hC : 1 ≤ C) (hD : 1 ≤ D)
    (hs : 0 < s) (hu : 1 < u) (hδ : 0 < δ)
    (hlog : Real.log n ≤ n ^ (2 * δ ^ 2)) :
    n ^ (1 - δ) ≤ (C / A + 3 * A / y) * n +
      (A * n) ^ s * Real.exp (D * y ^ (u - s)) := by
  let B := (C / A + 3 * A / y) * n + (A * n) ^ s * Real.exp (D * y ^ (u - s))
  let a := n ^ δ
  let b := n ^ (1 - δ)
  have hn0 : 0 < n := by linarith
  have hA0 : 0 < A := by linarith
  have hy0 : 0 < y := by linarith
  have hC0 : 0 ≤ C := by linarith
  have hD0 : 0 ≤ D := by linarith
  have ha0 : 0 < a := Real.rpow_pos_of_pos hn0 _
  have hb0 : 0 < b := Real.rpow_pos_of_pos hn0 _
  have hab : a * b = n := by
    dsimp [a, b]
    rw [← Real.rpow_add hn0, add_sub_cancel, Real.rpow_one]
  have hterm0 : 0 ≤ (A * n) ^ s * Real.exp (D * y ^ (u - s)) := by positivity
  have hlin0 : 0 ≤ (C / A + 3 * A / y) * n := by positivity
  have hfirst : n / A ≤ B := by
    calc
      _ = (1 / A + 0) * n := by ring
      _ ≤ (C / A + 3 * A / y) * n :=
        mul_le_mul_of_nonneg_right
          (_root_.add_le_add (div_le_div_of_nonneg_right hC hA0.le) (by positivity)) hn0.le
      _ ≤ B := le_add_of_nonneg_right hterm0
  have hsecond : A * n / y ≤ B := by
    calc
      _ = (0 + A / y) * n := by ring
      _ ≤ (C / A + 3 * A / y) * n := by
        apply mul_le_mul_of_nonneg_right _ hn0.le
        have hh : 0 ≤ A / y := by positivity
        have hc : 0 ≤ C / A := by positivity
        rw [mul_div_assoc]
        nlinarith
      _ ≤ B := le_add_of_nonneg_right hterm0
  have hthird : (A * n) ^ s * Real.exp (D * y ^ (u - s)) ≤ B :=
    le_add_of_nonneg_left hlin0
  have hexp1 : 1 ≤ Real.exp (D * y ^ (u - s)) := Real.one_le_exp (by positivity)
  by_contra h
  have hB : B < b := lt_of_not_ge h
  have hnA : n < b * A := (div_lt_iff₀ hA0).mp (hfirst.trans_lt hB)
  have haA : a < A := (mul_lt_mul_iff_right₀ hb0).mp (by nlinarith only [hab, hnA])
  have hnY : A * n < b * y := (div_lt_iff₀ hy0).mp (hsecond.trans_lt hB)
  have hAaY : A * a < y := by
    apply (mul_lt_mul_iff_right₀ hb0).mp
    calc
      b * (A * a) = A * n := by rw [← hab]; ring
      _ < b * y := hnY
  have hay : a ^ 2 ≤ y := by
    calc
      a ^ 2 = a * a := pow_two a
      _ ≤ A * a := mul_le_mul_of_nonneg_right haA.le ha0.le
      _ ≤ y := hAaY.le
  by_cases hsb : 1 - δ ≤ s
  · have hbB : b ≤ B := by
      calc
        b ≤ n ^ s := Real.rpow_le_rpow_of_exponent_le hn hsb
        _ ≤ (A * n) ^ s := Real.rpow_le_rpow hn0.le
          (by nlinarith only [hA, hn0]) hs.le
        _ ≤ (A * n) ^ s * Real.exp (D * y ^ (u - s)) :=
          le_mul_of_one_le_right (by positivity) hexp1
        _ ≤ B := hthird
    exact (not_lt_of_ge hbB) hB
  have hδus : δ ≤ u - s := by linarith [lt_of_not_ge hsb]
  have hpow : n ^ (2 * δ ^ 2) ≤ D * y ^ (u - s) := by
    calc
      _ = (a ^ 2) ^ δ := by
        dsimp [a]
        rw [← Real.rpow_mul_natCast hn0.le, ← Real.rpow_mul hn0.le]
        congr 1
        push_cast
        ring
      _ ≤ y ^ δ := Real.rpow_le_rpow (sq_nonneg a) hay hδ.le
      _ ≤ y ^ (u - s) := Real.rpow_le_rpow_of_exponent_le hy hδus
      _ ≤ D * y ^ (u - s) := le_mul_of_one_le_left (by positivity) hD
  have hBn : n ≤ B := by
    calc
      n = Real.exp (Real.log n) := (Real.exp_log hn0).symm
      _ ≤ Real.exp (D * y ^ (u - s)) := Real.exp_le_exp.mpr (hlog.trans hpow)
      _ ≤ (A * n) ^ s * Real.exp (D * y ^ (u - s)) :=
        le_mul_of_one_le_left (Real.exp_pos _).le
          (Real.one_le_rpow (one_le_mul_of_one_le_of_one_le hA hn) hs.le)
      _ ≤ B := hthird
  have hbn : b ≤ n := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hn
      (show 1 - δ ≤ 1 by linarith)
  exact (not_lt_of_ge (hbn.trans hBn)) hB

noncomputable def majorant (n A y : ℕ) (s u : ℝ) : ℝ :=
  (4 * Sieve.totientRatioAverageConstant / A + 3 * (A : ℝ) / y) * n +
    ((A * n : ℕ) : ℝ) ^ s * Real.exp (smoothRankinConstant s u * (y : ℝ) ^ (u - s))

/-- The threshold is independent of ALL the optimization parameters. -/
theorem eventually_majorant_ge_power (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ A y : ℕ, 0 < A → 0 < y →
      ∀ s u : ℝ, 0 < s → 1 < u →
        (n : ℝ) ^ (1 - δ) ≤ majorant n A y s u := by
  have he : 0 < 2 * δ ^ 2 := mul_pos (by norm_num) (sq_pos_of_pos hδ)
  have H := ((isLittleO_log_rpow_atTop he).comp_tendsto
    (show Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop from tendsto_natCast_atTop_atTop)).bound
      (by norm_num : (0 : ℝ) < 1)
  have hC : 1 ≤ Sieve.totientRatioAverageConstant := by
    unfold Sieve.totientRatioAverageConstant
    exact Real.one_le_exp (mul_nonneg (by norm_num)
      (tsum_nonneg (fun n => inv_nonneg.mpr (sq_nonneg _))))
  filter_upwards [H, eventually_ge_atTop 1] with n hlog hn
  have hlog' : Real.log (n : ℝ) ≤ (n : ℝ) ^ (2 * δ ^ 2) := by
    simpa only [Function.comp_apply, Real.norm_of_nonneg (Real.log_natCast_nonneg n),
      Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _), one_mul] using hlog
  intro A y hA hy s u hs hu
  have h := envelope_ge_power (n : ℝ) (A : ℝ) (y : ℝ)
    (4 * Sieve.totientRatioAverageConstant) (smoothRankinConstant s u) s u δ
    (by exact_mod_cast hn) (by exact_mod_cast hA) (by exact_mod_cast hy)
    (by linarith) (smooth_constant_ge_one s u hs hu) hs hu hδ hlog'
  simpa only [majorant, Nat.cast_mul] using h

/-- Even allowing the parameters to depend arbitrarily on n cannot make
this particular upper-bound formula a fixed-power saving. This is a
statement about the formula, NOT a lower bound on g. -/
theorem eventually_majorant_gt_power (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ A y : ℕ, 0 < A → 0 < y →
      ∀ s u : ℝ, 0 < s → 1 < u →
        (n : ℝ) ^ (1 - δ) < majorant n A y s u := by
  filter_upwards [eventually_majorant_ge_power (δ / 2) (by linarith),
    eventually_ge_atTop 2] with n hn hn2
  intro A y hA hy s u hs hu
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  exact (Real.rpow_lt_rpow_of_exponent_lt hn1 (show 1 - δ < 1 - δ / 2 by linarith)).trans_le
    (hn A y hA hy s u hs hu)

end Erdos821.RankinEnvelope
