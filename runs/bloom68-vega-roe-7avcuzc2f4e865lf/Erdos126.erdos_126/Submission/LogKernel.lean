import FormalConjecturesUtil

/-!
# Conditional negative definiteness of the additive logarithm kernel

The proof uses the power series for `-log (1 - x)`, after the change of
variables `x = (a - 1) / (a + 1)`. No distinctness assumption is needed.
-/

namespace Erdos126Log

/-- The change of variables from positive reals to the open interval `(-1, 1)`. -/
noncomputable def mobius (a : ℝ) : ℝ := (a - 1) / (a + 1)

lemma abs_mobius_lt_one {a : ℝ} (ha : 0 < a) : |mobius a| < 1 := by
  have hden : 0 < a + 1 := by linarith
  rw [mobius, abs_lt]
  constructor
  · apply (lt_div_iff₀ hden).2
    linarith
  · apply (div_lt_iff₀ hden).2
    linarith

lemma log_add_mobius {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Real.log (a + b) = Real.log (a + 1) + Real.log (b + 1) - Real.log 2 +
      Real.log (1 - mobius a * mobius b) := by
  have ha1 : a + 1 ≠ 0 := ne_of_gt (by linarith)
  have hb1 : b + 1 ≠ 0 := ne_of_gt (by linarith)
  have hab : a + b ≠ 0 := ne_of_gt (add_pos ha hb)
  have htwo : (2 : ℝ) ≠ 0 := by norm_num
  have hid : 1 - mobius a * mobius b = (2 * (a + b)) / ((a + 1) * (b + 1)) := by
    unfold mobius
    field_simp [ha1, hb1]
    ring
  rw [hid, Real.log_div (mul_ne_zero htwo hab) (mul_ne_zero ha1 hb1),
    Real.log_mul htwo hab, Real.log_mul ha1 hb1]
  ring

/-- Each coefficient of the summed logarithm power series is a nonnegative square. -/
lemma log_one_sub_mul_nonpos {ι : Type*} [Fintype ι] (x c : ι → ℝ)
    (hx : ∀ i, |x i| < 1) :
    (∑ i, ∑ j, c i * c j * Real.log (1 - x i * x j)) ≤ 0 := by
  classical
  have hprod (i j : ι) : |x i * x j| < 1 := by
    rw [abs_mul]
    calc
      |x i| * |x j| ≤ 1 * |x j| :=
        mul_le_mul_of_nonneg_right (hx i).le (abs_nonneg _)
      _ < 1 := by simpa only [one_mul] using hx j
  have hs : HasSum
      (fun n : ℕ => ∑ i, ∑ j,
        c i * c j * ((x i * x j) ^ (n + 1) / ((n : ℝ) + 1)))
      (∑ i, ∑ j, c i * c j * (-Real.log (1 - x i * x j))) := by
    exact hasSum_sum (fun i _ => hasSum_sum (fun j _ =>
      (Real.hasSum_pow_div_log_of_abs_lt_one (hprod i j)).mul_left (c i * c j)))
  have hterm (n : ℕ) :
      (∑ i, ∑ j, c i * c j * ((x i * x j) ^ (n + 1) / ((n : ℝ) + 1))) =
        (∑ i, c i * x i ^ (n + 1)) ^ 2 / ((n : ℝ) + 1) := by
    rw [pow_two, Finset.sum_mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [mul_pow]
    ring
  have hnonneg : 0 ≤ ∑ i, ∑ j, c i * c j * (-Real.log (1 - x i * x j)) :=
    hs.nonneg (fun n => by
      rw [hterm]
      exact div_nonneg (sq_nonneg _) (Nat.cast_add_one_pos n).le)
  simpa only [mul_neg, Finset.sum_neg_distrib, neg_nonneg] using hnonneg

/-- Zero-sum coefficients annihilate kernels which separate into a row and a column term. -/
lemma sum_separable_eq_zero {ι : Type*} [Fintype ι] (c u v : ι → ℝ)
    (hc : ∑ i, c i = 0) :
    (∑ i, ∑ j, c i * c j * (u i + v j)) = 0 := by
  classical
  calc
    (∑ i, ∑ j, c i * c j * (u i + v j)) =
        (∑ i, c i * u i) * (∑ j, c j) + (∑ i, c i) * (∑ j, c j * v j) := by
      rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring
    _ = 0 := by rw [hc]; ring

/-- The additive logarithm kernel is conditionally negative definite on positive reals. -/
lemma log_add_cnd {ι : Type*} [Fintype ι] (a c : ι → ℝ)
    (ha : ∀ i, 0 < a i) (hc : ∑ i, c i = 0) :
    (∑ i, ∑ j, c i * c j * Real.log (a i + a j)) ≤ 0 := by
  classical
  have hnonpos := log_one_sub_mul_nonpos (fun i => mobius (a i)) c
    (fun i => abs_mobius_lt_one (ha i))
  have hcancel :
      (∑ i, ∑ j, c i * c j *
        (Real.log (a i + 1) + (Real.log (a j + 1) - Real.log 2))) = 0 :=
    sum_separable_eq_zero c (fun i => Real.log (a i + 1))
      (fun j => Real.log (a j + 1) - Real.log 2) hc
  calc
    (∑ i, ∑ j, c i * c j * Real.log (a i + a j)) =
        (∑ i, ∑ j, c i * c j *
          (Real.log (a i + 1) + (Real.log (a j + 1) - Real.log 2))) +
        (∑ i, ∑ j, c i * c j * Real.log (1 - mobius (a i) * mobius (a j))) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [log_add_mobius (ha i) (ha j)]
      ring
    _ ≤ 0 := by rw [hcancel, zero_add]; exact hnonpos

end Erdos126Log
