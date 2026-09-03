import FormalConjecturesUtil

/-! A decreasing fractional profile with exactly constant self-convolution.
It is used for finite integer block tapering, not for an infinite 0/1 witness. -/
namespace Erdos66ConstantProfile
open AdditiveCombinatorics PowerSeries Filter
open scoped Topology

noncomputable def b : ℕ → ℝ
  | 0 => 1
  | n + 1 => b n * (2 * n + 1) / (2 * (n + 1))

@[simp] lemma b_zero : b 0 = 1 := rfl

lemma b_succ (n : ℕ) : b (n + 1) = b n * (2 * n + 1) / (2 * (n + 1)) := by rw [b]

lemma b_pos (n : ℕ) : 0 < b n := by
  induction n with
  | zero => norm_num
  | succ n ih => rw [b_succ]; positivity

lemma b_recurrence (n : ℕ) : 2 * ((n : ℝ) + 1) * b (n + 1) = (2 * n + 1) * b n := by
  rw [b_succ]
  field_simp

lemma b_antitone : Antitone b := by
  apply antitone_nat_of_succ_le
  intro n
  have hb := b_recurrence n
  have hp := b_pos n
  have hn := Nat.cast_nonneg (α := ℝ) n
  nlinarith

lemma b_le_one (n : ℕ) : b n ≤ 1 := by simpa using b_antitone (Nat.zero_le n)

lemma b_square_bound (n : ℕ) : ((n : ℝ) + 1) * b n ^ 2 ≤ 1 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have hn := Nat.cast_nonneg (α := ℝ) n
    have hn1 : (0 : ℝ) < 2 * (n + 1) := by positivity
    have hb := b_recurrence n
    have hs := congrArg (fun x : ℝ ↦ x ^ 2) hb
    have hpoly : (2 * (n : ℝ) + 1) ^ 2 * (n + 2) ≤ 4 * (n + 1) ^ 3 := by nlinarith
    have hm := mul_le_mul_of_nonneg_right hpoly (sq_nonneg (b n))
    have hm' := mul_le_mul_of_nonneg_left ih (sq_nonneg (2 * ((n : ℝ) + 1)))
    push_cast
    nlinarith [sq_nonneg (b (n + 1))]

lemma b_differential : 2 * (1 - X) * derivative ℝ (PowerSeries.mk b) = PowerSeries.mk b := by
  ext n
  cases n with
  | zero =>
    rw [mul_assoc, sub_mul, one_mul, two_mul]
    simp only [map_add, map_sub, coeff_zero_X_mul, coeff_derivative, coeff_mk]
    norm_num [b_succ]
  | succ n =>
    rw [mul_assoc, show (1 - X : PowerSeries ℝ) * derivative ℝ (PowerSeries.mk b) =
      derivative ℝ (PowerSeries.mk b) - X * derivative ℝ (PowerSeries.mk b) by ring,
      two_mul]
    simp only [map_add, map_sub, coeff_succ_X_mul, coeff_derivative, coeff_mk]
    have h₁ := b_recurrence n
    have h₂ := b_recurrence (n + 1)
    push_cast at h₂ ⊢
    nlinarith

lemma b_series_square : (PowerSeries.mk b) ^ 2 = PowerSeries.mk (fun _ ↦ (1 : ℝ)) := by
  have hd : derivative ℝ ((1 - X) * (PowerSeries.mk b) ^ 2) = 0 := by
    rw [Derivation.leibniz, map_sub]
    simp only [Derivation.map_one_eq_zero, derivative_X, zero_sub, Derivation.leibniz_pow,
      smul_eq_mul, Nat.reduceSub, pow_one, nsmul_eq_mul, Nat.cast_ofNat]
    have hh := congrArg (fun f : PowerSeries ℝ ↦ f * PowerSeries.mk b) b_differential
    linear_combination hh
  have he : (1 - X) * (PowerSeries.mk b) ^ 2 = 1 := by
    apply PowerSeries.derivative.ext
    · simpa using hd
    · simp
  have hg : (1 - X : PowerSeries ℝ) * PowerSeries.mk (fun _ ↦ (1 : ℝ)) = 1 := by
    ext n
    cases n with
    | zero => simp
    | succ n => simp [sub_mul]
  have hne : (1 - X : PowerSeries ℝ) ≠ 0 := by
    intro hz
    have hh := congrArg (constantCoeff (R := ℝ)) hz
    simpa using hh
  exact mul_left_cancel₀ hne (he.trans hg.symm)

lemma b_convolution (n : ℕ) : sumConv b b n = 1 := by
  have hh := congrArg (coeff n) b_series_square
  simpa only [pow_two, coeff_mul, coeff_mk, sumConv] using hh

lemma b_partial_sum (n : ℕ) : (∑ i ∈ Finset.range (n + 1), b i) = (2 * n + 1) * b n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have hh := b_recurrence n
    push_cast
    nlinarith

lemma b_tendsto_zero : Tendsto b atTop (𝓝 0) := by
  have hinv : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop).const_div_atTop 1
  have hs : Tendsto (fun n ↦ b n ^ 2) atTop (𝓝 0) := by
    apply squeeze_zero (fun n ↦ sq_nonneg _) ?_ hinv
    intro n
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < n + 1)).mpr
    nlinarith [b_square_bound n]
  have hh := hs.sqrt
  simpa only [Real.sqrt_zero, Real.sqrt_sq (b_pos _).le] using hh

end Erdos66ConstantProfile
