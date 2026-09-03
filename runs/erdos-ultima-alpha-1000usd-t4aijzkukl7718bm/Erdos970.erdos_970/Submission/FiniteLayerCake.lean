import Submission.SelbergNormalizerUpper

/-! Finite weighted layer-cake identities for truncated linear sieve profiles. -/
namespace Erdos970.FiniteSelberg
open Finset Real MeasureTheory

lemma intervalIntegrable_cut {f : ℝ → ℝ} {c L : ℝ}
    (hf : IntervalIntegrable f volume c L) (a : ℝ) :
    IntervalIntegrable (fun t => if a < t then f t else 0) volume c L := by
  change IntervalIntegrable ((Set.Ioi a).indicator f) volume c L
  exact ⟨hf.1.indicator measurableSet_Ioi, hf.2.indicator measurableSet_Ioi⟩

lemma integral_linear_cut (a c L : ℝ) (hcL : c ≤ L) :
    (∫ t in c..L, if a < t then 2 * (L - t) else 0) =
      max (L - max c a) 0 ^ 2 := by
  rw [intervalIntegral.integral_of_le hcL]
  change (∫ t in Set.Ioc c L, (Set.Ioi a).indicator (fun t => 2 * (L - t)) t) = _
  rw [MeasureTheory.integral_indicator measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi, Set.inter_comm, Set.Ioc_inter_Ioi]
  by_cases h : max c a ≤ L
  · rw [← intervalIntegral.integral_of_le h, max_eq_left (sub_nonneg.mpr h),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub (f := fun _ : ℝ => L) (g := fun t : ℝ => t)
        (continuous_const.intervalIntegrable _ _) (continuous_id.intervalIntegrable _ _),
      intervalIntegral.integral_const, integral_id]
    simp only [smul_eq_mul]
    ring
  · rw [Set.Ioc_eq_empty_of_le (le_of_not_ge h), setIntegral_empty,
      max_eq_right (by linarith : L - max c a ≤ 0)]
    norm_num

variable {ι : Type*} [Fintype ι]

noncomputable def cumulativeMass (w a : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i, if a i < t then w i else 0

lemma cumulative_integrable (w a : ι → ℝ) (c L : ℝ) :
    IntervalIntegrable (fun t => 2 * (L - t) * cumulativeMass w a t) volume c L := by
  have he : (fun t => 2 * (L - t) * cumulativeMass w a t) =
      fun t => ∑ i, if a i < t then 2 * (L - t) * w i else 0 := by
    funext t
    simp only [cumulativeMass, mul_sum, mul_ite, mul_zero]
  rw [he]
  have hh := IntervalIntegrable.sum univ (fun i (_ : i ∈ (univ : Finset ι)) =>
    intervalIntegrable_cut
      ((by fun_prop : Continuous (fun t : ℝ => 2 * (L - t) * w i)).intervalIntegrable c L) (a i))
  simpa only [sum_fn] using hh

/-- A finite layer-cake identity. The strict cutoff avoids endpoint conventions. -/
theorem weighted_linear_cut (w a : ι → ℝ) (c L : ℝ) (hcL : c ≤ L) :
    (∑ i, w i * max (L - max c (a i)) 0 ^ 2) =
      ∫ t in c..L, 2 * (L - t) * cumulativeMass w a t := by
  have he : (fun t => 2 * (L - t) * cumulativeMass w a t) =
      fun t => ∑ i, w i * (if a i < t then 2 * (L - t) else 0) := by
    funext t
    simp only [cumulativeMass, mul_sum]
    apply sum_congr rfl
    intro i hi
    split_ifs <;> ring
  rw [he, intervalIntegral.integral_finset_sum]
  · apply sum_congr rfl
    intro i hi
    rw [intervalIntegral.integral_const_mul, integral_linear_cut _ _ _ hcL]
  · intro i hi
    exact (intervalIntegrable_cut
      ((by fun_prop : Continuous (fun t : ℝ => 2 * (L - t))).intervalIntegrable c L) (a i)).const_mul _

lemma integral_linear_times_affine (A C c L : ℝ) :
    (∫ t in c..L, 2 * (L - t) * (A * t + C)) =
      A * (L * (L - c) ^ 2 - (2 / 3) * (L - c) ^ 3) + C * (L - c) ^ 2 := by
  have he : (fun t : ℝ => 2 * (L - t) * (A * t + C)) =
      fun t => (-2 * A) * t ^ 2 + (2 * A * L - 2 * C) * t + 2 * L * C := by
    funext t
    ring
  rw [he, intervalIntegral.integral_add, intervalIntegral.integral_add]
  · rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      integral_pow, integral_id, intervalIntegral.integral_const]
    simp only [Nat.cast_ofNat, smul_eq_mul]
    ring
  all_goals apply Continuous.intervalIntegrable; fun_prop

/-- A lower bound for a truncated affine square from a cumulative lower bound. -/
theorem soft_square_lower (w a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (L E : ℝ) (hL : 0 ≤ L)
    (hF : ∀ t ∈ Set.Icc 0 L, t - E ≤ cumulativeMass w a t) :
    L ^ 3 / 3 - E * L ^ 2 ≤ ∑ i, w i * max (L - a i) 0 ^ 2 := by
  have hh := intervalIntegral.integral_mono_on hL
    ((by fun_prop : Continuous (fun t : ℝ => 2 * (L - t) * (t - E))).intervalIntegrable 0 L)
    (cumulative_integrable w a 0 L)
    (fun t ht => mul_le_mul_of_nonneg_left (hF t ht) (by linarith [ht.2]))
  have hpoly := integral_linear_times_affine 1 (-E) 0 L
  simp only [one_mul, sub_zero] at hpoly
  have he : (fun t : ℝ => 2 * (L - t) * (t - E)) =
      fun t => 2 * (L - t) * (t + -E) := by funext t; ring
  rw [he, hpoly, ← weighted_linear_cut w a 0 L hL] at hh
  simp only [max_eq_right (ha _)] at hh
  nlinarith only [hh]

/-- A cumulative upper bound controls every capped square, with the cubic
correction retained rather than discarded. -/
theorem capped_square_upper (w a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (L v A C : ℝ) (hv : 0 ≤ v) (hvL : v ≤ L)
    (hF : ∀ t ∈ Set.Icc 0 L, cumulativeMass w a t ≤ A * t + C) :
    (∑ i, w i * min v (max (L - a i) 0) ^ 2) ≤
      A * (L * v ^ 2 - (2 / 3) * v ^ 3) + C * v ^ 2 := by
  have hcL : L - v ≤ L := by linarith
  have hh := intervalIntegral.integral_mono_on hcL
    (cumulative_integrable w a (L - v) L)
    ((by fun_prop : Continuous (fun t : ℝ => 2 * (L - t) * (A * t + C))).intervalIntegrable (L - v) L)
    (fun t ht => mul_le_mul_of_nonneg_left (hF t ⟨by linarith [ht.1], ht.2⟩)
      (by linarith [ht.2]))
  rw [integral_linear_times_affine, ← weighted_linear_cut w a (L - v) L hcL,
    sub_sub_cancel] at hh
  have he (i : ι) : max (L - max (L - v) (a i)) 0 = min v (max (L - a i) 0) := by
    rcases le_total (a i) (L - v) with h | h
    · rw [max_eq_left h, sub_sub_cancel, max_eq_left hv, min_eq_left]
      exact (show v ≤ L - a i by linarith).trans (le_max_left _ _)
    · rw [max_eq_right h]
      symm
      exact min_eq_right (max_le (by linarith) hv)
  simp_rw [he] at hh
  exact hh

lemma integral_constant_cut (a L : ℝ) (hL : 0 ≤ L) (ha : 0 ≤ a) :
    (∫ t in 0..L, if a < t then (1 : ℝ) else 0) = max (L - a) 0 := by
  rw [intervalIntegral.integral_of_le hL]
  change (∫ t in Set.Ioc 0 L, (Set.Ioi a).indicator (fun _ => (1 : ℝ)) t) = _
  rw [MeasureTheory.integral_indicator measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi, Set.inter_comm, Set.Ioc_inter_Ioi,
    max_eq_right ha]
  by_cases h : a ≤ L
  · rw [← intervalIntegral.integral_of_le h, max_eq_left (sub_nonneg.mpr h),
      intervalIntegral.integral_const]
    simp only [smul_eq_mul, mul_one]
  · rw [Set.Ioc_eq_empty_of_le (le_of_not_ge h), setIntegral_empty,
      max_eq_right (by linarith : L - a ≤ 0)]

lemma cumulativeMass_integrable (w a : ι → ℝ) (c L : ℝ) :
    IntervalIntegrable (cumulativeMass w a) volume c L := by
  have hh := IntervalIntegrable.sum univ (fun i (_ : i ∈ (univ : Finset ι)) =>
    intervalIntegrable_cut ((show Continuous (fun _ : ℝ => w i) from continuous_const).intervalIntegrable c L) (a i))
  simpa only [sum_fn, cumulativeMass] using (hh :
    IntervalIntegrable (∑ i, fun t => if a i < t then w i else 0) volume c L)

lemma weighted_first_cut (w a : ι → ℝ) (L : ℝ) (hL : 0 ≤ L) (ha : ∀ i, 0 ≤ a i) :
    (∑ i, w i * max (L - a i) 0) = ∫ t in 0..L, cumulativeMass w a t := by
  have he : cumulativeMass w a =
      fun t => ∑ i, w i * (if a i < t then (1 : ℝ) else 0) := by
    funext t
    simp only [cumulativeMass, mul_ite, mul_one, mul_zero]
  rw [he, intervalIntegral.integral_finset_sum]
  · apply sum_congr rfl
    intro i hi
    rw [intervalIntegral.integral_const_mul, integral_constant_cut _ _ hL (ha i)]
  · intro i hi
    exact (intervalIntegrable_cut
      (continuous_const.intervalIntegrable 0 L) (a i)).const_mul (w i)

lemma integral_affine (C L : ℝ) : (∫ t in 0..L, t + C) = L ^ 2 / 2 + C * L := by
  rw [intervalIntegral.integral_add (f := fun t : ℝ => t) (g := fun _ : ℝ => C) (continuous_id.intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _), integral_id, intervalIntegral.integral_const]
  simp only [zero_pow (by omega : 2 ≠ 0), sub_zero, smul_eq_mul]
  ring

/-- Approximate uniform cumulative mass gives sharp leading coefficients for
its first two ordinary moments. No probabilistic independence is used. -/
theorem cumulative_moments (w a : ι → ℝ) (L E : ℝ) (hL : 0 ≤ L)
    (ha : ∀ i, 0 ≤ a i ∧ a i ≤ L)
    (htotal : |(∑ i, w i) - L| ≤ E)
    (hF : ∀ t ∈ Set.Icc 0 L, |cumulativeMass w a t - t| ≤ E) :
    |(∑ i, w i * a i) - L ^ 2 / 2| ≤ 2 * E * L ∧
    |(∑ i, w i * a i ^ 2) - L ^ 3 / 3| ≤ 4 * E * L ^ 2 := by
  let s₁ := ∑ i, w i * max (L - a i) 0
  let s₂ := ∑ i, w i * max (L - a i) 0 ^ 2
  have hs₁lo : L ^ 2 / 2 - E * L ≤ s₁ := by
    have hh := intervalIntegral.integral_mono_on hL
      ((continuous_id.add continuous_const).intervalIntegrable 0 L)
      (cumulativeMass_integrable w a 0 L)
      (fun t ht => (show t + -E ≤ cumulativeMass w a t from by
        have := (abs_le.mp (hF t ht)).1; linarith))
    simp only [id_eq] at hh
    rw [integral_affine, ← weighted_first_cut w a L hL (fun i => (ha i).1)] at hh
    dsimp [s₁]
    linarith
  have hs₁hi : s₁ ≤ L ^ 2 / 2 + E * L := by
    have hh := intervalIntegral.integral_mono_on hL
      (cumulativeMass_integrable w a 0 L)
      ((continuous_id.add continuous_const).intervalIntegrable 0 L)
      (fun t ht => (show cumulativeMass w a t ≤ t + E from by
        have := (abs_le.mp (hF t ht)).2; linarith))
    simp only [id_eq] at hh
    rw [integral_affine, ← weighted_first_cut w a L hL (fun i => (ha i).1)] at hh
    exact hh
  have hs₂lo : L ^ 3 / 3 - E * L ^ 2 ≤ s₂ :=
    soft_square_lower w a (fun i => (ha i).1) L E hL (fun t ht => by
      have := (abs_le.mp (hF t ht)).1; linarith)
  have hs₂hi : s₂ ≤ L ^ 3 / 3 + E * L ^ 2 := by
    have hh := capped_square_upper w a (fun i => (ha i).1) L L 1 E hL le_rfl
      (fun t ht => by have := (abs_le.mp (hF t ht)).2; linarith)
    have he (i : ι) : min L (max (L - a i) 0) = max (L - a i) 0 :=
      min_eq_right (max_le (by linarith [(ha i).1]) hL)
    simp_rw [he] at hh
    dsimp [s₂]
    nlinarith only [hh]
  have he₁ : (∑ i, w i * a i) = L * (∑ i, w i) - s₁ := by
    dsimp [s₁]
    rw [mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro i hi
    rw [max_eq_left (sub_nonneg.mpr (ha i).2)]
    ring
  have he₂ : (∑ i, w i * a i ^ 2) = L ^ 2 * (∑ i, w i) - 2 * L * s₁ + s₂ := by
    dsimp [s₁, s₂]
    rw [mul_sum, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro i hi
    rw [max_eq_left (sub_nonneg.mpr (ha i).2)]
    ring
  have ht := abs_le.mp htotal
  have htlo := mul_le_mul_of_nonneg_left ht.1 hL
  have hthi := mul_le_mul_of_nonneg_left ht.2 hL
  have htlo₂ := mul_le_mul_of_nonneg_left ht.1 (sq_nonneg L)
  have hthi₂ := mul_le_mul_of_nonneg_left ht.2 (sq_nonneg L)
  have h1lo := mul_le_mul_of_nonneg_left hs₁lo hL
  have h1hi := mul_le_mul_of_nonneg_left hs₁hi hL
  rw [he₁, he₂, abs_le, abs_le]
  constructor <;> constructor <;> nlinarith only [htlo, hthi, htlo₂, hthi₂, hs₁lo, hs₁hi,
    h1lo, h1hi, hs₂lo, hs₂hi]

#print axioms weighted_linear_cut
#print axioms soft_square_lower
#print axioms capped_square_upper
#print axioms cumulative_moments
end Erdos970.FiniteSelberg
