import Submission.CumulativeExplore

/-!
# Weighted moments of a logarithmic representation asymptotic

Auxiliary analysis for integer prefixes; no existence or nonexistence conclusion.
-/

namespace Erdos66WeightedLog
open Filter AdditiveCombinatorics Erdos66Cumulative
open scoped Topology

lemma log_le_log_nat (i n : ℕ) (hi : i ≤ n) (hn : 1 ≤ n) :
    Real.log (i : ℝ) ≤ Real.log (n : ℝ) := by
  by_cases hz : i = 0
  · simpa only [hz, Nat.cast_zero, Real.log_zero] using log_nat_nonneg n
  · apply Real.log_le_log (by exact_mod_cast (show 0 < i by omega))
    exact_mod_cast hi

lemma absolute_log_error_limit {f : ℕ → ℝ} {c : ℝ}
    (h : Tendsto (fun n ↦ f n / Real.log n) atTop (𝓝 c)) :
    Tendsto (fun n : ℕ ↦ (∑ i ∈ Finset.range n, |f i - c * Real.log i|) /
      ((n : ℝ) * Real.log n)) atTop (𝓝 0) := by
  apply cumulative_of_log_limit
  have hh := (h.sub_const c).abs
  simp only [sub_self, abs_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hl : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  rw [← abs_of_pos hl, ← abs_div]
  congr 1
  rw [abs_of_pos hl]
  field_simp

lemma flat_log_error_limit {f : ℕ → ℝ} {c : ℝ}
    (h : Tendsto (fun n ↦ f n / Real.log n) atTop (𝓝 c)) :
    Tendsto (fun n : ℕ ↦ (∑ i ∈ Finset.range n, |f i - c * Real.log n|) /
      ((n : ℝ) * Real.log n)) atTop (𝓝 0) := by
  have hb := (absolute_log_error_limit h).add
    ((sum_log_normalized_limit.const_sub 1).const_mul |c|)
  simp only [sub_self, mul_zero, add_zero] at hb
  apply squeeze_zero' ?_ ?_ hb
  · filter_upwards [eventually_ge_atTop 2] with n hn
    exact div_nonneg (Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _))
      (mul_nonneg (Nat.cast_nonneg _) (log_nat_nonneg _))
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    have hl0 : Real.log (n : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast hn))
    have hden : 0 ≤ (n : ℝ) * Real.log n := mul_nonneg (Nat.cast_nonneg _) (log_nat_nonneg _)
    have hs : (∑ i ∈ Finset.range n, |f i - c * Real.log n|) ≤
        (∑ i ∈ Finset.range n, |f i - c * Real.log i|) +
          |c| * ((n : ℝ) * Real.log n - ∑ i ∈ Finset.range n, Real.log (i : ℝ)) := by
      calc
        _ ≤ ∑ i ∈ Finset.range n, (|f i - c * Real.log i| +
            |c| * (Real.log n - Real.log i)) := by
          apply Finset.sum_le_sum
          intro i hi
          have hli := log_le_log_nat i n (by have := Finset.mem_range.mp hi; omega) (by omega)
          calc
            _ = |(f i - c * Real.log i) + c * (Real.log i - Real.log n)| := by congr 1; ring
            _ ≤ _ := (abs_add_le _ _).trans_eq (by
              rw [abs_mul, abs_sub_comm (Real.log (i : ℝ)) (Real.log (n : ℝ)), abs_of_nonneg (sub_nonneg.mpr hli)])
        _ = _ := by
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
            Finset.sum_const, nsmul_eq_mul, Finset.card_range]
    calc
      _ ≤ ((∑ i ∈ Finset.range n, |f i - c * Real.log i|) +
          |c| * ((n : ℝ) * Real.log n - ∑ i ∈ Finset.range n, Real.log (i : ℝ))) /
            ((n : ℝ) * Real.log n) := div_le_div_of_nonneg_right hs hden
      _ = _ := by field_simp

/-- Bounded weights can be tested against the asymptotically constant profile on `[0,n)`. -/
lemma weighted_log_limit {f : ℕ → ℝ} {c L : ℝ}
    (h : Tendsto (fun n ↦ f n / Real.log n) atTop (𝓝 c)) (w : ℕ → ℕ → ℝ)
    (hw : ∀ n i, i < n → |w n i| ≤ 1)
    (havg : Tendsto (fun n : ℕ ↦ (∑ i ∈ Finset.range n, w n i) / n) atTop (𝓝 L)) :
    Tendsto (fun n : ℕ ↦ (∑ i ∈ Finset.range n, w n i * f i) /
      ((n : ℝ) * Real.log n)) atTop (𝓝 (c * L)) := by
  let err := fun n : ℕ ↦ (∑ i ∈ Finset.range n, w n i * f i) /
      ((n : ℝ) * Real.log n) - c * ((∑ i ∈ Finset.range n, w n i) / n)
  have herr : Tendsto err atTop (𝓝 0) := by
    apply (tendsto_zero_iff_abs_tendsto_zero err).mpr
    apply squeeze_zero' (Filter.Eventually.of_forall (fun n ↦ abs_nonneg (err n))) ?_
      (flat_log_error_limit h)
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    have hl0 : Real.log (n : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast hn))
    have hden : 0 ≤ (n : ℝ) * Real.log n := mul_nonneg (Nat.cast_nonneg _) (log_nat_nonneg _)
    have he : err n = (∑ i ∈ Finset.range n, w n i * (f i - c * Real.log n)) /
        ((n : ℝ) * Real.log n) := by
      dsimp [err]
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
      field_simp
    rw [he, abs_div, abs_of_nonneg hden]
    apply div_le_div_of_nonneg_right _ hden
    calc
      _ ≤ ∑ i ∈ Finset.range n, |w n i * (f i - c * Real.log n)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i hi
        rw [abs_mul]
        exact (mul_le_mul_of_nonneg_right (hw n i (Finset.mem_range.mp hi)) (abs_nonneg _)).trans_eq
          (one_mul _)
  have hh := (havg.const_mul c).add herr
  simp only [add_zero] at hh
  apply hh.congr'
  filter_upwards [] with n
  dsimp [err]
  ring



lemma sum_pow_formula0 (n : ℕ) :
    (∑ i ∈ Finset.range n, (i : ℝ) ^ 0) = (n : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

lemma sum_pow_formula1 (n : ℕ) :
    (∑ i ∈ Finset.range n, (i : ℝ) ^ 1) = (n : ℝ) * (n - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

lemma sum_pow_formula2 (n : ℕ) :
    (∑ i ∈ Finset.range n, (i : ℝ) ^ 2) = (n : ℝ) * (n - 1) * (2 * n - 1) / 6 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

lemma sum_pow_formula3 (n : ℕ) :
    (∑ i ∈ Finset.range n, (i : ℝ) ^ 3) = (n : ℝ) ^ 2 * (n - 1) ^ 2 / 4 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

lemma sum_pow_formula4 (n : ℕ) :
    (∑ i ∈ Finset.range n, (i : ℝ) ^ 4) = (n : ℝ) * (n - 1) * (2 * n - 1) * (3 * n ^ 2 - 3 * n - 1) / 30 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

lemma scaled_pow_average_eq (n k : ℕ) :
    (∑ i ∈ Finset.range n, ((i : ℝ) / n) ^ k) / n =
      (∑ i ∈ Finset.range n, (i : ℝ) ^ k) / (n : ℝ) ^ (k + 1) := by
  simp only [div_pow, ← Finset.sum_div, div_div, pow_succ]

lemma scaled_pow_average_limit (k : ℕ) (hk : k ≤ 4) :
    Tendsto (fun n : ℕ ↦ (∑ i ∈ Finset.range n, ((i : ℝ) / n) ^ k) / n)
      atTop (𝓝 (1 / ((k : ℝ) + 1))) := by
  interval_cases k <;> norm_num only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat]
  · apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    rw [scaled_pow_average_eq, sum_pow_formula0]
    field_simp
    <;> ring
  · have hcont : Continuous (fun t : ℝ ↦ (1 - t) / 2) := by fun_prop
    have hlim : Tendsto (fun n : ℕ ↦ (1 - (1 / (n : ℝ))) / 2) atTop (𝓝 (1 / ((1 : ℝ) + 1))) := by
      convert (hcont.tendsto 0).comp (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)) using 1 <;> norm_num
    norm_num at hlim
    apply hlim.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    rw [scaled_pow_average_eq, sum_pow_formula1]
    field_simp
    <;> ring
  · have hcont : Continuous (fun t : ℝ ↦ (1 - t) * (2 - t) / 6) := by fun_prop
    have hlim : Tendsto (fun n : ℕ ↦ (1 - (1 / (n : ℝ))) * (2 - (1 / (n : ℝ))) / 6) atTop (𝓝 (1 / ((2 : ℝ) + 1))) := by
      convert (hcont.tendsto 0).comp (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)) using 1 <;> norm_num
    norm_num at hlim
    apply hlim.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    rw [scaled_pow_average_eq, sum_pow_formula2]
    field_simp
    <;> ring
  · have hcont : Continuous (fun t : ℝ ↦ (1 - t) ^ 2 / 4) := by fun_prop
    have hlim : Tendsto (fun n : ℕ ↦ (1 - (1 / (n : ℝ))) ^ 2 / 4) atTop (𝓝 (1 / ((3 : ℝ) + 1))) := by
      convert (hcont.tendsto 0).comp (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)) using 1 <;> norm_num
    norm_num at hlim
    apply hlim.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    rw [scaled_pow_average_eq, sum_pow_formula3]
    field_simp
    <;> ring
  · have hcont : Continuous (fun t : ℝ ↦ (1 - t) * (2 - t) * (3 - 3 * t - t ^ 2) / 30) := by fun_prop
    have hlim : Tendsto (fun n : ℕ ↦ (1 - (1 / (n : ℝ))) * (2 - (1 / (n : ℝ))) * (3 - 3 * (1 / (n : ℝ)) - (1 / (n : ℝ)) ^ 2) / 30) atTop (𝓝 (1 / ((4 : ℝ) + 1))) := by
      convert (hcont.tendsto 0).comp (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)) using 1 <;> norm_num
    norm_num at hlim
    apply hlim.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    rw [scaled_pow_average_eq, sum_pow_formula4]
    field_simp
    <;> ring

lemma log_weighted_power_limit {f : ℕ → ℝ} {c : ℝ}
    (h : Tendsto (fun n ↦ f n / Real.log n) atTop (𝓝 c)) (k : ℕ) (hk : k ≤ 4) :
    Tendsto (fun n : ℕ ↦ (∑ i ∈ Finset.range n, ((i : ℝ) / n) ^ k * f i) /
      ((n : ℝ) * Real.log n)) atTop (𝓝 (c / ((k : ℝ) + 1))) := by
  have hw (n i : ℕ) (hi : i < n) : |((i : ℝ) / n) ^ k| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]
    apply pow_le_one₀ (by positivity)
    apply (div_le_one (by exact_mod_cast (show 0 < n by omega))).mpr
    exact_mod_cast hi.le
  simpa only [one_div, div_eq_mul_inv, one_mul] using
    weighted_log_limit h (fun n i ↦ ((i : ℝ) / n) ^ k) hw (scaled_pow_average_limit k hk)

end Erdos66WeightedLog
