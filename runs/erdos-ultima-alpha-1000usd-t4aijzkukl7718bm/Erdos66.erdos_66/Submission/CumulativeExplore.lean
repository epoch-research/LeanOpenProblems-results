import Submission.CountingExplore

/-!
# First-order cumulative asymptotics forced by a witness

These are necessary conditions only, not a settlement of Erdős Problem 66.
-/

namespace Erdos66Cumulative
open Filter AdditiveCombinatorics Asymptotics Erdos66Counting
open scoped Topology

lemma log_nat_nonneg (n : ℕ) : 0 ≤ Real.log (n : ℝ) := by
  by_cases hn : n = 0
  · simp [hn]
  · apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ n by omega)

lemma log_factorial_eq_sum (n : ℕ) :
    Real.log (n.factorial : ℝ) = ∑ i ∈ Finset.range n, Real.log ((i : ℝ) + 1) := by
  rw [Nat.factorial_eq_prod_range_add_one, Nat.cast_prod]
  simp only [Nat.cast_add, Nat.cast_one]
  exact Real.log_prod (fun i hi ↦ by positivity)

lemma log_factorial_bounds (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) * Real.log n - n ≤ Real.log (n.factorial : ℝ) ∧
      Real.log (n.factorial : ℝ) ≤ (n : ℝ) * Real.log n := by
  constructor
  · have h := Stirling.le_log_factorial_stirling (by omega : n ≠ 0)
    have hlog := log_nat_nonneg n
    have hpi : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
    linarith
  · rw [log_factorial_eq_sum]
    calc
      _ ≤ ∑ _i ∈ Finset.range n, Real.log (n : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        apply Real.log_le_log (by positivity)
        exact_mod_cast (show i + 1 ≤ n from Finset.mem_range.mp hi)
      _ = _ := by simp

lemma log_factorial_normalized_limit :
    Tendsto (fun n : ℕ ↦ Real.log (n.factorial : ℝ) / ((n : ℝ) * Real.log n))
      atTop (𝓝 1) := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hz : Tendsto (fun n : ℕ ↦
      1 - Real.log (n.factorial : ℝ) / ((n : ℝ) * Real.log n)) atTop (𝓝 0) := by
    apply squeeze_zero' ?_ ?_ (hlog.const_div_atTop 1)
    · filter_upwards [eventually_ge_atTop 2] with n hn
      have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
      have hb := (log_factorial_bounds n (by omega)).2
      exact sub_nonneg.mpr ((div_le_one (mul_pos hnpos hlogpos)).mpr hb)
    · filter_upwards [eventually_ge_atTop 2] with n hn
      have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
      have hb := (log_factorial_bounds n (by omega)).1
      have hh := div_le_div_of_nonneg_right hb (mul_pos hnpos hlogpos).le
      have he : ((n : ℝ) * Real.log n - n) / ((n : ℝ) * Real.log n) =
          1 - 1 / Real.log n := by field_simp
      rw [he] at hh
      linarith
  have hh := hz.const_sub 1
  simpa only [sub_zero, sub_sub_cancel] using hh

lemma sum_log_shift (n : ℕ) :
    (∑ i ∈ Finset.range n, Real.log ((i : ℝ) + 1)) =
      (∑ i ∈ Finset.range n, Real.log (i : ℝ)) + Real.log (n : ℝ) := by
  have h := Finset.sum_range_succ' (fun i : ℕ ↦ Real.log (i : ℝ)) n
  rw [Finset.sum_range_succ] at h
  simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, Real.log_zero, add_zero] using h.symm

lemma sum_log_normalized_limit :
    Tendsto (fun n : ℕ ↦ (∑ i ∈ Finset.range n, Real.log (i : ℝ)) /
      ((n : ℝ) * Real.log n)) atTop (𝓝 1) := by
  have h := log_factorial_normalized_limit.sub (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hl0 : Real.log (n : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast hn))
  rw [log_factorial_eq_sum, sum_log_shift]
  field_simp
  ring

lemma sum_log_tendsto_atTop :
    Tendsto (fun n : ℕ ↦ ∑ i ∈ Finset.range n, Real.log (i : ℝ)) atTop atTop := by
  have hg : Tendsto (fun n : ℕ ↦ (n : ℝ) * Real.log n) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_atTop₀
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have h := hg.atTop_mul_pos (by norm_num : (0 : ℝ) < 1) sum_log_normalized_limit
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hl0 : Real.log (n : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast hn))
  field_simp

/-- Summing a logarithmic asymptotic preserves its leading coefficient. -/
lemma cumulative_of_log_limit {f : ℕ → ℝ} {c : ℝ}
    (h : Tendsto (fun n ↦ f n / Real.log n) atTop (𝓝 c)) :
    Tendsto (fun n : ℕ ↦ (∑ i ∈ Finset.range n, f i) / ((n : ℝ) * Real.log n))
      atTop (𝓝 c) := by
  have he : (fun n : ℕ ↦ f n - c * Real.log n) =o[atTop]
      (fun n : ℕ ↦ Real.log n) := by
    have hnon : ∀ᶠ n : ℕ in atTop, Real.log (n : ℝ) = 0 →
        f n - c * Real.log n = 0 := by
      filter_upwards [eventually_ge_atTop 2] with n hn
      exact fun hh ↦ (ne_of_gt (Real.log_pos (by exact_mod_cast hn)) hh).elim
    apply (isLittleO_iff_tendsto' hnon).mpr
    have hh := h.sub_const c
    simp only [sub_self] at hh
    apply hh.congr'
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hl0 : Real.log (n : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast hn))
    field_simp

  have hs := (he.sum_range log_nat_nonneg sum_log_tendsto_atTop).tendsto_div_nhds_zero
  have hmain := sum_log_normalized_limit.const_mul c
  have herr := hs.mul sum_log_normalized_limit
  have hout := hmain.add herr
  simp only [mul_one, zero_mul, add_zero] at hout
  apply hout.congr'
  filter_upwards [sum_log_tendsto_atTop.eventually_ne_atTop 0] with n hn
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
  field_simp
  ring

lemma cumulative_sumRep_limit {A : Set ℕ} {c : ℝ}
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c)) :
    Tendsto (fun n : ℕ ↦ (∑ i ∈ Finset.range n, (sumRep A i : ℝ)) /
      ((n : ℝ) * Real.log n)) atTop (𝓝 c) := cumulative_of_log_limit h

lemma log_double_ratio_limit :
    Tendsto (fun n : ℕ ↦ Real.log (2 * (n : ℝ)) / Real.log n) atTop (𝓝 1) := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hh := (hlog.const_div_atTop (Real.log 2)).add_const 1
  simp only [zero_add] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hl0 : Real.log (n : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast hn))
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hn0, add_div, div_self hl0]

lemma cumulative_double_sumRep_limit {A : Set ℕ} {c : ℝ}
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c)) :
    Tendsto (fun n : ℕ ↦ (∑ i ∈ Finset.range (2 * n), (sumRep A i : ℝ)) /
      ((n : ℝ) * Real.log n)) atTop (𝓝 (2 * c)) := by
  have hmul : Tendsto (fun n : ℕ ↦ 2 * n) atTop atTop :=
    tendsto_atTop_mono (fun n ↦ by change n ≤ 2 * n; omega) tendsto_id
  have hc := (cumulative_sumRep_limit h).comp hmul
  have hh := (hc.mul log_double_ratio_limit).const_mul 2
  simp only [mul_one] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hl0 : Real.log (2 * (n : ℝ)) ≠ 0 := ne_of_gt (Real.log_pos (by
    have hh : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith))
  simp only [Function.comp_apply, Nat.cast_mul, Nat.cast_ofNat]
  field_simp

/-- A witness must have its squared counting function between the two leading bounds.
This does not claim that the normalized counting function has a limit. -/
lemma normalized_count_bounds {A : Set ℕ} {c : ℝ}
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, c - ε ≤ (count A n : ℝ) ^ 2 / ((n : ℝ) * Real.log n) ∧
      (count A n : ℝ) ^ 2 / ((n : ℝ) * Real.log n) ≤ 2 * c + ε := by
  have hlo := (cumulative_sumRep_limit h).eventually (lt_mem_nhds (show c - ε < c by linarith))
  have hhi := (cumulative_double_sumRep_limit h).eventually
    (gt_mem_nhds (show 2 * c < 2 * c + ε by linarith))
  filter_upwards [hlo, hhi, eventually_ge_atTop 2] with n hnlo hnhi hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hl0 : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hden : 0 ≤ (n : ℝ) * Real.log n := (mul_pos hn0 hl0).le
  have hl : (∑ i ∈ Finset.range n, (sumRep A i : ℝ)) ≤ (count A n : ℝ) ^ 2 := by
    exact_mod_cast cumulative_le_count_sq A n
  have hu : (count A n : ℝ) ^ 2 ≤ ∑ i ∈ Finset.range (2 * n), (sumRep A i : ℝ) := by
    exact_mod_cast count_sq_le_cumulative A n
  exact ⟨hnlo.le.trans (div_le_div_of_nonneg_right hl hden),
    (div_le_div_of_nonneg_right hu hden).trans hnhi.le⟩

end Erdos66Cumulative
