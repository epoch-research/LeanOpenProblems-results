import Submission.RoundingExplore

/-! Sublogarithmic prefix discrepancy, rather than bounded discrepancy,
already makes the mixed term in harmonic-profile rounding negligible.
The quadratic error estimate is still a separate, unproved construction task. -/
namespace Erdos66SublogDiscrepancy
open Filter AdditiveCombinatorics Erdos66Fractional Erdos66Generating Erdos66Rounding
open scoped Topology

lemma real_harmonic_monotone : Monotone (fun n : ℕ ↦ (harmonic n : ℝ)) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [harmonic_succ,Rat.cast_add]
  exact le_add_of_nonneg_right (by positivity)

lemma stepMass_convolution_envelope (f : ℕ → ℝ) (ε D : ℝ) (hε : 0 ≤ ε) (hD : 0 ≤ D)
    (hf : ∀ n, |f n| ≤ ε*(harmonic n : ℝ)+D) (n : ℕ) :
    |sumConv f stepMass n| ≤ ε*(harmonic n : ℝ)+D := by
  have hB : 0 ≤ ε*(harmonic n : ℝ)+D := add_nonneg (mul_nonneg hε (harmonic_nonneg n)) hD
  calc
    _ ≤ ∑ ij ∈ Finset.antidiagonal n, |f ij.1*stepMass ij.2| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ ij ∈ Finset.antidiagonal n, (ε*(harmonic n : ℝ)+D)*stepMass ij.2 := by
      apply Finset.sum_le_sum
      intro ij hij
      rw [abs_mul,abs_of_nonneg (stepMass_nonneg _)]
      have he := Finset.mem_antidiagonal.mp hij
      have hm := mul_le_mul_of_nonneg_left (real_harmonic_monotone (show ij.1 ≤ n by omega)) hε
      exact mul_le_mul_of_nonneg_right ((hf ij.1).trans (by linarith)) (stepMass_nonneg _)
    _ = (ε*(harmonic n : ℝ)+D)*∑ i∈Finset.range (n+1), stepMass i := by
      rw [← Finset.mul_sum,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      congr 1
      simpa only [Nat.add_sub_cancel] using Finset.sum_range_reflect stepMass (n+1)
    _ ≤ _ := (mul_le_mul_of_nonneg_left (stepMass_partial_le_one _) hB).trans_eq (mul_one _)

lemma mixed_harmonic_envelope (e : ℕ → ℝ) (ε D : ℝ) (hε : 0 ≤ ε) (hD : 0 ≤ D)
    (he : ∀ n, |prefixSum e n| ≤ ε*(harmonic n : ℝ)+D) (n : ℕ) :
    |sumConv e profile n| ≤ 2*(ε*(harmonic n : ℝ)+D) := by
  rw [mixed_convolution_identity]
  have hh := stepMass_convolution_envelope (prefixSum e) ε D hε hD he n
  exact (abs_sub _ _).trans (by linarith [he n])

/-- A prefix discrepancy o(log n) suffices to eliminate the mixed rounding
term after logarithmic normalization. -/
theorem mixed_log_limit_of_sublog_prefix (e : ℕ → ℝ)
    (he : Tendsto (fun n ↦ prefixSum e n/Real.log n) atTop (𝓝 0)) :
    Tendsto (fun n ↦ sumConv e profile n/Real.log n) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨D,hD,hbound⟩ := global_harmonic_error he (show 0<ε/8 by positivity)
  simp only [zero_mul,sub_zero] at hbound
  have hlog : Tendsto (fun n : ℕ ↦ Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall := (hlog.const_div_atTop D).eventually_lt_const (show 0<ε/8 by positivity)
  have hH := harmonic_log_ratio.eventually_lt_const (by norm_num : (1:ℝ)<2)
  filter_upwards [hsmall,hH,eventually_ge_atTop 2] with n hn hHn hn2
  rw [Real.dist_eq,sub_zero]
  have hl : 0<Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast hn2)
  have hb := mixed_harmonic_envelope e (ε/8) D (by positivity) hD hbound n
  rw [abs_div,abs_of_pos hl]
  calc
    _ ≤ 2*((ε/8)*(harmonic n : ℝ)+D)/Real.log n := div_le_div_of_nonneg_right hb hl.le
    _ = 2*((ε/8)*((harmonic n : ℝ)/Real.log n)+D/Real.log n) := by ring
    _ < ε := by
      have hh := mul_le_mul_of_nonneg_left hHn.le (show 0≤ε/8 by positivity)
      nlinarith

/-- The exact quadratic-error criterion remains valid in the larger class
of sublogarithmic-prefix-discrepancy roundings. -/
theorem sublog_prefix_limit_iff_quadratic_error (A : Set ℕ)
    (hprefix : Tendsto (fun n ↦ prefixSum (roundingError A) n/Real.log n) atTop (𝓝 0)) :
    Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 1) ↔
      Tendsto (fun n ↦ sumConv (roundingError A) (roundingError A) n/Real.log n)
        atTop (𝓝 0) := by
  have hm := (mixed_log_limit_of_sublog_prefix (roundingError A) hprefix).const_mul 2
  simp only [mul_zero] at hm
  constructor
  · intro hA
    have hh := (hA.sub harmonic_shift_log_ratio).sub hm
    simp only [sub_self] at hh
    apply hh.congr'
    exact Eventually.of_forall (fun n ↦ by dsimp only; rw [rounding_decomposition]; ring)
  · intro he
    have hh := (harmonic_shift_log_ratio.add hm).add he
    simp only [add_zero] at hh
    apply hh.congr'
    exact Eventually.of_forall (fun n ↦ by dsimp only; rw [rounding_decomposition]; ring)

/-- A sufficient rounding criterion, with both estimates explicitly required.
No rounding satisfying the quadratic estimate is constructed here. -/
theorem sublog_rounding_suffices
    (h : ∃ A : Set ℕ,
      Tendsto (fun n ↦ prefixSum (roundingError A) n/Real.log n) atTop (𝓝 0) ∧
      Tendsto (fun n ↦ sumConv (roundingError A) (roundingError A) n/Real.log n) atTop (𝓝 0)) :
    ∃ (A : Set ℕ) (c : ℝ), c≠0 ∧
      Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c) := by
  obtain ⟨A,hA,hq⟩ := h
  exact ⟨A,1,one_ne_zero,(sublog_prefix_limit_iff_quadratic_error A hA).mpr hq⟩

end Erdos66SublogDiscrepancy
