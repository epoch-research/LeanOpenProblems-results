import Submission.TopBandSkewBound

/-! Signed band-kernel cancellation for cutoffs of logarithmic exponent
 tending to one. This does not include fixed exponents strictly below one. -/

namespace Erdos371
open Filter
open FiniteSieve

lemma nearLinear_cutoff_eventually_ge_power (B : ℕ → ℕ) (hB : ∀ N, 1 ≤ B N)
    (hlog : Tendsto (fun N : ℕ => Real.log (B N)/Real.log N) atTop (nhds 1))
    (u : ℝ) (hu : 0 < u) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ)^(1-u) ≤ B N := by
  filter_upwards [hlog.eventually (lt_mem_nhds (show 1-u < (1 : ℝ) by linarith)),
    eventually_gt_atTop (1 : ℕ)] with N hr hN
  have hn0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hb0 : (0 : ℝ) < B N := by exact_mod_cast (show 0 < B N from lt_of_lt_of_le Nat.zero_lt_one (hB N))
  have hlN : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  apply (Real.log_le_log_iff (Real.rpow_pos_of_pos hn0 _) hb0).mp
  rw [Real.log_rpow hn0]
  exact ((lt_div_iff₀ hlN).mp hr).le

lemma nearLinear_cutoff_eventually_above_sqrt (B : ℕ → ℕ) (hB : ∀ N, 1 ≤ B N)
    (hlog : Tendsto (fun N : ℕ => Real.log (B N)/Real.log N) atTop (nhds 1)) :
    ∀ᶠ N : ℕ in atTop, N+1 ≤ (B N)^2 := by
  filter_upwards [hlog.eventually (lt_mem_nhds (by norm_num : (1/2 : ℝ) < 1)),
    eventually_gt_atTop (1 : ℕ)] with N hr hN
  have hb0 : (0 : ℝ) < B N := by exact_mod_cast (show 0 < B N from lt_of_lt_of_le Nat.zero_lt_one (hB N))
  have hlN : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  have hh := (lt_div_iff₀ hlN).mp hr
  by_contra h
  have hs : (B N)^2 ≤ N := by omega
  have hs' : (B N : ℝ)^2 ≤ N := by exact_mod_cast hs
  have hlogs := Real.log_le_log (pow_pos hb0 2) hs'
  rw [Real.log_pow] at hlogs
  norm_num at hlogs
  linarith

/-- An actual signed cancellation theorem in the exponent-one boundary
regime. The constant positive-power interior remains outside its scope. -/
theorem nearLinear_band_kernel_cancellation (B C : ℕ → ℕ)
    (hB : ∀ N, 1 ≤ B N) (hBC : ∀ N, B N ≤ C N)
    (hlog : Tendsto (fun N : ℕ => Real.log (B N)/Real.log N) atTop (nhds 1)) :
    Tendsto (fun N : ℕ => divisorSkewKernel (primeBandMoebius (B N) (C N))
      (properRoughMoebius (C N)) N/N) atTop (nhds 0) := by
  have hK : 0 ≤ largePairConstant := by unfold largePairConstant; positivity
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let u := min (1/8) (ε/(4*(largePairConstant+1)))
  have hu : 0 < u := lt_min (by norm_num) (by positivity)
  have hu1 : u ≤ 1/8 := min_le_left _ _
  have huε : u ≤ ε/(4*(largePairConstant+1)) := min_le_right _ _
  have hsmall : largePairConstant*u^2 ≤ ε/4 := by
    have h := (le_div_iff₀ (show 0 < 4*(largePairConstant+1) by positivity)).mp huε
    have hs : u^2 ≤ u := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hs hK
    nlinarith
  have hc : ∀ᶠ N : ℕ in atTop, 1 ≤ B N ∧ B N ≤ C N ∧ (N : ℝ)^(1-u) ≤ B N := by
    filter_upwards [nearLinear_cutoff_eventually_ge_power B hB hlog u hu] with N hn
    exact ⟨hB N,hBC N,hn⟩
  filter_upwards [band_kernel_top_eventually_le B C u hu.le hu1 hc (ε/2) (by positivity)] with N hn
  rw [Real.dist_eq,sub_zero,abs_div,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) N)]
  linarith

theorem smoothCutoffSkew_nearLinear_cancellation (B C : ℕ → ℕ)
    (hB : ∀ N, 1 ≤ B N) (hBC : ∀ N, B N ≤ C N)
    (hlog : Tendsto (fun N : ℕ => Real.log (B N)/Real.log N) atTop (nhds 1)) :
    Tendsto (fun N : ℕ => smoothCutoffSkew (B N) (C N) N/N) atTop (nhds 0) := by
  exact (smoothCutoffSkew_cancellation_iff B C hB hBC).mpr
    (nearLinear_band_kernel_cancellation B C hB hBC hlog)

theorem primeBandDiscrepancy_nearLinear_cancellation (B C : ℕ → ℕ)
    (hB : ∀ N, 1 ≤ B N) (hBC : ∀ N, B N ≤ C N)
    (hlog : Tendsto (fun N : ℕ => Real.log (B N)/Real.log N) atTop (nhds 1)) :
    Tendsto (fun N : ℕ => primeBandDiscrepancy (B N) (C N) N/N) atTop (nhds 0) := by
  apply (nearLinear_band_kernel_cancellation B C hB hBC hlog).congr'
  filter_upwards [nearLinear_cutoff_eventually_above_sqrt B hB hlog] with N hs
  rw [divisorSkewKernel_above_sqrt (B N) (C N) N (hBC N) hs]

#print axioms nearLinear_band_kernel_cancellation
#print axioms primeBandDiscrepancy_nearLinear_cancellation
end Erdos371
