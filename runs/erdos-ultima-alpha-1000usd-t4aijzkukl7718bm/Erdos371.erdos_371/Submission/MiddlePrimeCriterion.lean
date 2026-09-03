import Submission.MiddlePrimeComplement

/-! The remaining equivalent target now requires a long W-smooth cofactor
and a prime in (Y,W]. The original density conclusion is still unproved. -/
namespace Erdos371
open Finset Filter FiniteSieve
open scoped Topology

theorem exists_middle_prime_complement_criterion (W : ℕ → ℕ) (L : ℕ) (hL : 0 < L)
    (hW : ∀ᶠ N : ℕ in atTop, 1 < W N ∧ N+1 ≤ (W N)^L) :
    ∃ B H U Y : ℕ → ℕ,
      Tendsto B atTop atTop ∧ Tendsto H atTop atTop ∧ Tendsto U atTop atTop ∧ Tendsto Y atTop atTop ∧
      Tendsto (fun N => Real.log (B N+1 : ℝ)/Real.log N) atTop (𝓝 0) ∧
      Tendsto (fun N => Real.log (U N+1 : ℝ)/Real.log N) atTop (𝓝 0) ∧
      (∀ᶠ N : ℕ in atTop, Y N ≤ U N ∧ U N ≤ W N) ∧
      (∀ k : ℕ, ∀ᶠ N in atTop, (B N)^k ≤ Y N) ∧
      ({n | Nat.maxPrimeFac (n+1)>Nat.maxPrimeFac n}.HasDensity (1/2) ↔
        Tendsto (fun N : ℕ => (∑ n ∈ range N,
          middlePrimeComplementAt (B N) (H N*N) (U N) (Y N) (W N) (n+1))/N) atTop (𝓝 0)) := by
  obtain ⟨B,H,U,C,hB,hH,hU,hlog,hlogU,hHB,hC,hbudget,hClim,hpowers,hUW,hmixed,hplain⟩ :=
    exists_joint_growing_full_cutoffs W L hL hW
  have hsmall : Tendsto (fun N : ℕ => (∑ n ∈ range N,
      roughSmallDivisorSum (B N) (H N*N) (n+1))/N) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hClim
    filter_upwards [hbudget] with N hp
    rw [norm_div,Real.norm_natCast,Real.norm_eq_abs]
    exact div_le_div_of_nonneg_right (hp N) (Nat.cast_nonneg N)
  have hshort : Tendsto (fun N : ℕ => (∑ n ∈ range N,
      complementPrefixAt (B N) (H N*N) (U N) (n+1))/N) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [hplain ε hε] with N hm
    simpa only [Real.dist_eq,sub_zero] using hm (U N) le_rfl
  have hmix : Tendsto (fun N : ℕ => (∑ n ∈ range N,
      mixedComplementRectangleAt (B N) (H N*N) (W N) (U N) N (n+1))/N) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [hmixed ε hε] with N hm
    simpa only [Real.dist_eq,sub_zero] using hm (U N) le_rfl
  obtain ⟨Y,hY,hYU,hYpowers,hcount⟩ := exists_smooth_complement_count_cutoff B U hB hpowers
  have hsmooth : Tendsto (fun N : ℕ => (∑ n ∈ range N,
      |smoothComplementAfterAt (B N) (H N*N) (U N) (Y N) (n+1)|)/N) atTop (𝓝 0) := by
    apply squeeze_zero (fun N => div_nonneg (sum_nonneg fun n _ => abs_nonneg _) (Nat.cast_nonneg N)) _ hcount
    intro N
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
    exact sum_le_sum fun n _ => smoothComplementAfterAt_abs_le_count _ _ _ _ _
  have hBW : ∀ᶠ N : ℕ in atTop, B N ≤ W N := by
    filter_upwards [hpowers 1,hUW] with N hb hu
    have hb' : B N ≤ U N := by simpa only [pow_one] using hb
    exact hb'.trans hu
  have hYW : ∀ᶠ N : ℕ in atTop, Y N ≤ W N := by
    filter_upwards [hYU,hUW] with N hy hu
    exact hy.trans hu
  have hcanon : (fun N : ℕ => (∑ n ∈ range N,
      uncoveredComplementAt (B N) (H N*N) (U N) (Y N) (W N) N (n+1))/N) =ᶠ[atTop]
      (fun N : ℕ => (∑ n ∈ range N,
        longLowComplementAt (B N) (H N*N) (U N) (Y N) (W N) (n+1))/N) := by
    filter_upwards [hH.eventually_ge_atTop 1,eventually_gt_atTop (0 : ℕ),hUW] with N hh hn hu
    congr 1
    apply sum_congr rfl
    intro n hnN
    exact uncoveredComplementAt_eq_longLow _ _ _ _ _ N (n+1) hh hn (by omega)
      (by have := mem_range.mp hnN; omega) hu
  have herrAbs := longLow_middle_mean_error_zero B (fun N => H N*N) U Y W L hW hcount
  have herr : Tendsto (fun N : ℕ => (∑ n ∈ range N,
      longLowComplementAt (B N) (H N*N) (U N) (Y N) (W N) (n+1))/N-
      (∑ n ∈ range N, middlePrimeComplementAt (B N) (H N*N) (U N) (Y N) (W N) (n+1))/N)
      atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ herrAbs
    apply Eventually.of_forall
    intro N
    rw [Real.norm_eq_abs,← sub_div,← sum_sub_distrib,abs_div,abs_of_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
    exact div_le_div_of_nonneg_right (abs_sum_le_sum_abs _ _) (Nat.cast_nonneg N)
  have hlast : Tendsto (fun N : ℕ => (∑ n ∈ range N,
      uncoveredComplementAt (B N) (H N*N) (U N) (Y N) (W N) N (n+1))/N) atTop (𝓝 0) ↔
      Tendsto (fun N : ℕ => (∑ n ∈ range N,
        middlePrimeComplementAt (B N) (H N*N) (U N) (Y N) (W N) (n+1))/N) atTop (𝓝 0) := by
    constructor
    · intro h
      have ht := (h.congr' hcanon).sub herr
      simp only [sub_zero] at ht
      convert ht using 1
      funext N
      ring
    · intro h
      have ht := herr.add h
      simp only [sub_add_cancel,add_zero] at ht
      exact ht.congr' hcanon.symm
  refine ⟨B,H,U,Y,hB,hH,hU,hY,hlog,hlogU,?_,hYpowers,?_⟩
  · filter_upwards [hYU,hUW] with N hy hu
    exact ⟨hy,hu⟩
  · exact (density_iff_long_complement B H U hH hlog hsmall hshort).trans
      ((long_complement_zero_iff_escaping B (fun N => H N*N) U Y hU hsmooth).trans
        ((escaping_zero_iff_uncovered B H U Y W hBW hUW hYW hmix).trans hlast))

#print axioms exists_middle_prime_complement_criterion
end Erdos371
