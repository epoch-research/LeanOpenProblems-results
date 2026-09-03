import Submission.JointHighPrefixCutoffs

/-! Common cutoffs for the actual ordinary prefix and full-high mixed
rectangle. Both estimates retain the original size condition. -/
namespace Erdos371
open Finset Filter FiniteSieve
open scoped Topology

theorem exists_joint_full_endpoint_prefixes (W : ℕ → ℕ) (L : ℕ) (hL : 0 < L)
    (hW : ∀ᶠ N in atTop, 1 < W N ∧ N+1 ≤ (W N)^L) :
    ∃ B H : ℕ → ℕ, ∃ C : ℕ → ℝ,
      Tendsto B atTop atTop ∧ Tendsto H atTop atTop ∧
      Tendsto (fun N => Real.log (B N+1 : ℝ)/Real.log N) atTop (𝓝 0) ∧
      (∀ᶠ N in atTop, H N ≤ B N+1) ∧ (∀ N, 0 ≤ C N) ∧
      (∀ᶠ N in atTop, ∀ M : ℕ,
        |∑ n ∈ range M, roughSmallDivisorSum (B N) (H N*N) (n+1)| ≤ C N) ∧
      Tendsto (fun N : ℕ => C N/N) atTop (𝓝 0) ∧
      (∀ k : ℕ, ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ F ≤ (B N)^k,
        |(∑ n ∈ range N, mixedComplementRectangleAt (B N) (H N*N) (W N) F N (n+1))/N| < ε) ∧
      (∀ k : ℕ, ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ F ≤ (B N)^k,
        |(∑ n ∈ range N, complementPrefixAt (B N) (H N*N) F (n+1))/N| < ε) := by
  obtain ⟨B,H,C,hBt,hHt,hB,hHB,hC,hbudget,hClim,hweighted,hplain⟩ := exists_joint_high_weighted_prefix_cutoffs W id L hW
  refine ⟨B,H,C,hBt,hHt,hB,hHB,hC,hbudget,hClim,?_,
    complementPrefixAt_uniform_zero_of_untruncated B H hBt hB hHB hplain⟩
  intro k ε hε
  have herr := mixed_full_endpoint_mean_error B H W k L hL hBt hB hHB hW
  filter_upwards [herr (ε/2) (by positivity),hweighted k (ε/2) (by positivity),
    eventually_gt_atTop (0 : ℕ)] with N he hw hN
  intro F hF
  have hdiff : |(∑ n ∈ range N, mixedComplementRectangleAt (B N) (H N*N) (W N) F N (n+1))/N-
      (∑ n ∈ range N, highDivisorWeight (W N) N (n+1)*untruncatedComplementPrefix (B N) F (n+1))/N| < ε/2 := by
    rw [← sub_div,← sum_sub_distrib,abs_div,abs_of_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
    exact (div_le_div_of_nonneg_right (abs_sum_le_sum_abs _ _) (Nat.cast_nonneg N)).trans_lt (he F hF)
  have htri := abs_sub_le
    ((∑ n ∈ range N, mixedComplementRectangleAt (B N) (H N*N) (W N) F N (n+1))/N)
    ((∑ n ∈ range N, highDivisorWeight (W N) N (n+1)*untruncatedComplementPrefix (B N) F (n+1))/N) 0
  simp only [sub_zero] at htri
  simp only [id_eq] at hw
  linarith [hw F hF]



theorem exists_joint_growing_full_cutoffs (W : ℕ → ℕ) (L : ℕ) (hL : 0 < L)
    (hW : ∀ᶠ N in atTop, 1 < W N ∧ N+1 ≤ (W N)^L) :
    ∃ B H U : ℕ → ℕ, ∃ C : ℕ → ℝ,
      Tendsto B atTop atTop ∧ Tendsto H atTop atTop ∧ Tendsto U atTop atTop ∧
      Tendsto (fun N => Real.log (B N+1 : ℝ)/Real.log N) atTop (𝓝 0) ∧
      Tendsto (fun N => Real.log (U N+1 : ℝ)/Real.log N) atTop (𝓝 0) ∧
      (∀ᶠ N in atTop, H N ≤ B N+1) ∧ (∀ N, 0 ≤ C N) ∧
      (∀ᶠ N in atTop, ∀ M : ℕ,
        |∑ n ∈ range M, roughSmallDivisorSum (B N) (H N*N) (n+1)| ≤ C N) ∧
      Tendsto (fun N : ℕ => C N/N) atTop (𝓝 0) ∧
      (∀ k : ℕ, ∀ᶠ N in atTop, (B N)^k ≤ U N) ∧ (∀ᶠ N in atTop, U N ≤ W N) ∧
      (∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ F ≤ U N,
        |(∑ n ∈ range N, mixedComplementRectangleAt (B N) (H N*N) (W N) F N (n+1))/N| < ε) ∧
      (∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ F ≤ U N,
        |(∑ n ∈ range N, complementPrefixAt (B N) (H N*N) F (n+1))/N| < ε) := by
  obtain ⟨B,H,C,hB,hH,hlog,hHB,hC,hbudget,hClim,hmixed,hplain⟩ := exists_joint_full_endpoint_prefixes W L hL hW
  obtain ⟨K,hK,hlogK,hmaxK⟩ := exists_growing_rectangle_window B H W id hB hlog hmixed
  obtain ⟨J,hJ,hlogJ,hmaxJ⟩ := exists_growing_complement_window B H hB hlog hplain
  let I (N : ℕ) := min (K N) (J N)
  let U (N : ℕ) := (B N)^(I N)
  have hI : Tendsto I atTop atTop := by
    apply tendsto_atTop.mpr
    intro M
    filter_upwards [hK.eventually_ge_atTop M,hJ.eventually_ge_atTop M] with N hk hj
    exact le_min hk hj
  have hU : Tendsto U atTop atTop := by
    apply tendsto_atTop.mpr
    intro M
    filter_upwards [hB.eventually_ge_atTop M,hB.eventually_gt_atTop 0,hI.eventually_ge_atTop 1] with N hb hb0 hi
    exact hb.trans (by simpa only [pow_one] using Nat.pow_le_pow_right hb0 hi)
  have hUK : ∀ᶠ N : ℕ in atTop, U N ≤ (B N)^(K N) := by
    filter_upwards [hB.eventually_gt_atTop 0] with N hb
    exact Nat.pow_le_pow_right hb (min_le_left _ _)
  have hUJ : ∀ᶠ N : ℕ in atTop, U N ≤ (B N)^(J N) := by
    filter_upwards [hB.eventually_gt_atTop 0] with N hb
    exact Nat.pow_le_pow_right hb (min_le_right _ _)
  have hlogU : Tendsto (fun N : ℕ => Real.log (U N+1 : ℝ)/Real.log N) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun N => div_nonneg
      (Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) (U N); linarith))
      (Real.log_natCast_nonneg N)) _ hlogK
    filter_upwards [hUK] with N hu
    apply div_le_div_of_nonneg_right _ (Real.log_natCast_nonneg N)
    exact Real.log_le_log (by positivity) (by exact_mod_cast Nat.add_le_add_right hu 1)
  refine ⟨B,H,U,C,hB,hH,hU,hlog,hlogU,hHB,hC,hbudget,hClim,?_,?_,?_,?_⟩
  · intro k
    filter_upwards [hB.eventually_gt_atTop 0,hI.eventually_ge_atTop k] with N hb hi
    exact Nat.pow_le_pow_right hb hi
  · simpa only [pow_one] using subpower_below_power_cutoff U W L hL hlogU (hW.mono fun N h => h.2) 1
  · intro ε hε
    filter_upwards [hmaxK ε hε,hUK] with N hm hu
    exact fun F hF => hm F (hF.trans hu)
  · intro ε hε
    filter_upwards [hmaxJ ε hε,hUJ] with N hm hu
    exact fun F hF => hm F (hF.trans hu)

#print axioms exists_joint_full_endpoint_prefixes
#print axioms exists_joint_growing_full_cutoffs
end Erdos371
