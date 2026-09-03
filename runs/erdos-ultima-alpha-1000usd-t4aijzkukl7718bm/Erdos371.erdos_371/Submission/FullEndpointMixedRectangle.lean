import Submission.FullEndpointRectangleError

/-! Signed cancellation of the mixed complementary rectangle through the
full high-factor endpoint N, with a growing subpower low-factor window. -/
namespace Erdos371
open Finset Filter FiniteSieve
open scoped Topology

theorem exists_full_endpoint_mixed_rectangle (W : ℕ → ℕ) (L : ℕ) (hL : 0 < L)
    (hW : ∀ᶠ N in atTop, 1 < W N ∧ N+1 ≤ (W N)^L) :
    ∃ B H : ℕ → ℕ, ∃ C : ℕ → ℝ,
      Tendsto B atTop atTop ∧ Tendsto H atTop atTop ∧
      Tendsto (fun N => Real.log (B N+1 : ℝ)/Real.log N) atTop (𝓝 0) ∧
      (∀ᶠ N in atTop, H N ≤ B N+1) ∧ (∀ N, 0 ≤ C N) ∧
      (∀ᶠ N in atTop, ∀ M : ℕ,
        |∑ n ∈ range M, roughSmallDivisorSum (B N) (H N*N) (n+1)| ≤ C N) ∧
      Tendsto (fun N : ℕ => C N/N) atTop (𝓝 0) ∧
      (∀ k : ℕ, ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ F ≤ (B N)^k,
        |(∑ n ∈ range N, mixedComplementRectangleAt (B N) (H N*N) (W N) F N (n+1))/N| < ε) := by
  obtain ⟨B,H,C,hBt,hHt,hB,hHB,hC,hbudget,hClim,hweighted⟩ := exists_high_weighted_prefix_cutoffs W id L hW
  refine ⟨B,H,C,hBt,hHt,hB,hHB,hC,hbudget,hClim,?_⟩
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



theorem exists_cancelled_growing_full_rectangle (W : ℕ → ℕ) (L : ℕ) (hL : 0 < L)
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
        |(∑ n ∈ range N, mixedComplementRectangleAt (B N) (H N*N) (W N) F N (n+1))/N| < ε) := by
  obtain ⟨B,H,C,hB,hH,hlog,hHB,hC,hbudget,hClim,hfixed⟩ := exists_full_endpoint_mixed_rectangle W L hL hW
  obtain ⟨K,hK,hlogU,hmax⟩ := exists_growing_rectangle_window B H W id hB hlog hfixed
  let U : ℕ → ℕ := fun N => (B N)^(K N)
  have hU : Tendsto U atTop atTop := by
    apply tendsto_atTop.mpr
    intro M
    filter_upwards [hB.eventually_ge_atTop M,hB.eventually_gt_atTop 0,hK.eventually_ge_atTop 1]
      with N hb hb0 hk
    exact hb.trans (by simpa only [pow_one] using Nat.pow_le_pow_right hb0 hk)
  have hUl : Tendsto (fun N => Real.log (U N+1 : ℝ)/Real.log N) atTop (𝓝 0) := by
    simpa only [U,Nat.cast_pow] using hlogU
  refine ⟨B,H,U,C,hB,hH,hU,hlog,hUl,hHB,hC,hbudget,hClim,?_,?_,hmax⟩
  · intro k
    filter_upwards [hB.eventually_gt_atTop 0,hK.eventually_ge_atTop k] with N hb hk
    exact Nat.pow_le_pow_right hb hk
  · simpa only [pow_one] using subpower_below_power_cutoff U W L hL hUl (hW.mono fun N h => h.2) 1


#print axioms exists_full_endpoint_mixed_rectangle
#print axioms exists_cancelled_growing_full_rectangle
end Erdos371
