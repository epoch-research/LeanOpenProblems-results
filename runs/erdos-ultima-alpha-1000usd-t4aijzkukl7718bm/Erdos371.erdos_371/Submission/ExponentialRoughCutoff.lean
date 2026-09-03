import Submission.ExponentialAbelian
import Submission.SuperlinearRoughCutoff

/-! Uniform prefix bounds and exponential cancellation for the small rough
moduli, through a slowly superlinear cutoff. The large-divisor remainder is
not estimated in this file. -/
namespace Erdos371
open Finset Filter ExponentialWindow
open scoped Topology

noncomputable def roughPrefixBudget (B K D : ℕ) : ℝ :=
  ((2 : ℝ)^K+1)*roughNumberCount B (D+1)

lemma roughPrefixBudget_nonneg (B K D : ℕ) : 0 ≤ roughPrefixBudget B K D := by
  unfold roughPrefixBudget
  positivity

lemma roughSmallDivisorSum_prefix_budget (B K D M : ℕ) (hB : 1 ≤ B)
    (hsize : D ≤ (B+1)^K) :
    |∑ n ∈ range M, roughSmallDivisorSum B D (n+1)| ≤ roughPrefixBudget B K D := by
  simpa only [Real.norm_eq_abs, roughPrefixBudget] using
    roughSmallDivisorSum_bounded_factor_length B K D M hB hsize

/-- This estimate uses the bound on every signed prefix sum, so inserting
an exponential weight is justified by partial summation. -/
theorem roughSmallDivisorSum_exponential_bound (B K D : ℕ) (hB : 1 ≤ B)
    (hsize : D ≤ (B+1)^K) (t : ℝ) (ht : 0 < t) :
    |exponentialMean (fun n => roughSmallDivisorSum B D (n+1)) t| ≤
      roughPrefixBudget B K D*t := by
  apply exponential_mean_of_bounded_prefix _ (roughPrefixBudget_nonneg B K D) ht
  intro M
  exact roughSmallDivisorSum_prefix_budget B K D M hB hsize

lemma roughPrefixBudget_fixed_multiple_tendsto (B : ℕ → ℕ) (K H : ℕ)
    (hH : 0 < H) (hB : Tendsto B atTop atTop) :
    Tendsto (fun N : ℕ => roughPrefixBudget (B N) K (H*N)/N) atTop (𝓝 0) := by
  have hM : Tendsto (fun N : ℕ => H*N) atTop atTop := by
    apply tendsto_atTop.mpr
    intro M
    filter_upwards [eventually_ge_atTop M] with N hN
    have hle : N ≤ H*N := by nlinarith
    exact hN.trans hle
  have ht := (roughNumberCount_reindexed_succ_tendsto B (fun N => H*N) hB hM).const_mul
    (((2 : ℝ)^K+1)*H)
  simp only [mul_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  have hH0 : (H : ℝ) ≠ 0 := by exact_mod_cast hH.ne'
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold roughPrefixBudget
  push_cast
  field_simp

lemma rootRoughCutoff_multiple_size (k : ℕ) :
    ∀ᶠ N : ℕ in atTop, (k+1)*N ≤ (rootRoughCutoff k N+1)^((k+1)*2) := by
  filter_upwards [eventually_ge_atTop (k+1)] with N hN
  have hb := (rootRoughCutoff_power k N).trans (Nat.pow_le_pow_left (Nat.le_succ _) (k+1))
  calc
    (k+1)*N ≤ N*N := Nat.mul_le_mul_right N hN
    _ ≤ ((rootRoughCutoff k N+1)^(k+1))*((rootRoughCutoff k N+1)^(k+1)) := Nat.mul_le_mul hb hb
    _ = _ := by rw [pow_mul, pow_two]

/-- The diagonal enforces a single o(N) budget for ALL sampling endpoints
M, not merely the endpoint M=N. -/
theorem exists_subpower_superlinear_uniform_prefix_budget :
    ∃ B H : ℕ → ℕ, ∃ C : ℕ → ℝ,
      Tendsto B atTop atTop ∧ Tendsto H atTop atTop ∧
      Tendsto (fun N => Real.log (B N+1 : ℝ)/Real.log N) atTop (𝓝 0) ∧
      (∀ᶠ N in atTop, H N ≤ B N+1) ∧
      (∀ N, 0 ≤ C N) ∧
      (∀ᶠ N in atTop, ∀ M : ℕ,
        |∑ n ∈ range M, roughSmallDivisorSum (B N) (H N*N) (n+1)| ≤ C N) ∧
      Tendsto (fun N : ℕ => C N/N) atTop (𝓝 0) := by
  classical
  let P (N k : ℕ) : Prop := k ≤ rootRoughCutoff k N ∧ 1 ≤ rootRoughCutoff k N ∧
    (k+1)*N ≤ (rootRoughCutoff k N+1)^((k+1)*2) ∧
    Real.log (rootRoughCutoff k N+1 : ℝ)/Real.log N ≤ 2/(k+1 : ℝ) ∧
    roughPrefixBudget (rootRoughCutoff k N) ((k+1)*2) ((k+1)*N)/N ≤ 1/(k+1 : ℝ)
  have hP (k : ℕ) : ∀ᶠ N in atTop, P N k := by
    have hb := roughPrefixBudget_fixed_multiple_tendsto (rootRoughCutoff k) ((k+1)*2) (k+1)
      (by omega) (rootRoughCutoff_atTop k)
    filter_upwards [(rootRoughCutoff_atTop k).eventually_ge_atTop k,
      (rootRoughCutoff_atTop k).eventually_ge_atTop 1, rootRoughCutoff_multiple_size k,
      rootRoughCutoff_log_eventually_le k,
      hb.eventually_lt_const (show (0 : ℝ) < 1/(k+1 : ℝ) by positivity)] with N hk h1 hs hl hb
    exact ⟨hk,h1,hs,hl,hb.le⟩
  let K (N : ℕ) := Nat.findGreatest (P N) N
  let B (N : ℕ) := rootRoughCutoff (K N) N
  let H (N : ℕ) := K N+1
  let C (N : ℕ) := roughPrefixBudget (B N) (H N*2) (H N*N)
  have hK : Tendsto K atTop atTop := by
    apply tendsto_atTop.mpr
    intro k
    filter_upwards [eventually_ge_atTop k, hP k] with N hNk hp
    exact Nat.le_findGreatest hNk hp
  have hPK : ∀ᶠ N in atTop, P N (K N) := by
    filter_upwards [hP 0] with N hp
    exact Nat.findGreatest_spec (Nat.zero_le N) hp
  have hB : Tendsto B atTop atTop := by
    apply tendsto_atTop.mpr
    intro M
    filter_upwards [hPK,hK.eventually_ge_atTop M] with N hp hk
    exact hk.trans hp.1
  have hi : Tendsto (fun N => 1/(K N+1 : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hK
  refine ⟨B,H,C,hB,(tendsto_add_atTop_nat 1).comp hK,?_,?_,?_,?_,?_⟩
  · have hi2 := hi.const_mul 2
    simp only [mul_zero] at hi2
    apply squeeze_zero' (Eventually.of_forall fun N =>
      div_nonneg (Real.log_nonneg (show (1 : ℝ) ≤ B N+1 by
        have := Nat.cast_nonneg (α := ℝ) (B N); linarith)) (Real.log_natCast_nonneg N)) _ hi2
    filter_upwards [hPK] with N hp
    exact hp.2.2.2.1.trans_eq (by ring)
  · exact hPK.mono fun N hp => Nat.add_le_add_right hp.1 1
  · intro N
    exact roughPrefixBudget_nonneg _ _ _
  · filter_upwards [hPK] with N hp
    intro M
    exact roughSmallDivisorSum_prefix_budget (B N) (H N*2) (H N*N) M hp.2.1 hp.2.2.1
  · apply squeeze_zero' (Eventually.of_forall fun N =>
      div_nonneg (roughPrefixBudget_nonneg _ _ _) (Nat.cast_nonneg N)) _ hi
    exact hPK.mono fun N hp => hp.2.2.2.2

/-- There are subpower B and growing H for which the full small-modulus
sum through H*N has vanishing ordinary exponential mean at t=1/N. This
is only the small-modulus part, not the full comparison. -/
theorem exists_subpower_superlinear_exponential_cutoff :
    ∃ B H : ℕ → ℕ, Tendsto B atTop atTop ∧ Tendsto H atTop atTop ∧
      Tendsto (fun N => Real.log (B N+1 : ℝ)/Real.log N) atTop (𝓝 0) ∧
      (∀ᶠ N in atTop, H N ≤ B N+1) ∧
      Tendsto (fun N : ℕ => exponentialMean
        (fun n => roughSmallDivisorSum (B N) (H N*N) (n+1)) (1/N)) atTop (𝓝 0) := by
  obtain ⟨B,H,C,hB,hH,hlog,hHB,hC,hbound,hlim⟩ := exists_subpower_superlinear_uniform_prefix_budget
  refine ⟨B,H,hB,hH,hlog,hHB,?_⟩
  apply squeeze_zero_norm' _ hlim
  filter_upwards [hbound, eventually_gt_atTop (0 : ℕ)] with N hb hN
  have ht : (0 : ℝ) < 1/(N : ℝ) := by positivity
  have he := exponential_mean_of_bounded_prefix
    (fun n => roughSmallDivisorSum (B N) (H N*N) (n+1)) (hC N) ht hb
  simpa only [Real.norm_eq_abs, mul_one_div] using he

#print axioms roughSmallDivisorSum_exponential_bound
#print axioms exists_subpower_superlinear_uniform_prefix_budget
#print axioms exists_subpower_superlinear_exponential_cutoff
end Erdos371
