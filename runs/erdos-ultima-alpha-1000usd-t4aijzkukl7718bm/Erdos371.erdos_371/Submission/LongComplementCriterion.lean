import Submission.GrowingComplementWindow

/-! Exact remaining criterion after the growing uniformly cancelled window.
The long sum is defined arithmetically, not by subtraction, and no estimate
for its mean is asserted. -/
namespace Erdos371
open Finset Filter
open scoped Topology

noncomputable def complementAfterAt (B D U n : ℕ) : ℝ :=
  (ArithmeticFunction.moebius (roughRadical B (n*(n+1))) : ℝ)*
    ∑ e ∈ (roughRadical B (n*(n+1))).divisors,
      if U < e ∧ D*e < roughRadical B (n*(n+1)) then
        (ArithmeticFunction.moebius e : ℝ)*divisorSideColour n (roughRadical B (n*(n+1))/e) else 0

lemma roughLargeDivisorTail_prefix_add_after (B D U n : ℕ) (hn : 0 < n) (hD : 1 ≤ D) :
    roughLargeDivisorTail B D n=complementPrefixAt B D U n+complementAfterAt B D U n := by
  rw [roughLargeDivisorTail_complement B D n hn hD,sum_filter]
  unfold complementPrefixAt complementAfterAt
  rw [← mul_add,← sum_add_distrib]
  congr 1
  apply sum_congr rfl
  intro e _
  by_cases h : D*e < roughRadical B (n*(n+1))
  · by_cases he : e ≤ U
    · simp only [h,he,not_lt.mpr he,and_true,if_true,if_false,add_zero]
    · simp only [h,he,lt_of_not_ge he,and_true,if_true,if_false,zero_add]
  · simp only [h,and_false,if_false,add_zero]

/-- For the chosen cutoffs, it is exactly the mean of the displayed long
arithmetic sum that still needs to be controlled. -/
theorem density_iff_long_complement (B H U : ℕ → ℕ)
    (hH : Tendsto H atTop atTop)
    (hlog : Tendsto (fun N => Real.log (B N+1 : ℝ)/Real.log N) atTop (𝓝 0))
    (hsmall : Tendsto (fun N : ℕ =>
      (∑ n ∈ range N, roughSmallDivisorSum (B N) (H N*N) (n+1))/N) atTop (𝓝 0))
    (hshort : Tendsto (fun N : ℕ =>
      (∑ n ∈ range N, complementPrefixAt (B N) (H N*N) (U N) (n+1))/N) atTop (𝓝 0)) :
    {n | Nat.maxPrimeFac (n+1)>Nat.maxPrimeFac n}.HasDensity (1/2) ↔
      Tendsto (fun N : ℕ => (∑ n ∈ range N, complementAfterAt (B N) (H N*N) (U N) (n+1))/N)
        atTop (𝓝 0) := by
  rw [density_iff_sublinear_complement B H hH hlog hsmall]
  have hd : Tendsto (fun N : ℕ =>
      (∑ n ∈ range N, complementedRoughTail (B N) (H N) N (n+1))/N-
      (∑ n ∈ range N, complementAfterAt (B N) (H N*N) (U N) (n+1))/N) atTop (𝓝 0) := by
    apply hshort.congr'
    filter_upwards [hH.eventually_gt_atTop 0,eventually_gt_atTop (0 : ℕ)] with N hh hn
    rw [← roughLargeDivisorTail_prefix_eq_complement (B N) (H N) N hh hn]
    have he (n : ℕ) := roughLargeDivisorTail_prefix_add_after (B N) (H N*N) (U N) (n+1)
      (by omega) (Nat.mul_pos hh hn)
    simp only [he,sum_add_distrib,add_div,add_sub_cancel_right]
  constructor
  · intro h
    have ht := h.sub hd
    simp only [sub_zero] at ht
    convert ht using 1
    funext N
    ring
  · intro h
    simpa only [sub_add_cancel,add_zero] using hd.add h

/-- The remaining complementary endpoint U dominates every fixed B-power.
The long-mean vanishing on the right remains an unproved hypothesis. -/
theorem exists_growing_long_complement_criterion :
    ∃ B H U : ℕ → ℕ,
      Tendsto B atTop atTop ∧ Tendsto H atTop atTop ∧ Tendsto U atTop atTop ∧
      Tendsto (fun N => Real.log (B N+1 : ℝ)/Real.log N) atTop (𝓝 0) ∧
      Tendsto (fun N => Real.log (U N+1 : ℝ)/Real.log N) atTop (𝓝 0) ∧
      (∀ k : ℕ, ∀ᶠ N in atTop, (B N)^k ≤ U N) ∧
      Tendsto (fun N : ℕ => (U N : ℝ)*H N/N) atTop (𝓝 0) ∧
      ({n | Nat.maxPrimeFac (n+1)>Nat.maxPrimeFac n}.HasDensity (1/2) ↔
        Tendsto (fun N : ℕ => (∑ n ∈ range N, complementAfterAt (B N) (H N*N) (U N) (n+1))/N)
          atTop (𝓝 0)) := by
  obtain ⟨B,H,U,C,hB,hH,hU,hlog,hlogU,hHB,hC,hprefix,hClim,hpowers,hmax,hfrac⟩ :=
    exists_cancelled_growing_complement_window
  have hsmall : Tendsto (fun N : ℕ =>
      (∑ n ∈ range N, roughSmallDivisorSum (B N) (H N*N) (n+1))/N) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hClim
    filter_upwards [hprefix] with N hp
    rw [norm_div,Real.norm_natCast,Real.norm_eq_abs]
    exact div_le_div_of_nonneg_right (hp N) (Nat.cast_nonneg N)
  have hshort : Tendsto (fun N : ℕ =>
      (∑ n ∈ range N, complementPrefixAt (B N) (H N*N) (U N) (n+1))/N) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [hmax ε hε] with N hm
    simpa only [Real.dist_eq,sub_zero] using hm (U N) le_rfl
  exact ⟨B,H,U,hB,hH,hU,hlog,hlogU,hpowers,hfrac,
    density_iff_long_complement B H U hH hlog hsmall hshort⟩

#print axioms exists_growing_long_complement_criterion
end Erdos371
