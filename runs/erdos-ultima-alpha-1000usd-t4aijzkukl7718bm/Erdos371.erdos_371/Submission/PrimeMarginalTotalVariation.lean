import Submission.PrimeMarginalEndpoint

/-! Total-variation continuity of exact largest-prime-factor marginals at
comparable natural endpoints. This is not a two-coordinate estimate. -/
namespace Erdos371
open Finset Filter
open scoped Topology
set_option autoImplicit false

noncomputable def primeMarginalProbability (N p : ℕ) : ℝ :=
  (((range N).filter fun n => Nat.maxPrimeFac (n+1)=p).card : ℝ)/(N : ℝ)

noncomputable def primeMarginalL1Distance (M N : ℕ) : ℝ :=
  ∑ p ∈ range (max M N+1), |primeMarginalProbability M p-primeMarginalProbability N p|

lemma primeMarginalMean_fiber_sum (g : ℕ → ℝ) (N X : ℕ) (hNX : N ≤ X) :
    primeMarginalMean g N = ∑ p ∈ range (X+1), g p*primeMarginalProbability N p := by
  have hmap : ∀ n ∈ range N, Nat.maxPrimeFac (n+1) ∈ range (X+1) := by
    intro n hn
    have hp := Nat.maxPrimeFac_le (n := n+1)
    have hn := mem_range.mp hn
    exact mem_range.mpr (by omega)
  have hs := sum_fiberwise_of_maps_to hmap (fun n => g (Nat.maxPrimeFac (n+1)))
  have he (p : ℕ) :
      (∑ n ∈ (range N).filter (fun n => Nat.maxPrimeFac (n+1)=p), g (Nat.maxPrimeFac (n+1))) =
      (((range N).filter fun n => Nat.maxPrimeFac (n+1)=p).card : ℝ)*g p := by
    calc
      _ = ∑ _n ∈ (range N).filter (fun n => Nat.maxPrimeFac (n+1)=p), g p := by
        apply sum_congr rfl
        intro n hn
        rw [(mem_filter.mp hn).2]
      _ = _ := by simp
  simp_rw [he] at hs
  unfold primeMarginalMean primeMarginalProbability
  rw [← hs,sum_div]
  apply sum_congr rfl
  intro p _
  ring

noncomputable def primeMarginalTest (M N p : ℕ) : ℝ :=
  if primeMarginalProbability N p ≤ primeMarginalProbability M p then 1 else -1

lemma primeMarginalTest_bound (M N p : ℕ) : |primeMarginalTest M N p| ≤ 1 := by
  unfold primeMarginalTest
  split_ifs <;> norm_num

lemma primeMarginalTest_pairing (M N : ℕ) :
    primeMarginalMean (primeMarginalTest M N) M-primeMarginalMean (primeMarginalTest M N) N =
      primeMarginalL1Distance M N := by
  rw [primeMarginalMean_fiber_sum _ M (max M N) (le_max_left _ _),
    primeMarginalMean_fiber_sum _ N (max M N) (le_max_right _ _),← sum_sub_distrib]
  unfold primeMarginalL1Distance
  apply sum_congr rfl
  intro p _
  rw [← mul_sub]
  unfold primeMarginalTest
  split_ifs with h
  · rw [one_mul,abs_of_nonneg (sub_nonneg.mpr h)]
  · rw [neg_one_mul,abs_of_neg (sub_neg.mpr (lt_of_not_ge h))]

lemma primeMarginalL1Distance_nonneg (M N : ℕ) : 0 ≤ primeMarginalL1Distance M N :=
  sum_nonneg (fun _ _ => abs_nonneg _)

/-- A uniform finite bound on the full prime-value marginal, not just on
finitely many preselected observables. -/
theorem primeMarginalL1Distance_comparable_bound (K M N : ℕ)
    (hB : 1 ≤ subpowerCutoff N) (hM : 0 < M) (hMN : M ≤ N) (hNM : N ≤ K*M) :
    primeMarginalL1Distance M N ≤ (K+1 : ℝ)*primeMarginalEndpointBudget N := by
  have hh := primeMarginalMean_comparable_bound (primeMarginalTest M N) K M N
    hB hM hMN hNM (primeMarginalTest_bound M N)
  rwa [primeMarginalTest_pairing,abs_of_nonneg (primeMarginalL1Distance_nonneg M N)] at hh

/-- Exact largest-prime-factor marginal distributions at comparable
endpoints approach one another in total variation. -/
theorem primeMarginalL1Distance_comparable_zero
    (M N : ℕ → ℕ) (hM : Tendsto M atTop atTop) (hN : Tendsto N atTop atTop)
    (K : ℕ) (hc : ∀ᶠ j : ℕ in atTop, M j ≤ N j ∧ N j ≤ K*M j) :
    Tendsto (fun j => primeMarginalL1Distance (M j) (N j)) atTop (𝓝 0) := by
  have ht := primeMarginalMean_comparable_tendsto_zero
    (fun j => primeMarginalTest (M j) (N j)) (fun j => primeMarginalTest_bound (M j) (N j))
    M N hM hN K hc
  simpa only [primeMarginalTest_pairing] using ht

#print axioms primeMarginalL1Distance_comparable_zero
end Erdos371
