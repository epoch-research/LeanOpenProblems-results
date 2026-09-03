import Submission.DensityCutoffRefinement

/-!
# Accumulated cost of the first-moment cutoff refinement

This is a limitation of the explicit sufficient refinement inequalities,
not an upper bound for the actual supply of smooth shifted primes.
-/
open Nat Finset Filter ArithmeticFunction
open scoped Classical BigOperators Topology
namespace Erdos821
open AnalyticSieve HigherDivisors

lemma smoothPrimeLogMass_le_mangoldtSum (N Y : ℕ) :
    smoothPrimeLogMass N Y ≤ mangoldtSum N := by
  calc
    _ = ∑ p ∈ smoothPrimePool N Y, vonMangoldt p := by
      apply sum_congr rfl
      intro p hp
      exact (vonMangoldt_apply_prime (Nat.mem_primesBelow.mp (mem_filter.mp hp).1).2).symm
    _ ≤ ∑ p ∈ Icc 1 N, vonMangoldt p := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro p hp
        have hh := Nat.mem_primesBelow.mp (mem_filter.mp hp).1
        exact mem_Icc.mpr ⟨hh.2.pos, by omega⟩
      · intro p _ _
        exact vonMangoldt_nonneg
    _ = _ := rfl

lemma weighted_smooth_density_le_one (N Y : ℕ) (c : ℝ)
    (hpsi : 0 < mangoldtSum N) (H : c*mangoldtSum N ≤ smoothPrimeLogMass N Y) :
    c ≤ 1 := by
  have hh := H.trans (smoothPrimeLogMass_le_mangoldtSum N Y)
  nlinarith only [hh,hpsi]

lemma eventual_weighted_smooth_density_le_one (t b : ℕ) (ht : 1 ≤ t) (c : ℝ)
    (H : ∀ᶠ m : ℕ in atTop, c*mangoldtSum (progressionScaleN (t*m)) ≤
      smoothPrimeLogMass (progressionScaleN (t*m)) (progressionScaleN (b*m))) :
    c ≤ 1 := by
  obtain ⟨m,hm,hpsi⟩ := (H.and ((progressionScaleN_mul_tendsto t ht).eventually
    eventually_mangoldt_nine_tenths)).exists
  apply weighted_smooth_density_le_one _ _ c _ hm
  have hN : (0 : ℝ)<progressionScaleN (t*m) := by unfold progressionScaleN; positivity
  linarith only [hpsi,hN]

namespace CutoffRefinementBudget

/-- The logarithmic cutoff minus the retained density is a monotone potential. -/
theorem potential_monotone (β c : ℕ → ℝ) (hβ : ∀ i, 0<β i)
    (hstep : ∀ i, Real.log (β i/β (i+1)) ≤ c i-c (i+1)) :
    Monotone (fun i => Real.log (β i)-c i) := by
  apply monotone_nat_of_le_succ
  intro i
  have hh := hstep i
  rw [Real.log_div (hβ i).ne' (hβ (i+1)).ne'] at hh
  linarith only [hh]

/-- Every finite chain is bounded away from cutoff zero by its initial density. -/
theorem cutoff_lower_bound (β c : ℕ → ℝ) (hβ : ∀ i, 0<β i)
    (hc : ∀ i, 0≤c i)
    (hstep : ∀ i, Real.log (β i/β (i+1)) ≤ c i-c (i+1)) (n : ℕ) :
    β 0*Real.exp (-c 0) ≤ β n := by
  have hh := potential_monotone β c hβ hstep (Nat.zero_le n)
  have hlog : Real.log (β 0)-c 0 ≤ Real.log (β n) := by linarith only [hh,hc n]
  have he := Real.exp_le_exp.mpr hlog
  simpa only [sub_eq_add_neg,Real.exp_add,Real.exp_log (hβ 0),Real.exp_log (hβ n)] using he

/-- In particular, a density-halving schedule cannot evade this bound. -/
theorem halving_cutoff_lower_bound (β c : ℕ → ℝ) (hβ : ∀ i, 0<β i)
    (hc : ∀ i, 0≤c i) (hhalf : ∀ i, c (i+1)=c i/2)
    (hstep : ∀ i, Real.log (β i/β (i+1)) < c i/2) (n : ℕ) :
    β 0*Real.exp (-c 0) ≤ β n := by
  apply cutoff_lower_bound β c hβ hc _ n
  intro i
  rw [hhalf i]
  linarith only [hstep i]

/-- A charged refinement sequence cannot converge to zero. -/
theorem not_tendsto_cutoff_zero (β c : ℕ → ℝ) (hβ : ∀ i, 0<β i)
    (hc : ∀ i, 0≤c i)
    (hstep : ∀ i, Real.log (β i/β (i+1)) ≤ c i-c (i+1)) :
    ¬ Tendsto β atTop (𝓝 0) := by
  intro hlim
  have hpos : 0<β 0*Real.exp (-c 0) := mul_pos (hβ 0) (Real.exp_pos _)
  obtain ⟨n,hn⟩ := (hlim.eventually (eventually_lt_nhds hpos)).exists
  exact (not_lt_of_ge (cutoff_lower_bound β c hβ hc hstep n)) hn

/-- Actual normalized prime densities are at most one, so these sufficient
conditions cannot take a sequence below its starting ratio divided by e. -/
theorem cutoff_lower_bound_of_prime_supply (β c : ℕ → ℝ) (hβ : ∀ i, 0<β i)
    (hc : ∀ i, 0≤c i)
    (hstep : ∀ i, Real.log (β i/β (i+1)) ≤ c i-c (i+1))
    (t b : ℕ) (ht : 1≤t)
    (H : ∀ᶠ m : ℕ in atTop, c 0*mangoldtSum (progressionScaleN (t*m)) ≤
      smoothPrimeLogMass (progressionScaleN (t*m)) (progressionScaleN (b*m))) (n : ℕ) :
    β 0*Real.exp (-1) ≤ β n := by
  have hc1 := eventual_weighted_smooth_density_le_one t b ht (c 0) H
  apply le_trans _ (cutoff_lower_bound β c hβ hc hstep n)
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [hc1])) (hβ 0).le

end CutoffRefinementBudget
end Erdos821
