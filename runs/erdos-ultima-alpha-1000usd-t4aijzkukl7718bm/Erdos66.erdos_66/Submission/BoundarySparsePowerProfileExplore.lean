import Submission.BoundarySparseCostsExplore
import Submission.PrefixBalancedPowerProfileExplore

/-! A harmonic rounding with weak power-saving exceptions and arbitrarily
small fixed-window boundary envelopes. -/
namespace Erdos66BoundarySparsePowerProfile
open Filter AdditiveCombinatorics Erdos66BoundarySparseCosts Erdos66BoundaryPairCounts Erdos66BoundaryPairPotential Erdos66TripleIntersectionMean
  Erdos66PrefixBalancedPowerProfile Erdos66PowerExceptionalProfile Erdos66Fractional
  Erdos66Generating Erdos66Rounding
open scoped Classical Topology
set_option maxHeartbeats 2000000

 theorem exists_boundary_sparse_power_potentials : ∃ (A : Set ℕ) (N₀ : ℕ → ℕ),
    (∀ n, |prefixSum (roundingError A) n| ≤ 1) ∧
    (∀ j n, N₀ j ≤ n →
        ((j:ℝ)+1)*((boundary A (cutoff j) n).card:ℝ) ≤ 3*ell n) ∧
    (∀ j : ℕ, Summable (fun n ↦ powerCost 1 (1/((j:ℝ)+1)) n (sumRep A n))) := by
  obtain ⟨A,N₀,hbr,hd,hcost⟩ := exists_boundary_sparse_summable_rep_costs
    (fun j n x ↦ powerCost 1 (1/((j:ℝ)+1)) n x)
    (fun j n ↦ powerTail 1 (1/((j:ℝ)+1)) n)
    (fun j n b ↦ powerWeight 1 (1/((j:ℝ)+1)) n b)
    (fun j _n b ↦ powerTilt (1/((j:ℝ)+1)) b)
    (fun j n b ↦ powerWeight_nonneg _ _ _ _)
    (fun j n b ↦ powerTilt_bound _ (by positivity)
      ((div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) j])) b)
    (fun j n x ↦ powerCost_expansion _ _ _ _)
    (fun j ↦ powerTail_summable _ _ (by norm_num) (by positivity))
    (fun j ↦ uniform_powerCost_bound profile (fun n ↦ ⟨profile_nonneg n,profile_le_one n⟩)
      1 (by norm_num) profile_log_limit _ (by positivity)
      ((div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) j])))
  refine ⟨A,N₀,?_,hd,hcost⟩
  intro n
  simpa only [prefixSum,roundingError,Finset.sum_sub_distrib] using hbr (n+1)

 theorem exists_boundary_sparse_power_exceptions : ∃ (A : Set ℕ) (N₀ : ℕ → ℕ),
    (∀ n, |prefixSum (roundingError A) n| ≤ 1) ∧
    (∀ j n, N₀ j ≤ n →
        ((j:ℝ)+1)*((boundary A (cutoff j) n).card:ℝ) ≤ 3*ell n) ∧
    (∀ ε : ℝ, 0<ε → ∃ α : ℝ, 0<α ∧ α<1 ∧ Summable (fun n : ℕ ↦
      if ε ≤ |(sumRep A n : ℝ)/Real.log n-1| then 1/((n:ℝ)+2)^(1-α : ℝ) else 0)) := by
  obtain ⟨A,N₀,hbr,hd,hcost⟩ := exists_boundary_sparse_power_potentials
  exact ⟨A,N₀,hbr,hd,power_exceptions_of_potentials A 1 (by norm_num) hcost⟩

end Erdos66BoundarySparsePowerProfile
