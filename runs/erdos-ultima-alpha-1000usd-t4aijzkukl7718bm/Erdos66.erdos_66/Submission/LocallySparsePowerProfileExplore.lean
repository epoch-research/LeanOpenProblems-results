import Submission.LocallySparseCostsExplore
import Submission.PrefixBalancedPowerProfileExplore

/-! One harmonic rounding simultaneously has bounded prefix discrepancy,
summable two-sided power potentials, and logarithmic local difference counts. -/
namespace Erdos66LocallySparsePowerProfile
open Filter AdditiveCombinatorics Erdos66LocallySparseCosts Erdos66LocalDifferencePotential
  Erdos66PrefixBalancedPowerProfile Erdos66PowerExceptionalProfile Erdos66Fractional
  Erdos66Generating Erdos66Rounding
open scoped Classical Topology
set_option maxHeartbeats 2000000

 theorem exists_locally_sparse_power_potentials : ∃ (A : Set ℕ) (N₀ : ℕ),
    (∀ n, |prefixSum (roundingError A) n| ≤ 1) ∧
    (∀ N d, N₀ ≤ N → 0<d → (localDiff A N d : ℝ) ≤ 24*Real.log ((N:ℝ)+2)) ∧
    (∀ j : ℕ, Summable (fun n ↦ powerCost 1 (1/((j:ℝ)+1)) n (sumRep A n))) := by
  obtain ⟨A,N₀,hbr,hd,hcost⟩ := exists_locally_sparse_summable_rep_costs
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

 theorem exists_locally_sparse_power_exceptions : ∃ (A : Set ℕ) (N₀ : ℕ),
    (∀ n, |prefixSum (roundingError A) n| ≤ 1) ∧
    (∀ N d, N₀ ≤ N → 0<d → (localDiff A N d : ℝ) ≤ 24*Real.log ((N:ℝ)+2)) ∧
    (∀ ε : ℝ, 0<ε → ∃ α : ℝ, 0<α ∧ α<1 ∧ Summable (fun n : ℕ ↦
      if ε ≤ |(sumRep A n : ℝ)/Real.log n-1| then 1/((n:ℝ)+2)^(1-α : ℝ) else 0)) := by
  obtain ⟨A,N₀,hbr,hd,hcost⟩ := exists_locally_sparse_power_potentials
  exact ⟨A,N₀,hbr,hd,power_exceptions_of_potentials A 1 (by norm_num) hcost⟩

end Erdos66LocallySparsePowerProfile
