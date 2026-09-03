import Submission.PatternSparseCostsExplore
import Submission.PrefixBalancedPowerProfileExplore

/-! Arbitrary budgeted positive finite patterns imposed on one harmonic
rounding with all reciprocal-integer two-sided power potentials. -/
namespace Erdos66PatternSparsePowerProfile
open Filter AdditiveCombinatorics Erdos66PatternSparseCosts Erdos66NaturalPositivePattern
  Erdos66PrefixBalancedPowerProfile Erdos66PowerExceptionalProfile Erdos66Fractional
  Erdos66Generating Erdos66Rounding
open scoped Classical Topology
set_option maxHeartbeats 1600000

 theorem exists_pattern_sparse_power_potentials (P : ℕ → Pattern)
    (hP : ∀ S : Finset ℕ, (∑ j∈S, (P j).eval profile) ≤ 1/4) :
    ∃ A : Set ℕ,
      (∀ n, |prefixSum (roundingError A) n| ≤ 1) ∧
      (∀ S : Finset ℕ, (∑ j∈S, (P j).value (fun i ↦ decide (i∈A))) ≤ 1) ∧
      (∀ j : ℕ, Summable (fun n ↦ powerCost 1 (1/((j:ℝ)+1)) n (sumRep A n))) := by
  obtain ⟨A,hbr,hpat,hcost⟩ := exists_pattern_sparse_summable_rep_costs P hP
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
  refine ⟨A,?_,hpat,hcost⟩
  intro n
  simpa only [prefixSum,roundingError,Finset.sum_sub_distrib] using hbr (n+1)

 theorem exists_indexed_pattern_power_potentials {α : Type*} [Denumerable α] (P : α → Pattern)
    (hP : ∀ S : Finset α, (∑ j∈S, (P j).eval profile) ≤ 1/4) :
    ∃ A : Set ℕ,
      (∀ n, |prefixSum (roundingError A) n| ≤ 1) ∧
      (∀ S : Finset α, (∑ j∈S, (P j).value (fun i ↦ decide (i∈A))) ≤ 1) ∧
      (∀ j : ℕ, Summable (fun n ↦ powerCost 1 (1/((j:ℝ)+1)) n (sumRep A n))) := by
  let e := Denumerable.eqv α
  have hnat (S : Finset ℕ) : (∑ j∈S, (P (e.symm j)).eval profile) ≤ 1/4 := by
    have hh := hP (S.image e.symm)
    rw [Finset.sum_image e.symm.injective.injOn] at hh
    exact hh
  obtain ⟨A,hbr,hpat,hcost⟩ := exists_pattern_sparse_power_potentials (fun n ↦ P (e.symm n)) hnat
  refine ⟨A,hbr,?_,hcost⟩
  intro S
  have hh := hpat (S.image e)
  rw [Finset.sum_image e.injective.injOn] at hh
  simpa only [Equiv.symm_apply_apply] using hh

end Erdos66PatternSparsePowerProfile
