import Submission.GeneralPatternCostsExplore
import Submission.PrefixBalancedPowerProfileExplore
import Submission.PolynomialPatternBudgetExplore

/-! Positive-pattern budgets with arbitrary probability profiles and positive
logarithmic convolution coefficients. -/
namespace Erdos66GeneralPatternPower
open Filter AdditiveCombinatorics Erdos66GeneralPatternCosts Erdos66NaturalPositivePattern
  Erdos66PrefixBalancedPowerProfile Erdos66PowerExceptionalProfile Erdos66Fractional
  Erdos66Generating Erdos66MatchingNaturalPattern Erdos66PolynomialPatternBudget
open scoped Classical Topology
set_option maxHeartbeats 1800000

 theorem exists_general_pattern_power (p : ℕ → ℝ) (hp : ∀ n, 0 ≤ p n ∧ p n ≤ 1)
    (c : ℝ) (hc : 0<c) (hconv : Tendsto (fun n ↦ sumConv p p n/Real.log n) atTop (𝓝 c))
    (P : ℕ → Pattern) (hP : ∀ S : Finset ℕ, (∑ j∈S, (P j).eval p) ≤ 1/4) :
    ∃ A : Set ℕ,
      (∀ k, |(∑ i∈Finset.range k, indicator A i)-(∑ i∈Finset.range k, p i)| ≤ 1) ∧
      (∀ S : Finset ℕ, (∑ j∈S, (P j).value (fun i ↦ decide (i∈A))) ≤ 1) ∧
      (∀ j : ℕ, Summable (fun n ↦ powerCost c (1/((j:ℝ)+1)) n (sumRep A n))) := by
  exact exists_general_pattern_rep_costs p hp P hP
    (fun j n x ↦ powerCost c (1/((j:ℝ)+1)) n x)
    (fun j n ↦ powerTail c (1/((j:ℝ)+1)) n)
    (fun j n b ↦ powerWeight c (1/((j:ℝ)+1)) n b)
    (fun j _n b ↦ powerTilt (1/((j:ℝ)+1)) b)
    (fun j n b ↦ powerWeight_nonneg _ _ _ _)
    (fun j n b ↦ powerTilt_bound _ (by positivity)
      ((div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) j])) b)
    (fun j n x ↦ powerCost_expansion _ _ _ _)
    (fun j ↦ powerTail_summable _ _ hc (by positivity))
    (fun j ↦ uniform_powerCost_bound p hp c hc hconv _ (by positivity)
      ((div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) j])))

 theorem exists_general_polynomial_patterns (p : ℕ → ℝ) (hp : ∀ n, 0 ≤ p n ∧ p n ≤ 1)
    (c : ℝ) (hc : 0<c) (hconv : Tendsto (fun n ↦ sumConv p p n/Real.log n) atTop (𝓝 c))
    (P : ℕ → Pattern) (hP : ∀ m, (P m).eval p ≤ 3*((m:ℝ)+2)) :
    ∃ (A : Set ℕ) (M : ℕ),
      (∀ k, |(∑ i∈Finset.range k, indicator A i)-(∑ i∈Finset.range k, p i)| ≤ 1) ∧
      (∀ m, (P m).value (fun i ↦ decide (i∈A)) ≤ ((m:ℝ)+M+2)^4) ∧
      (∀ j : ℕ, Summable (fun n ↦ powerCost c (1/((j:ℝ)+1)) n (sumRep A n))) := by
  obtain ⟨M,hM⟩ := exists_index_tail_budget
  let Q : ℕ → Pattern := fun m ↦ scalePattern (1/((m:ℝ)+M+2)^4) (by positivity) (P m)
  have hQ (S : Finset ℕ) : (∑ m∈S, (Q m).eval p) ≤ 1/4 := by
    apply (Finset.sum_le_sum (fun m hm ↦ ?_)).trans (hM S).le
    dsimp only [Q]
    rw [scalePattern_eval]
    have hx : 0 < (m:ℝ)+M+2 := by positivity
    calc
      _ ≤ (1/((m:ℝ)+M+2)^4)*(3*((m:ℝ)+2)) :=
        mul_le_mul_of_nonneg_left (hP m) (by positivity)
      _ ≤ (1/((m:ℝ)+M+2)^4)*(3*((m:ℝ)+M+2)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith [Nat.cast_nonneg (α := ℝ) M]
      _ = 3/((m:ℝ)+M+2)^3 := by field_simp
  obtain ⟨A,hbr,hbounds,hcost⟩ := exists_general_pattern_power p hp c hc hconv Q hQ
  refine ⟨A,M,hbr,?_,hcost⟩
  intro m
  have hh := hbounds {m}
  simp only [Finset.sum_singleton,Q,scalePattern_value] at hh
  have hx : 0 < ((m:ℝ)+M+2)^4 := by positivity
  rw [one_div,mul_comm,←div_eq_mul_inv] at hh
  exact (div_le_one hx).mp hh

end Erdos66GeneralPatternPower
