import Submission.PrefixBalancedExponentialCostsExplore
import Submission.PowerExceptionalProfileExplore

/-! Two-sided power-saving exceptional profiles, now with bounded prefix
rounding discrepancy. This still permits infinitely many exceptional targets. -/
namespace Erdos66PrefixBalancedPowerProfile
open Filter AdditiveCombinatorics Erdos66PrefixBalancedExponentialCosts
  Erdos66PowerExceptionalProfile Erdos66BiasedTailPotential Erdos66ScaledFractionalTail
  Erdos66Generating Erdos66Rounding
open scoped Classical Topology
set_option maxHeartbeats 2200000

noncomputable def powerTilt (δ : ℝ) (b : Bool) : ℝ := if b then δ/16 else -(δ/16)
noncomputable def powerWeight (c δ : ℝ) (n : ℕ) (b : Bool) : ℝ :=
  ((n:ℝ)+2)^(saving c δ)/((n:ℝ)+2)*
    Real.exp (if b then -(δ/16)*(c*Real.log n+δ*(c*Real.log n))
      else (δ/16)*(c*Real.log n-δ*(c*Real.log n)))

lemma powerTilt_bound (δ : ℝ) (hδ : 0≤δ) (hδ1 : δ≤1) (b : Bool) : |powerTilt δ b|≤1/2 := by
  cases b <;> simp only [powerTilt,Bool.false_eq_true,if_false,if_true,abs_neg,
    abs_of_nonneg (show 0≤δ/16 by positivity)] <;> linarith

lemma powerWeight_nonneg (c δ : ℝ) (n : ℕ) (b : Bool) : 0≤powerWeight c δ n b := by
  unfold powerWeight
  exact mul_nonneg (div_nonneg (Real.rpow_nonneg (by positivity) _) (by positivity)) (Real.exp_pos _).le

lemma powerCost_expansion (c δ : ℝ) (n : ℕ) (x : ℝ) :
    powerCost c δ n x=∑ b : Bool, powerWeight c δ n b*Real.exp (powerTilt δ b*x) := by
  have hp : Real.exp (-(δ/16)*(c*Real.log n+δ*(c*Real.log n)))*Real.exp ((δ/16)*x)=
      Real.exp ((δ/16)*(x-c*Real.log n-δ*(c*Real.log n))) := by
    rw [←Real.exp_add]; congr 1; ring
  have hm : Real.exp ((δ/16)*(c*Real.log n-δ*(c*Real.log n)))*Real.exp (-(δ/16)*x)=
      Real.exp (-(δ/16)*(x-c*Real.log n+δ*(c*Real.log n))) := by
    rw [←Real.exp_add]; congr 1; ring
  simp only [powerCost,potential,powerWeight,powerTilt,Fintype.sum_bool,if_true,
    Bool.false_eq_true,if_false,mul_assoc,hp,hm]
  ring

 theorem exists_balanced_power_potentials (p : ℕ → ℝ) (hp : ∀ n, 0≤p n ∧ p n≤1)
    (c : ℝ) (hc : 0<c)
    (hconv : Tendsto (fun n ↦ sumConv p p n/Real.log n) atTop (𝓝 c)) :
    ∃ A : Set ℕ,
      (∀ k, |(∑ i∈Finset.range k, indicator A i)-(∑ i∈Finset.range k, p i)|≤1) ∧
      (∀ j : ℕ, Summable (fun n ↦ powerCost c (1/((j:ℝ)+1)) n (sumRep A n))) := by
  apply exists_balanced_summable_rep_costs p hp
    (fun j n x ↦ powerCost c (1/((j:ℝ)+1)) n x)
    (fun j n ↦ powerTail c (1/((j:ℝ)+1)) n)
    (fun j n b ↦ powerWeight c (1/((j:ℝ)+1)) n b)
    (fun j _n b ↦ powerTilt (1/((j:ℝ)+1)) b)
  · intro j n b
    exact powerWeight_nonneg _ _ _ _
  · intro j n b
    exact powerTilt_bound _ (by positivity)
      ((div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) j])) b
  · intro j n x
    exact powerCost_expansion _ _ _ _
  · intro j
    exact powerTail_summable _ _ hc (by positivity)
  · intro j
    exact uniform_powerCost_bound p hp c hc hconv _ (by positivity)
      ((div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) j]))

 theorem exists_harmonic_rounding_with_power_exceptions :
    ∃ A : Set ℕ,
      (∀ n, |prefixSum (roundingError A) n|≤1) ∧
      (∀ ε : ℝ, 0<ε → ∃ α : ℝ, 0<α ∧ α<1 ∧ Summable (fun n : ℕ ↦
        if ε≤|(sumRep A n : ℝ)/Real.log n-1| then 1/((n:ℝ)+2)^(1-α : ℝ) else 0)) := by
  obtain ⟨A,hbr,hA⟩ := exists_balanced_power_potentials Erdos66Fractional.profile
    (fun n ↦ ⟨Erdos66Fractional.profile_nonneg n,Erdos66Fractional.profile_le_one n⟩)
    1 (by norm_num) Erdos66Fractional.profile_log_limit
  refine ⟨A,?_,power_exceptions_of_potentials A 1 (by norm_num) hA⟩
  intro n
  simpa only [prefixSum,roundingError,Finset.sum_sub_distrib] using hbr (n+1)

end Erdos66PrefixBalancedPowerProfile
