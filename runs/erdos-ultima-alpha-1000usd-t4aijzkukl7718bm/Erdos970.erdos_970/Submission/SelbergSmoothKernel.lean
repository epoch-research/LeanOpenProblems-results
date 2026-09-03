import Submission.SelbergSmoothCost

/-! The smooth-support mean bound applied to the exact canonical coefficient norm. -/
namespace Erdos970.FiniteSelberg
open Finset Real
set_option maxHeartbeats 0
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def smoothCostConstant : ℝ := exp 2+exp 20
lemma smoothCostConstant_pos : 0 < smoothCostConstant := by unfold smoothCostConstant; positivity

lemma canonical_cost_le_smooth (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (Y R : ℕ) (hY : 1 ≤ log (Y : ℝ))
    (hpY : ∀ i, p i ≤ Y) (hR : 0 < R) :
    kernelCost (fun i => 1/(p i : ℝ))
      (canonicalOrthogonal (fun i => 1/(p i : ℝ)) (divisorSupport p R)) ≤
      smoothCostConstant*(R : ℝ)*exp (-log (R : ℝ)/(2*log (Y : ℝ)))/
        normalizer (fun i => 1/(p i : ℝ)) (divisorSupport p R) := by
  have hq := prime_marginals p hp
  rw [kernelCost_canonical _ hq _ (divisorSupport_nonempty p R hR)]
  apply div_le_div_of_nonneg_right _ (normalizer_pos _ hq _ (divisorSupport_nonempty p R hR)).le
  have hf (i : ι) : (1+1/(p i : ℝ))/(1-1/(p i : ℝ)) = primeCostWeight (p i) := by
    have hp0 : (p i : ℝ) ≠ 0 := by exact_mod_cast (hp i).ne_zero
    unfold primeCostWeight
    field_simp
  simp_rw [hf]
  exact smooth_divisor_cost_sum_le p hp hinj Y R hY hpY hR

#print axioms canonical_cost_le_smooth
end Erdos970.FiniteSelberg
