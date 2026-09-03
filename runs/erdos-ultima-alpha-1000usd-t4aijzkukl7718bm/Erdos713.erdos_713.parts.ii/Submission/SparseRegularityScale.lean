import FormalConjecturesUtil
import Submission.PolynomialRateCriterion

/-! The standard dense error budget cannot certify a fixed relative error
for a subquadratic pure-power sequence. This says nothing about the actual
error of a particular partition and does not settle Erdős 713. -/
open Filter Asymptotics
open scoped Topology
namespace Erdos713SparseRegularityScale
open Erdos713PolynomialRate

lemma density_tendsto_zero {f : ℕ → ℝ} {α c : ℝ} (hα : α < 2)
    (hf : f ~[atTop] (fun n : ℕ => c * (n : ℝ)^α)) :
    Tendsto (fun n : ℕ => f n / (n : ℝ)^2) atTop (𝓝 0) := by
  have hp : Tendsto (fun n : ℕ => (n : ℝ)^(α-2)) atTop (𝓝 0) := by
    simpa only [neg_sub] using
      (tendsto_rpow_neg_atTop (sub_pos.mpr hα)).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  have ht := (ratio_limit hf).mul hp
  simp only [mul_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hx : 0 < (n : ℝ) := by exact_mod_cast hn
  rw [Real.rpow_sub hx,Real.rpow_two]
  field_simp [(Real.rpow_pos_of_pos hx α).ne']

theorem fixed_budget_dominates {f : ℕ → ℝ} {α c ε : ℝ} (hα : α < 2)
    (hf : f ~[atTop] (fun n : ℕ => c * (n : ℝ)^α)) (hε : 0 < ε) (K : ℝ) :
    ∀ᶠ n : ℕ in atTop, K * f n < ε * (n : ℝ)^2 := by
  have ht : Tendsto (fun n : ℕ => K * (f n / (n : ℝ)^2)) atTop (𝓝 0) := by
    simpa only [mul_zero] using (density_tendsto_zero hα hf).const_mul K
  filter_upwards [ht.eventually (gt_mem_nhds hε),eventually_gt_atTop (0 : ℕ)] with n hn hpos
  have hx : 0 < (n : ℝ)^2 := sq_pos_of_pos (by exact_mod_cast hpos)
  apply (div_lt_iff₀ hx).mp
  simpa only [mul_div_assoc] using hn

theorem no_fixed_relative_budget {f : ℕ → ℝ} {α c ε : ℝ} (hα : α < 2)
    (hf : f ~[atTop] (fun n : ℕ => c * (n : ℝ)^α)) (hε : 0 < ε) :
    ¬ ∃ K : ℝ, ∀ᶠ n : ℕ in atTop, ε * (n : ℝ)^2 ≤ K * f n := by
  rintro ⟨K,hK⟩
  obtain ⟨n,hn,hlt⟩ := (hK.and (fixed_budget_dominates hα hf hε K)).exists
  exact (not_lt_of_ge hn) hlt

/-- If this dense budget is required to be a fixed multiple of f, its
nonnegative parameter must tend to zero. -/
theorem parameter_tendsto_zero {f ε : ℕ → ℝ} {α c K : ℝ} (hα : α < 2)
    (hf : f ~[atTop] (fun n : ℕ => c * (n : ℝ)^α))
    (hε : ∀ᶠ n : ℕ in atTop, 0 ≤ ε n)
    (hbound : ∀ᶠ n : ℕ in atTop, ε n * (n : ℝ)^2 ≤ K * f n) :
    Tendsto ε atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => K * (f n / (n : ℝ)^2)) atTop (𝓝 0) := by
    simpa only [mul_zero] using (density_tendsto_zero hα hf).const_mul K
  apply squeeze_zero' hε ?_ ht
  filter_upwards [hbound,eventually_gt_atTop (0 : ℕ)] with n hn hpos
  have hx : 0 < (n : ℝ)^2 := sq_pos_of_pos (by exact_mod_cast hpos)
  rw [← mul_div_assoc]
  exact (le_div_iff₀ hx).mpr hn

#print axioms density_tendsto_zero
#print axioms no_fixed_relative_budget
#print axioms parameter_tendsto_zero
end Erdos713SparseRegularityScale
