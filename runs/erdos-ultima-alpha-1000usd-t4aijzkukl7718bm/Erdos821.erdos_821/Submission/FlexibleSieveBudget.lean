import Submission.FlexibleChebyshevSpecialization

/-!
# Limits of the flexible structured-sieve sufficient conditions

The conclusions here bound only the exponents supplied by this particular
parameter family. They are NOT upper bounds on inverse-totient multiplicity
and do not disprove the original conjecture.
-/
namespace Erdos821
open AnalyticSieve

lemma chebyshevRatioConstant_lt_decimal :
    chebyshevRatioConstant < (9213/10000 : ℝ) := by
  have h6 := Real.log_div_le_sum_range_add (x := (1/11 : ℝ)) (by norm_num) (by norm_num) 3
  have h5 := Real.log_div_le_sum_range_add (x := (1/9 : ℝ)) (by norm_num) (by norm_num) 3
  norm_num [Finset.sum_range_succ] at h6 h5
  have h3 : Real.log 3 = Real.log 2+Real.log (6/5)+Real.log (5/4) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),← Real.log_mul (by norm_num) (by norm_num)]
    congr 1
    norm_num
  have h5' : Real.log 5 = 2*Real.log 2+Real.log (5/4) := by
    have h2 : Real.log ((2 : ℝ)^2) = 2*Real.log 2 := by rw [Real.log_pow]; norm_num
    rw [← h2,← Real.log_mul (by norm_num) (by norm_num)]
    congr 1
    norm_num
  rw [chebyshevRatioConstant_eq,h3,h5']
  linarith [Real.log_two_lt_d9]

/-- Normalized sufficient coefficient conditions, without a modulus-level
restriction built into the definition. -/
def FlexibleRetentionBudget (δ β κ j : ℝ) : Prop :=
  0 ≤ β ∧ 0 ≤ j ∧ j ≤ β ∧ δ+β+κ=1 ∧
    (8192/675 : ℝ)*κ ≤ chebyshevRatioConstant*j^2

lemma FlexibleRetentionBudget.cofactor_le {δ β κ j : ℝ}
    (h : FlexibleRetentionBudget δ β κ j) :
    κ ≤ (248751/3276800 : ℝ)*β^2 := by
  obtain ⟨hβ,hj,hjβ,hsum,hcoef⟩ := h
  have hsq : j^2 ≤ β^2 := pow_le_pow_left₀ hj hjβ 2
  have hc0 : 0 ≤ chebyshevRatioConstant :=
    (by norm_num : (0 : ℝ) ≤ 92129/100000).trans chebyshevRatioConstant_gt_decimal.le
  have h1 := mul_le_mul_of_nonneg_left hsq hc0
  have h2 := mul_le_mul_of_nonneg_right chebyshevRatioConstant_lt_decimal.le (sq_nonneg β)
  nlinarith only [hcoef,h1,h2]

lemma FlexibleRetentionBudget.modulus_level_required {δ β κ j : ℝ}
    (h : FlexibleRetentionBudget δ β κ j) :
    1-β-(248751/3276800 : ℝ)*β^2 ≤ δ := by
  have hk := h.cofactor_le
  have hsum := h.2.2.2.1
  linarith

/-- Even after removing the old fixed margins, cube-root smoothness would
require a modulus level greater than 0.658. -/
theorem FlexibleRetentionBudget.cube_root_requires_large_modulus {δ β κ j : ℝ}
    (h : FlexibleRetentionBudget δ β κ j) (hβ : β ≤ 1/3) :
    (6470683/9830400 : ℝ) ≤ δ := by
  have hs : β^2 ≤ (1/3 : ℝ)^2 := pow_le_pow_left₀ h.1 hβ 2
  have hd := h.modulus_level_required
  nlinarith only [hβ,hs,hd]

/-- The new budget is different from the old 27/32 budget; its cutoffs
nevertheless remain bounded away from zero at a half modulus level. -/
theorem FlexibleRetentionBudget.below_half_cutoff {δ β κ j : ℝ}
    (h : FlexibleRetentionBudget δ β κ j) (hδ : δ ≤ 1/2) :
    (48233/100000 : ℝ) < β := by
  by_contra hn
  have hβ : β ≤ (48233/100000 : ℝ) := le_of_not_gt hn
  have hs : β^2 ≤ (48233/100000 : ℝ)^2 := pow_le_pow_left₀ h.1 hβ 2
  have hd := h.modulus_level_required
  nlinarith only [hδ,hβ,hs,hd]

lemma flexible_chebyshev_parameters_retention_budget (r t b h : ℕ)
    (heq : r+b+h=t) (hrt : 2*r+1 ≤ t) (hb : 2 ≤ b)
    (hc : (8192/675 : ℝ)*(t : ℝ)*h < chebyshevRatioConstant*((b : ℝ)-1)^2) :
    FlexibleRetentionBudget ((r : ℝ)/t) ((b : ℝ)/t) ((h : ℝ)/t) (((b : ℝ)-1)/t) := by
  have ht : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hbR : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have heqR : (r : ℝ)+b+h=t := by exact_mod_cast heq
  refine ⟨by positivity,div_nonneg (by linarith) ht.le,?_,?_,?_⟩
  · exact div_le_div_of_nonneg_right (by linarith) ht.le
  · rw [← add_div,← add_div,heqR,div_self ht.ne']
  · have h := div_le_div_of_nonneg_right hc.le (sq_nonneg (t : ℝ))
    convert h using 1 <;> field_simp

/-- Every exponent threshold supplied by the flexible criterion is below
0.51767. This does not bound thresholds achievable by other methods. -/
theorem flexible_chebyshev_parameters_exponent_bound (r t b h : ℕ)
    (heq : r+b+h=t) (hrt : 2*r+1 ≤ t) (hb : 2 ≤ b)
    (hc : (8192/675 : ℝ)*(t : ℝ)*h < chebyshevRatioConstant*((b : ℝ)-1)^2) :
    1-(b : ℝ)/t < (51767/100000 : ℝ) := by
  have ht : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hr : (r : ℝ)/t ≤ 1/2 := by
    apply (div_le_iff₀ ht).mpr
    have hrtR : 2*(r : ℝ)+1 ≤ t := by exact_mod_cast hrt
    linarith
  have hcut := (flexible_chebyshev_parameters_retention_budget r t b h heq hrt hb hc).below_half_cutoff hr
  linarith only [hcut]

/-- Iterating this same budget to vanishing smoothness cutoffs would require
modulus levels tending to one, not repeated use of the half-level theorem. -/
theorem FlexibleRetentionBudget.modulus_level_tends_to_one
    (δ β κ j : ℕ → ℝ) (h : ∀ n, FlexibleRetentionBudget (δ n) (β n) (κ n) (j n))
    (hδ : ∀ n, δ n ≤ 1)
    (hβ : Filter.Tendsto β Filter.atTop (nhds 0)) :
    Filter.Tendsto δ Filter.atTop (nhds 1) := by
  have hlow : Filter.Tendsto (fun n => 1-β n-(248751/3276800 : ℝ)*(β n)^2)
      Filter.atTop (nhds 1) := by
    have ht := (hβ.const_sub 1).sub ((hβ.pow 2).const_mul (248751/3276800 : ℝ))
    simpa only [sub_zero,zero_pow (by decide : 2 ≠ 0),mul_zero] using ht
  exact hlow.squeeze tendsto_const_nhds (fun n => (h n).modulus_level_required) hδ

end Erdos821
