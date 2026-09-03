import Submission.RoughHyperbolicSuccessors
import Submission.UnitSlopeMultiplicity

/-!
# A concrete budget for the successor-sieve improvement

All parameters are fixed. The desired smoothness ratio is 180000/400020,
which would yield a multiplicity exponent above 11/20 after the arithmetic
supply is connected. This file proves only the real coefficient budgets.
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 4000000

lemma tendsto_scaled_inv_linear (a : ℝ) (ha : a ≠ 0) :
    Tendsto (fun m : ℕ => (m : ℝ)/(a*m-1)) atTop (𝓝 (1/a)) := by
  have hi : Tendsto (fun m : ℕ => 1/(m : ℝ)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hh := (tendsto_const_nhds.sub hi).inv₀ (by simpa using ha)
  simp only [sub_zero,one_div] at hh
  simp only [one_div]
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with m hm
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have he : a-(m : ℝ)⁻¹=(a*m-1)/(m : ℝ) := by field_simp
  rw [he,inv_div]

lemma tendsto_scaled_inv_square (a : ℝ) (ha : a ≠ 0) :
    Tendsto (fun m : ℕ => (m : ℝ)/(a*m)^2) atTop (𝓝 (0 : ℝ)) := by
  have hi : Tendsto (fun m : ℕ => 1/(m : ℝ)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hh := hi.const_mul (1/a^2)
  simp only [mul_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with m hm
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  field_simp

noncomputable def successorLeadingCoefficient : ℝ :=
  (2*200003/99999)*(1+1/(2 : ℝ)^10)

noncomputable def successorLongBudget (C : ℝ) (m : ℕ) : ℝ :=
  (64*400021)*(successorLeadingCoefficient+(1/1000)/Real.log 2)*
    ((m : ℝ)/(128*90000*m-1)-(m : ℝ)/(128*99999*m-1))+
      (128*400021*successorLeadingCoefficient*C/Real.log 2)*
        ((m : ℝ)/(128*90000*m)^2)

noncomputable def successorLongBudgetLimit : ℝ :=
  (64*400021)*(successorLeadingCoefficient+(1/1000)/Real.log 2)*
    (1/(128*90000)-1/(128*99999))

lemma tendsto_successorLongBudget (C : ℝ) :
    Tendsto (successorLongBudget C) atTop (𝓝 successorLongBudgetLimit) := by
  have h1 := tendsto_scaled_inv_linear (128*90000) (by norm_num)
  have h2 := tendsto_scaled_inv_linear (128*99999) (by norm_num)
  have h3 := tendsto_scaled_inv_square (128*90000) (by norm_num)
  have hh := ((h1.sub h2).const_mul
    ((64*400021)*(successorLeadingCoefficient+(1/1000)/Real.log 2))).add
      (h3.const_mul (128*400021*successorLeadingCoefficient*C/Real.log 2))
  simpa only [mul_zero,add_zero] using hh

lemma successorLongBudgetLimit_lt : successorLongBudgetLimit < 9/10 := by
  have hl : (1/2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hi : 1/Real.log 2 ≤ (2 : ℝ) := by
    have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℝ)<1/2) hl
    norm_num at hh ⊢
    exact hh
  have hsmall : (1/1000 : ℝ)/Real.log 2 ≤ 1/500 := by
    have hh := mul_le_mul_of_nonneg_left hi (show (0 : ℝ)≤1/1000 by norm_num)
    convert hh using 1 <;> ring
  unfold successorLongBudgetLimit successorLeadingCoefficient
  norm_num only [show (2 : ℝ)^10=1024 by norm_num]
  have hh := mul_le_mul_of_nonneg_left hsmall
    (show (0 : ℝ) ≤ (64*400021)*(1/(128*90000)-1/(128*99999)) by norm_num)
  nlinarith only [hh]

lemma eventually_successorLongBudget (C : ℝ) :
    ∀ᶠ m : ℕ in atTop, successorLongBudget C m ≤ 9/10 :=
  (tendsto_successorLongBudget C).eventually (eventually_le_nhds successorLongBudgetLimit_lt)

noncomputable def successorShortBudget (m : ℕ) : ℝ :=
  (64*400021)/(75*(99999 : ℝ)^2*Real.log 2)*(1/(m : ℝ))+
    (64*400021*1536)/(75*(99999 : ℝ)^2)

lemma eventually_successorShortBudget :
    ∀ᶠ m : ℕ in atTop, successorShortBudget m ≤ 3/50 := by
  have hi : Tendsto (fun m : ℕ => 1/(m : ℝ)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hh := (hi.const_mul ((64*400021)/(75*(99999 : ℝ)^2*Real.log 2))).add_const
    ((64*400021*1536)/(75*(99999 : ℝ)^2))
  simp only [mul_zero,zero_add] at hh
  exact hh.eventually (eventually_le_nhds (by norm_num :
    (64*400021*1536)/(75*(99999 : ℝ)^2) < 3/50))

lemma successorLongBudget_identity (C : ℝ) (m : ℕ) (hm : 1 ≤ m) :
    (64*400021*(m : ℝ)*Real.log 2)*
      ((successorLeadingCoefficient/(Real.log 2)^2)*
          (Real.log 2*(1/(128*90000*m-1)-1/(128*99999*m-1))+2*C/(128*90000*m)^2)+
        ((1/1000)/(Real.log 2)^2)*(1/(128*90000*m-1)-1/(128*99999*m-1))) =
      successorLongBudget C m := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (m : ℝ) ≠ 0 := ne_of_gt (by linarith)
  have h1 : (128*90000*(m : ℝ)-1) ≠ 0 := ne_of_gt (by linarith)
  have h2 : (128*99999*(m : ℝ)-1) ≠ 0 := ne_of_gt (by linarith)
  have hl : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
  unfold successorLongBudget
  field_simp
  ring

lemma successorShortBudget_identity (m : ℕ) (hm : 1 ≤ m) :
    (64*400021*(m : ℝ)*Real.log 2)*
      ((1/75)*(1+1536*(m : ℝ)*Real.log 2)/((99999 : ℝ)*m*Real.log 2)^2) =
        successorShortBudget m := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hl : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
  unfold successorShortBudget
  field_simp

end Erdos821.AnalyticSieve
