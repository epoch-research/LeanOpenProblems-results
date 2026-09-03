import Submission.ProductCofactorHyperbolicBound
import Submission.SuccessorSupplyScales

/-!
# A two-range product-sieve budget below one
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 3000000

noncomputable def productSupplyFirstCoefficient : ℝ :=
  (2*200003/106376)*(1+1/(2 : ℝ)^10)
noncomputable def productSupplySecondCoefficient : ℝ :=
  (2*400003/199999)*(1+1/(2 : ℝ)^10)

noncomputable def productSupplyLongBudget (A : ℝ) (u v : ℕ) (C : ℝ) (m : ℕ) : ℝ :=
  (64*400021)*(A+(1/1000000)/Real.log 2)*
    ((m : ℝ)/(128*(u : ℝ)*m-1)-(m : ℝ)/(128*(v : ℝ)*m-1))+
      (128*400021*A*C/Real.log 2)*((m : ℝ)/(128*(u : ℝ)*m)^2)

noncomputable def productSupplyLongLimit (A : ℝ) (u v : ℕ) : ℝ :=
  (64*400021)*(A+(1/1000000)/Real.log 2)*(1/(128*(u : ℝ))-1/(128*(v : ℝ)))

lemma tendsto_productSupplyLongBudget (A C : ℝ) (u v : ℕ) (hu : 1 ≤ u) (hv : 1 ≤ v) :
    Tendsto (productSupplyLongBudget A u v C) atTop (𝓝 (productSupplyLongLimit A u v)) := by
  have hu0 : (128*(u : ℝ)) ≠ 0 := by positivity
  have hv0 : (128*(v : ℝ)) ≠ 0 := by positivity
  have h1 := tendsto_scaled_inv_linear (128*(u : ℝ)) hu0
  have h2 := tendsto_scaled_inv_linear (128*(v : ℝ)) hv0
  have h3 := tendsto_scaled_inv_square (128*(u : ℝ)) hu0
  have hh := ((h1.sub h2).const_mul ((64*400021)*(A+(1/1000000)/Real.log 2))).add
    (h3.const_mul (128*400021*A*C/Real.log 2))
  simpa only [mul_zero,add_zero] using hh

lemma productSupply_log_error_coefficient : (1/1000000 : ℝ)/Real.log 2 ≤ 1/500000 := by
  have hl : (1/2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1/2) hl
  norm_num at hh
  have hi := mul_le_mul_of_nonneg_left hh (show (0 : ℝ) ≤ 1/1000000 by norm_num)
  convert hi using 1; ring

lemma productSupplyFirstLimit_lt :
    productSupplyLongLimit productSupplyFirstCoefficient 88850 94000 < 93/200 := by
  have hh := mul_le_mul_of_nonneg_left productSupply_log_error_coefficient
    (show (0 : ℝ) ≤ (64*400021)*(1/(128*88850)-1/(128*94000)) by norm_num)
  unfold productSupplyLongLimit productSupplyFirstCoefficient
  norm_num only [Nat.cast_ofNat,show (2 : ℝ)^10=1024 by norm_num]
  nlinarith only [hh]

lemma productSupplySecondLimit_lt :
    productSupplyLongLimit productSupplySecondCoefficient 94000 100007 < 64/125 := by
  have hh := mul_le_mul_of_nonneg_left productSupply_log_error_coefficient
    (show (0 : ℝ) ≤ (64*400021)*(1/(128*94000)-1/(128*100007)) by norm_num)
  unfold productSupplyLongLimit productSupplySecondCoefficient
  norm_num only [Nat.cast_ofNat,show (2 : ℝ)^10=1024 by norm_num]
  nlinarith only [hh]

lemma eventually_productSupplyFirstBudget (C : ℝ) :
    ∀ᶠ m : ℕ in atTop, productSupplyLongBudget productSupplyFirstCoefficient 88850 94000 C m ≤ 93/200 :=
  (tendsto_productSupplyLongBudget _ C 88850 94000 (by decide) (by decide)).eventually
    (eventually_le_nhds productSupplyFirstLimit_lt)

lemma eventually_productSupplySecondBudget (C : ℝ) :
    ∀ᶠ m : ℕ in atTop, productSupplyLongBudget productSupplySecondCoefficient 94000 100007 C m ≤ 64/125 :=
  (tendsto_productSupplyLongBudget _ C 94000 100007 (by decide) (by decide)).eventually
    (eventually_le_nhds productSupplySecondLimit_lt)

noncomputable def productSupplyShortBudget (m : ℕ) : ℝ :=
  (64*400021)/(75*(100007 : ℝ)^2*Real.log 2)*(1/(m : ℝ))+
    (64*400021*512)/(75*(100007 : ℝ)^2)

lemma eventually_productSupplyShortBudget :
    ∀ᶠ m : ℕ in atTop, productSupplyShortBudget m ≤ 7/400 := by
  have hi : Tendsto (fun m : ℕ => 1/(m : ℝ)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hh := (hi.const_mul ((64*400021)/(75*(100007 : ℝ)^2*Real.log 2))).add_const
    ((64*400021*512)/(75*(100007 : ℝ)^2))
  simp only [mul_zero,zero_add] at hh
  exact hh.eventually (eventually_le_nhds (by norm_num :
    (64*400021*512)/(75*(100007 : ℝ)^2) < 7/400))

lemma productSupplyLongBudget_identity (A C : ℝ) (u v m : ℕ)
    (hu : 1 ≤ u) (hv : 1 ≤ v) (hm : 1 ≤ m) :
    (64*400021*(m : ℝ)*Real.log 2)*
      ((A/(Real.log 2)^2)*
          (Real.log 2*(1/(128*(u : ℝ)*m-1)-1/(128*(v : ℝ)*m-1))+2*C/(128*(u : ℝ)*m)^2)+
        ((1/1000000)/(Real.log 2)^2)*(1/(128*(u : ℝ)*m-1)-1/(128*(v : ℝ)*m-1))) =
      productSupplyLongBudget A u v C m := by
  have hl : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hu0 : (u : ℝ) ≠ 0 := by exact_mod_cast (show u ≠ 0 by omega)
  have hum : (1 : ℝ) ≤ (u : ℝ)*m := by exact_mod_cast Nat.mul_pos hu hm
  have hvm : (1 : ℝ) ≤ (v : ℝ)*m := by exact_mod_cast Nat.mul_pos hv hm
  have h1 : 128*(u : ℝ)*m-1 ≠ 0 := by nlinarith only [hum]
  have h2 : 128*(v : ℝ)*m-1 ≠ 0 := by nlinarith only [hvm]
  unfold productSupplyLongBudget
  field_simp
  ring

lemma productSupplyShortBudget_identity (m : ℕ) (hm : 1 ≤ m) :
    (64*400021*(m : ℝ)*Real.log 2)*
      ((1/75)*(1+512*(m : ℝ)*Real.log 2)/((100007 : ℝ)*m*Real.log 2)^2) =
        productSupplyShortBudget m := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hl : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
  unfold productSupplyShortBudget
  field_simp

end Erdos821.AnalyticSieve
