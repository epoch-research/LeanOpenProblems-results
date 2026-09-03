import Submission.ProductSupplyRoughBound

/-!
# Rescaled product-sieve budgets

A finer fixed-ratio lower bound; no assertion of arbitrary-root supply.
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 5000000

noncomputable def scaledProductLongBudget (A : ℝ) (u v : ℕ) (C : ℝ) (m : ℕ) : ℝ :=
  (64*40000021)*(A+(1/1000000)/Real.log 2)*
    ((m : ℝ)/(128*(u : ℝ)*m-1)-(m : ℝ)/(128*(v : ℝ)*m-1))+
      (128*40000021*A*C/Real.log 2)*((m : ℝ)/(128*(u : ℝ)*m)^2)

noncomputable def scaledProductLongLimit (A : ℝ) (u v : ℕ) : ℝ :=
  (64*40000021)*(A+(1/1000000)/Real.log 2)*(1/(128*(u : ℝ))-1/(128*(v : ℝ)))

lemma tendsto_scaledProductLongBudget (A C : ℝ) (u v : ℕ) (hu : 1 ≤ u) (hv : 1 ≤ v) :
    Tendsto (scaledProductLongBudget A u v C) atTop (𝓝 (scaledProductLongLimit A u v)) := by
  have hu0 : (128*(u : ℝ)) ≠ 0 := by positivity
  have hv0 : (128*(v : ℝ)) ≠ 0 := by positivity
  have h1 := tendsto_scaled_inv_linear (128*(u : ℝ)) hu0
  have h2 := tendsto_scaled_inv_linear (128*(v : ℝ)) hv0
  have h3 := tendsto_scaled_inv_square (128*(u : ℝ)) hu0
  have hh := ((h1.sub h2).const_mul ((64*40000021)*(A+(1/1000000)/Real.log 2))).add
    (h3.const_mul (128*40000021*A*C/Real.log 2))
  simpa only [mul_zero,add_zero] using hh

noncomputable def scaledProductShortBudget (m : ℕ) : ℝ :=
  (64*40000021)/(75*(10000007 : ℝ)^2*Real.log 2)*(1/(m : ℝ))+
    (64*40000021*512)/(75*(10000007 : ℝ)^2)

lemma eventually_scaledProductShortBudget :
    ∀ᶠ m : ℕ in atTop, scaledProductShortBudget m ≤ 7/40000 := by
  have hi : Tendsto (fun m : ℕ => 1/(m : ℝ)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hh := (hi.const_mul ((64*40000021)/(75*(10000007 : ℝ)^2*Real.log 2))).add_const
    ((64*40000021*512)/(75*(10000007 : ℝ)^2))
  simp only [mul_zero,zero_add] at hh
  exact hh.eventually (eventually_le_nhds (by norm_num :
    (64*40000021*512)/(75*(10000007 : ℝ)^2) < 7/40000))

lemma scaledProductLongBudget_identity (A C : ℝ) (u v m : ℕ)
    (hu : 1 ≤ u) (hv : 1 ≤ v) (hm : 1 ≤ m) :
    (64*40000021*(m : ℝ)*Real.log 2)*
      ((A/(Real.log 2)^2)*
          (Real.log 2*(1/(128*(u : ℝ)*m-1)-1/(128*(v : ℝ)*m-1))+2*C/(128*(u : ℝ)*m)^2)+
        ((1/1000000)/(Real.log 2)^2)*(1/(128*(u : ℝ)*m-1)-1/(128*(v : ℝ)*m-1))) =
      scaledProductLongBudget A u v C m := by
  have hl : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hu0 : (u : ℝ) ≠ 0 := by exact_mod_cast (show u ≠ 0 by omega)
  have hum : (1 : ℝ) ≤ (u : ℝ)*m := by exact_mod_cast Nat.mul_pos hu hm
  have hvm : (1 : ℝ) ≤ (v : ℝ)*m := by exact_mod_cast Nat.mul_pos hv hm
  have h1 : 128*(u : ℝ)*m-1 ≠ 0 := by nlinarith only [hum]
  have h2 : 128*(v : ℝ)*m-1 ≠ 0 := by nlinarith only [hvm]
  unfold scaledProductLongBudget
  field_simp
  ring

lemma scaledProductShortBudget_identity (m : ℕ) (hm : 1 ≤ m) :
    (64*40000021*(m : ℝ)*Real.log 2)*
      ((1/75)*(1+512*(m : ℝ)*Real.log 2)/((10000007 : ℝ)*m*Real.log 2)^2) =
        scaledProductShortBudget m := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hl : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
  unfold scaledProductShortBudget
  field_simp

lemma scaled_product_long_weighted_budget (c H X u v m : ℕ) (A C J cnt : ℝ)
    (hc : 0 < c) (hu : 1 ≤ u) (huv : u ≤ v) (hm : 1 ≤ m)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hJ : 0 ≤ J) (hcnt : 0 ≤ cnt)
    (hHF : (H : ℝ)*((c : ℝ)/(c.totient : ℝ)) ≤ (X : ℝ)/(c.totient : ℝ))
    (hlog : Real.log X ≤ 64*40000021*(m : ℝ)*Real.log 2)
    (hbound : cnt ≤
      (A*(H : ℝ)*((c : ℝ)/(c.totient : ℝ))/(Real.log 2)^2)*
        (Real.log 2*(1/(128*(u : ℝ)*m-1)-1/(128*(v : ℝ)*m-1))+2*C/(128*(u : ℝ)*m)^2)+
          ((1/1000000)*(H : ℝ)/(Real.log 2)^2)*(1/(128*(u : ℝ)*m-1)-1/(128*(v : ℝ)*m-1)))
    (hbudget : scaledProductLongBudget A u v C m ≤ J) :
    Real.log X*cnt ≤ J*(X : ℝ)/(c.totient : ℝ) := by
  let F : ℝ := (c : ℝ)/(c.totient : ℝ)
  let L : ℝ := 64*40000021*(m : ℝ)*Real.log 2
  let D : ℝ := 1/(128*(u : ℝ)*m-1)-1/(128*(v : ℝ)*m-1)
  let U : ℝ := (A/(Real.log 2)^2)*(Real.log 2*D+2*C/(128*(u : ℝ)*m)^2)+
    ((1/1000000)/(Real.log 2)^2)*D
  have hφ : (0 : ℝ) < c.totient := by exact_mod_cast Nat.totient_pos.mpr hc
  have hF1 : 1 ≤ F := (one_le_div hφ).mpr (by exact_mod_cast Nat.totient_le c)
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hum : (1 : ℝ) ≤ (u : ℝ)*m := by exact_mod_cast Nat.mul_pos hu hm
  have huvm : (u : ℝ)*m ≤ (v : ℝ)*m := by exact_mod_cast Nat.mul_le_mul_right m huv
  have hD : 0 ≤ D := by
    apply sub_nonneg.mpr
    exact one_div_le_one_div_of_le (by nlinarith only [hum] : (0 : ℝ) < 128*(u : ℝ)*m-1)
      (by nlinarith only [huvm])
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have he : 0 ≤ ((1/1000000 : ℝ)/(Real.log 2)^2)*D := by positivity
  have hExtra := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hF1 (Nat.cast_nonneg H)) he
  have hraw : cnt ≤ (H : ℝ)*F*U := by
    apply hbound.trans
    have hh := _root_.add_le_add
      (le_refl ((A*(H : ℝ)*F/(Real.log 2)^2)*(Real.log 2*D+2*C/(128*(u : ℝ)*m)^2))) hExtra
    convert hh using 1 <;> dsimp [F,U,D] <;> ring
  have hh := mul_le_mul hlog hraw hcnt hL
  have hid : L*U=scaledProductLongBudget A u v C m :=
    scaledProductLongBudget_identity A C u v m hu (hu.trans huv) hm
  have heq : L*((H : ℝ)*F*U)=(H : ℝ)*F*scaledProductLongBudget A u v C m := by rw [← hid]; ring
  rw [heq] at hh
  apply (hh.trans (mul_le_mul_of_nonneg_left hbudget (show 0 ≤ (H : ℝ)*F by positivity))).trans
  have hlast := mul_le_mul_of_nonneg_left hHF hJ
  convert hlast using 1 <;> dsimp [F] <;> ring

lemma scaled_supply_quotient_bounds (m X d : ℕ)
    (hXlo : independentN 40000020 m ≤ X) (hXhi : X ≤ independentN 40000021 m)
    (hdlo : independentN 20000000 m ≤ d) (hdhi : d ≤ independentN 20000004 m) :
    2^(128*10000008*m) ≤ X/d ∧ X/d ≤ 2^(128*10000011*m) := by
  have hd : 0 < d := (by unfold independentN; positivity : 0 < independentN 20000000 m).trans_le hdlo
  constructor
  · apply (Nat.le_div_iff_mul_le hd).mpr
    apply (Nat.mul_le_mul_left _ hdhi).trans
    apply le_trans _ hXlo
    simp only [independentN,← pow_add]
    apply Nat.pow_le_pow_right (by decide)
    omega
  · have hmul : X ≤ 2^(128*10000011*m)*d := by
      apply hXhi.trans
      apply le_trans _ (Nat.mul_le_mul_left _ hdlo)
      simp only [independentN,← pow_add]
      apply Nat.pow_le_pow_right (by decide)
      omega
    apply (Nat.div_le_div_right hmul).trans_eq
    exact Nat.mul_div_cancel _ hd

lemma scaled_supply_log_upper (m X : ℕ) (hX : X ≤ independentN 40000021 m) :
    Real.log (X : ℝ) ≤ 64*40000021*(m : ℝ)*Real.log 2 := by
  have hh := log_nat_mono hX
  simpa only [independentN,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_mul,Real.log_pow] using hh

noncomputable def scaledProductTailError (m : ℕ) : ℝ :=
  (2 : ℝ)^(512*m)*((2 : ℝ)^(640000448*m)+(2 : ℝ)^(160000112*m)+1)

lemma scaledProductTailError_nonneg (m : ℕ) : 0 ≤ scaledProductTailError m := by
  unfold scaledProductTailError
  positivity

lemma scaledProductTailError_le (m : ℕ) : scaledProductTailError m ≤ 3*(2 : ℝ)^(640000960*m) := by
  have h1 : (2 : ℝ)^(160000112*m) ≤ (2 : ℝ)^(640000448*m) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have h2 : (1 : ℝ) ≤ 2^(640000448*m) := one_le_pow₀ (by norm_num)
  have hh := mul_le_mul_of_nonneg_left (_root_.add_le_add (_root_.add_le_add (le_refl ((2 : ℝ)^(640000448*m))) h1) h2)
    (show (0 : ℝ) ≤ 2^(512*m) by positivity)
  have he : (2 : ℝ)^(512*m)*(2 : ℝ)^(640000448*m)=(2 : ℝ)^(640000960*m) := by
    rw [← pow_add]
    congr 1
    omega
  unfold scaledProductTailError
  nlinarith only [hh,he]

lemma eventually_scaled_product_tail_error :
    ∀ᶠ m : ℕ in atTop, ∀ X H : ℕ, X ≤ independentN 40000021 m →
      2^(128*10000008*m) ≤ H →
        Real.log (X : ℝ)*scaledProductTailError m ≤ (H : ℝ)/1000000 := by
  filter_upwards [eventually_nat_poly_le_two_pow 1 (3000000*2560001344) 1] with m hm
  intro X H hX hH
  have hpoly : (3000000*2560001344 : ℝ)*(m : ℝ) ≤ (2 : ℝ)^m := by
    have hh : (3000000*2560001344 : ℝ)*((m : ℝ)+1) ≤ (2 : ℝ)^m := by
      exact_mod_cast (by simpa only [one_mul,pow_one] using hm)
    nlinarith only [hh]
  have hlog : Real.log (X : ℝ) ≤ 2560001344*(m : ℝ) := by
    have hh := scaled_supply_log_upper m X hX
    have hl2 : Real.log (2 : ℝ) ≤ 1 := by linarith [Real.log_two_lt_d9]
    have hmul := mul_le_mul_of_nonneg_left hl2 (show (0 : ℝ) ≤ 64*40000021*m by positivity)
    nlinarith only [hh,hmul]
  have herr := mul_le_mul hlog (scaledProductTailError_le m) (scaledProductTailError_nonneg m)
    (show (0 : ℝ) ≤ 2560001344*m by positivity)
  have hscaled := mul_le_mul_of_nonneg_right hpoly (show (0 : ℝ) ≤ 2^(640000960*m) by positivity)
  have hpow : (2 : ℝ)^m*(2 : ℝ)^(640000960*m) ≤ (H : ℝ) := by
    rw [← pow_add]
    apply le_trans _ (Nat.cast_le.mpr hH)
    simp only [Nat.cast_pow,Nat.cast_ofNat]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  nlinarith only [herr,hscaled,hpow]


end Erdos821.AnalyticSieve
