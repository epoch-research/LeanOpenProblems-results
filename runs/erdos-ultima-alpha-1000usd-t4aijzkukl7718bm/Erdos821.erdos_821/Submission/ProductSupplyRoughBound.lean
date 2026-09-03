import Submission.ProductSupplyScales

/-!
# A rejected-prime budget using two long-cofactor ranges
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 5000000

lemma product_long_weighted_budget (c H X u v m : ℕ) (A C J cnt : ℝ)
    (hc : 0 < c) (hu : 1 ≤ u) (huv : u ≤ v) (hm : 1 ≤ m)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hJ : 0 ≤ J) (hcnt : 0 ≤ cnt)
    (hHF : (H : ℝ)*((c : ℝ)/(c.totient : ℝ)) ≤ (X : ℝ)/(c.totient : ℝ))
    (hlog : Real.log X ≤ 64*400021*(m : ℝ)*Real.log 2)
    (hbound : cnt ≤
      (A*(H : ℝ)*((c : ℝ)/(c.totient : ℝ))/(Real.log 2)^2)*
        (Real.log 2*(1/(128*(u : ℝ)*m-1)-1/(128*(v : ℝ)*m-1))+2*C/(128*(u : ℝ)*m)^2)+
          ((1/1000000)*(H : ℝ)/(Real.log 2)^2)*(1/(128*(u : ℝ)*m-1)-1/(128*(v : ℝ)*m-1)))
    (hbudget : productSupplyLongBudget A u v C m ≤ J) :
    Real.log X*cnt ≤ J*(X : ℝ)/(c.totient : ℝ) := by
  let F : ℝ := (c : ℝ)/(c.totient : ℝ)
  let L : ℝ := 64*400021*(m : ℝ)*Real.log 2
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
  have hid : L*U=productSupplyLongBudget A u v C m :=
    productSupplyLongBudget_identity A C u v m hu (hu.trans huv) hm
  have heq : L*((H : ℝ)*F*U)=(H : ℝ)*F*productSupplyLongBudget A u v C m := by rw [← hid]; ring
  rw [heq] at hh
  apply (hh.trans (mul_le_mul_of_nonneg_left hbudget (show 0 ≤ (H : ℝ)*F by positivity))).trans
  have hlast := mul_le_mul_of_nonneg_left hHF hJ
  convert hlast using 1 <;> dsimp [F] <;> ring

/-- The improved cutoff is 177700/400020, below 4/9. -/
theorem eventually_product_supply_rough_bound :
    ∀ᶠ m : ℕ in atTop, ∀ X d : ℕ,
      independentN 400020 m ≤ X → X ≤ independentN 400021 m →
      independentN 200000 m ≤ d → d ≤ independentN 200004 m →
      d ∈ Nat.smoothNumbers (independentN 177700 m) →
        Real.log (X : ℝ)*((roughProgressionPrimes d (independentN 177700 m) X).card : ℝ) ≤
          (199/200 : ℝ)*(X : ℝ)/(d.totient : ℝ) := by
  obtain ⟨C₁,hC₁,K₁,hFirst⟩ := exists_product_cofactor_hyperbolic_bound 1 106376 200003 12750 10
    (by decide) (by decide) (by decide) (by decide) (by decide) (1/1000000) (by norm_num)
  obtain ⟨C₂,hC₂,K₂,hSecond⟩ := exists_long_cofactor_hyperbolic_bound 1 199999 400003 3 10
    (by decide) (by decide) (by decide) (by decide) (by decide) (1/1000000) (by norm_num)
  filter_upwards [eventually_productSupplyFirstBudget C₁,eventually_productSupplySecondBudget C₂,
    eventually_productSupplyShortBudget,
    eventually_short_cofactor_dyadic_bound 100011 100007 (by decide) (by decide),
    eventually_product_supply_tail_error,eventually_ge_atTop (max 10000 (max K₁ K₂))]
    with m hFB hSB hTB hShort hTail hm
  intro X d hXlo hXhi hdlo hdhi hds
  have hmB : 10000 ≤ m := (le_max_left _ _).trans hm
  have hmK₁ : K₁ ≤ m := (le_max_left _ _).trans ((le_max_right _ _).trans hm)
  have hmK₂ : K₂ ≤ m := (le_max_right _ _).trans ((le_max_right _ _).trans hm)
  have hm1 : 1 ≤ m := by omega
  have hd : 0 < d := (by unfold independentN; positivity : 0 < independentN 200000 m).trans_le hdlo
  have hφ : (0 : ℝ) < d.totient := by exact_mod_cast Nat.totient_pos.mpr hd
  let H := X/d
  let F : ℝ := (d : ℝ)/(d.totient : ℝ)
  let L : ℝ := 64*400021*(m : ℝ)*Real.log 2
  have hH := successor_supply_quotient_bounds m X d hXlo hXhi hdlo hdhi
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hF1 : 1 ≤ F := (one_le_div hφ).mpr (by exact_mod_cast Nat.totient_le d)
  have hHF : (H : ℝ)*F ≤ (X : ℝ)/(d.totient : ℝ) := by
    have hh : ((X/d : ℕ) : ℝ)*(d : ℝ) ≤ X := by exact_mod_cast Nat.div_mul_le_self X d
    simpa only [H,F,mul_div_assoc] using div_le_div_of_nonneg_right hh hφ.le
  have hHX : (H : ℝ) ≤ (X : ℝ)/(d.totient : ℝ) :=
    (le_mul_of_one_le_right (Nat.cast_nonneg H) hF1).trans hHF
  have hlog : Real.log (X : ℝ) ≤ L := successor_supply_log_upper m X hXhi
  have hfirst0 := hFirst (128*88850*m) (128*5150*m) d H (by omega) (by omega) hd
    (product_supply_hyperbola_upper m H hH.2) (by
      rw [show 128*88850*m+128*5150*m=128*94000*m by omega]
      exact product_supply_first_threshold m H hmB hH.1)
  rw [show 128*88850*m+128*5150*m=128*94000*m by omega] at hfirst0
  simp only [Nat.cast_mul,Nat.cast_ofNat] at hfirst0
  rw [show 128*88850*(m : ℝ)+128*5150*(m : ℝ)=128*94000*(m : ℝ) by ring] at hfirst0
  have hfirstW : Real.log X*((hyperbolicPrimePairPool d H (2^(128*88850*m)) (2^(128*94000*m))).card : ℝ) ≤
      (93/200 : ℝ)*(X : ℝ)/(d.totient : ℝ) := by
    apply product_long_weighted_budget d H X 88850 94000 m productSupplyFirstCoefficient C₁ (93/200) _
      hd (by decide) (by decide) hm1 (by norm_num [productSupplyFirstCoefficient]) hC₁.le
      (by norm_num) (Nat.cast_nonneg _) hHF hlog _ hFB
    exact hfirst0
  have hsecond0 := hSecond (128*94000*m) (128*6007*m) d H (by omega) (by omega) hd (by
    rw [show 128*94000*m+128*6007*m=128*100007*m by omega]
    exact product_supply_second_threshold m H hmB hH.1)
  rw [show 128*94000*m+128*6007*m=128*100007*m by omega] at hsecond0
  simp only [Nat.cast_mul,Nat.cast_ofNat] at hsecond0
  rw [show 128*94000*(m : ℝ)+128*6007*(m : ℝ)=128*100007*(m : ℝ) by ring] at hsecond0
  have hsecondW : Real.log X*((hyperbolicPrimePairPool d H (2^(128*94000*m)) (2^(128*100007*m))).card : ℝ) ≤
      (64/125 : ℝ)*(X : ℝ)/(d.totient : ℝ) := by
    apply product_long_weighted_budget d H X 94000 100007 m productSupplySecondCoefficient C₂ (64/125) _
      hd (by decide) (by decide) hm1 (by norm_num [productSupplySecondCoefficient]) hC₂.le
      (by norm_num) (Nat.cast_nonneg _) hHF hlog _ hSB
    exact hsecond0
  let V : ℝ := (1/75)*(1+512*(m : ℝ)*Real.log 2)/((100007 : ℝ)*m*Real.log 2)^2
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hshort0 := hShort d H H hd hH.2
  have hshort : ((hyperbolicPrimePairPool d H (2^(128*100007*m)) H).card : ℝ) ≤
      (H : ℝ)*F*V+productSupplyTailError m := by
    convert hshort0 using 1; dsimp [F,V,productSupplyTailError]; norm_num; ring
  have hshortW : Real.log X*((hyperbolicPrimePairPool d H (2^(128*100007*m)) H).card : ℝ) ≤
      (11/625 : ℝ)*(X : ℝ)/(d.totient : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hshort (Real.log_natCast_nonneg X)
    rw [mul_add] at hh
    have hmain := mul_le_mul_of_nonneg_right hlog (show 0 ≤ (H : ℝ)*F*V by positivity)
    have hid : L*V=productSupplyShortBudget m := productSupplyShortBudget_identity m hm1
    have he : L*((H : ℝ)*F*V)=(H : ℝ)*F*productSupplyShortBudget m := by rw [← hid]; ring
    rw [he] at hmain
    have hmain' := hmain.trans (mul_le_mul_of_nonneg_left hTB (show 0 ≤ (H : ℝ)*F by positivity))
    have ht := hTail X H hXhi hH.1
    have h1 := mul_le_mul_of_nonneg_left hHF (show (0 : ℝ) ≤ 7/400 by norm_num)
    have h2 := div_le_div_of_nonneg_right hHX (show (0 : ℝ) ≤ 10000 by norm_num)
    simp only [div_eq_mul_inv] at hh hmain' ht h1 h2 ⊢
    nlinarith only [hh,hmain',ht,h1,h2]
  have hrough := rough_progression_card_le_long_short d (independentN 177700 m) X
    (2^(128*94000*m)) hd hds (product_supply_smooth_cutoff_not_prime m hm1)
  have hsplit : ((hyperbolicPrimePairPool d H (2^(128*94000*m)) H).card : ℝ) ≤
      ((hyperbolicPrimePairPool d H (2^(128*94000*m)) (2^(128*100007*m))).card : ℝ)+
        ((hyperbolicPrimePairPool d H (2^(128*100007*m)) H).card : ℝ) := by
    exact_mod_cast hyperbolic_prime_pair_card_split d H (2^(128*94000*m)) (2^(128*100007*m)) H
  have hY : independentN 177700 m=2^(128*88850*m) := rfl
  rw [hY] at hrough
  have hh := mul_le_mul_of_nonneg_left hrough (Real.log_natCast_nonneg X)
  have hh' := mul_le_mul_of_nonneg_left hsplit (Real.log_natCast_nonneg X)
  rw [mul_add] at hh hh'
  rw [hY]
  have hnonneg : 0 ≤ (X : ℝ)/(d.totient : ℝ) := by positivity
  simp only [div_eq_mul_inv] at hh hh' hfirstW hsecondW hshortW hnonneg ⊢
  nlinarith only [hh,hh',hfirstW,hsecondW,hshortW,hnonneg]

end Erdos821.AnalyticSieve
