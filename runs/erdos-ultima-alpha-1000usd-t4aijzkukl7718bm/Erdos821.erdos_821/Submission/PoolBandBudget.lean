import Submission.PoolBandScales

/-! Uniform budget tools for variable retained-pool prime bands. -/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 5000000

lemma eventually_pool_block_coefficient_uniform :
    ∀ᶠ m : ℕ in atTop, ∀ u : ℕ, 1 ≤ u →
      (1+1/(2 : ℝ)^10)*(256*(m : ℝ)+2)*(2 : ℝ)^10/(128*(u : ℝ)*m+1)^3 ≤
        (1/1000000 : ℝ)*poolTotientMass (widePairPool 10000000 m) := by
  let W := widePairMassDenom 10000000
  have hW : 0 < W := widePairMassDenom_pos 10000000
  have hWR : (0 : ℝ)<W := by exact_mod_cast hW
  filter_upwards [eventually_ge_atTop (1000000*W*600000+1)] with m hm
  intro u hu
  have huR : (1 : ℝ) ≤ u := by exact_mod_cast hu
  have hm1 : 1 ≤ m := by omega
  have hmR : (1000000 : ℝ)*W*600000+1 ≤ m := by exact_mod_cast hm
  have hnum : (1+1/(2 : ℝ)^10)*(256*(m : ℝ)+2)*(2 : ℝ)^10 ≤ 600000*((m : ℝ)+1) := by
    norm_num
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  have hden : ((m : ℝ)+1)^3 ≤ (128*(u : ℝ)*m+1)^3 := by
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  calc
    _ ≤ 600000*((m : ℝ)+1)/((m : ℝ)+1)^3 := div_le_div₀ (by positivity) hnum (by positivity) hden
    _ = 600000/((m : ℝ)+1)^2 := by field_simp
    _ ≤ 1/(1000000*(W : ℝ)) := by
      apply (div_le_div_iff₀ (by positivity : (0 : ℝ)<((m : ℝ)+1)^2) (by positivity : (0 : ℝ)<1000000*W)).mpr
      have hm0 := Nat.cast_nonneg (α := ℝ) m
      nlinarith only [hmR,hm0,sq_nonneg (m : ℝ)]
    _ = (1/1000000 : ℝ)*(1/(W : ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (widePairPool_mass_lower 10000000 m hm1) (by norm_num)


lemma pool_scaled_weighted_budget (u v m X : ℕ) (A C V cnt J : ℝ)
    (hu : 1 ≤ u) (huv : u ≤ v) (hm : 1 ≤ m)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hV : 0 ≤ V) (hcnt : 0 ≤ cnt)
    (hX : X ≤ independentN 40000021 m)
    (hraw : cnt ≤
      (A*(X : ℝ)*V/(Real.log 2)^2)*
        (Real.log 2*(1/(128*(u : ℝ)*m-1)-1/(128*(v : ℝ)*m-1))+2*C/(128*(u : ℝ)*m)^2)+
      ((1/1000000 : ℝ)*(X : ℝ)*V/(Real.log 2)^2)*
        (1/(128*(u : ℝ)*m-1)-1/(128*(v : ℝ)*m-1)))
    (hbudget : scaledProductLongBudget A u v C m ≤ J) :
    Real.log (X : ℝ)*cnt ≤ J*(X : ℝ)*V := by
  let Δ : ℝ := 1/(128*(u : ℝ)*m-1)-1/(128*(v : ℝ)*m-1)
  let T : ℝ := Real.log 2*Δ+2*C/(128*(u : ℝ)*m)^2
  let U : ℝ := A/(Real.log 2)^2*T+(1/1000000 : ℝ)/(Real.log 2)^2*Δ
  let L : ℝ := 64*40000021*(m : ℝ)*Real.log 2
  have hum : (1 : ℝ) ≤ (u : ℝ)*m := by exact_mod_cast Nat.mul_pos hu hm
  have huvm : (u : ℝ)*m ≤ (v : ℝ)*m := by exact_mod_cast Nat.mul_le_mul_right m huv
  have hΔ : 0 ≤ Δ := sub_nonneg.mpr (one_div_le_one_div_of_le (by nlinarith) (by nlinarith))
  have hlog2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have he : L*U=scaledProductLongBudget A u v C m :=
    scaledProductLongBudget_identity A C u v m hu (hu.trans huv) hm
  have hbound : cnt ≤ (X : ℝ)*V*U := by
    convert hraw using 1; dsimp [U,T,Δ]; ring
  have h := mul_le_mul (scaled_supply_log_upper m X hX) hbound hcnt hL
  have hb := mul_le_mul_of_nonneg_left hbudget (show 0 ≤ (X : ℝ)*V by positivity)
  have hid : L*((X : ℝ)*V*U)=(X : ℝ)*V*scaledProductLongBudget A u v C m := by
    rw [← he]
    ring
  rw [hid] at h
  apply (h.trans hb).trans_eq
  ring

end Erdos821.AnalyticSieve
