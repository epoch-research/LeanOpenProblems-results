import Submission.CofactorProductScales

/-!
# A power-saving primitive bilinear mean up to the product half level
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 3000000

noncomputable def cofactorProductMeanConstant (b v t : ℕ) : ℝ :=
  144*(256*(b : ℝ))*(256*(v : ℝ)+4)*(256*(t : ℝ))

lemma cofactorProductMeanConstant_nonneg (b v t : ℕ) : 0 ≤ cofactorProductMeanConstant b v t := by
  unfold cofactorProductMeanConstant
  positivity

lemma cofactorScale_bilinear_primitive_saving (a b l v t m B X : ℕ)
    (ha : 1 ≤ a) (hab : a ≤ b) (hl : 1 ≤ l) (ht : 1 ≤ t)
    (hlevel : 2*b+1 ≤ l+t)
    (hB : cofactorScale l m ≤ B) (hBup : B ≤ cofactorScale v m) (hX : X ≤ cofactorScale t m) :
    ((2 : ℝ)^m)^2*primitiveCofactorBilinearMean (Ioc (cofactorScale a m) (cofactorScale b m)) B X ≤
      cofactorProductMeanConstant b v t*((m : ℝ)+1)^3*(B : ℝ)*(cofactorScale t m : ℝ) := by
  by_cases hX0 : X = 0
  · subst X
    simp only [primitiveCofactorBilinearMean,twistedArithmeticSum,show Icc (1 : ℕ) 0 = ∅ by decide,
      sum_empty,norm_zero,mul_zero,zero_div,sum_const_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (cofactorProductMeanConstant_nonneg b v t)
      (by positivity)) (Nat.cast_nonneg B)) (Nat.cast_nonneg _)
  have hX1 : 1 ≤ X := by omega
  have hB1 : 1 ≤ B := (cofactorScale_pos l m).trans_le hB
  let r := 256*(b-a)*m
  have hexp : 256*a*m+r=256*b*m := by
    have hh := congrArg (fun z : ℕ => 256*z*m) (Nat.add_sub_of_le hab)
    dsimp [r]
    nlinarith only [hh]
  have hh := primitiveCofactorBilinearMean_dyadic_interval (256*a*m) r B X hB1 hX1
  rw [hexp,← cofactorScale_eq a m,← cofactorScale_eq b m] at hh
  have hr : (r : ℝ) ≤ (256*(b : ℝ))*((m : ℝ)+1) := by
    have hnat : r ≤ 256*b*m := Nat.mul_le_mul_right m (Nat.mul_le_mul_left _ (Nat.sub_le b a))
    have hc : (r : ℝ) ≤ 256*(b : ℝ)*m := by exact_mod_cast hnat
    nlinarith only [hc,Nat.cast_nonneg (α := ℝ) b]
  have hlog := cofactorScale_log_add_two_le v m B hBup
  have hlogX : Real.log X ≤ 256*(t : ℝ)*((m : ℝ)+1) :=
    (log_nat_mono hX).trans (cofactorScale_log_le t m)
  have hshape := cofactorBilinearShape_mono_right (cofactorScale b m) (cofactorScale a m) B X (cofactorScale t m) hX
  have hnonneg : 0 ≤ 2+Real.log ((B : ℝ)+2) := by
    have := Real.log_nonneg (show 1 ≤ (B : ℝ)+2 by linarith [Nat.cast_nonneg (α := ℝ) B])
    linarith
  have hraw : primitiveCofactorBilinearMean (Ioc (cofactorScale a m) (cofactorScale b m)) B X ≤
      (36*(256*(b : ℝ))*(256*(v : ℝ)+4)*(256*(t : ℝ)))*((m : ℝ)+1)^3*
        cofactorBilinearShape (cofactorScale b m) (cofactorScale a m) B (cofactorScale t m) := by
    apply hh.trans
    have hc := mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_right hr (by norm_num : (0 : ℝ) ≤ 36))
      hlog hnonneg (by positivity)) hlogX (Real.log_natCast_nonneg _) (by positivity)
    have hc' := mul_le_mul hc hshape (cofactorBilinearShape_nonneg _ _ _ _) (by positivity)
    convert hc' using 1; ring
  have hscaled := mul_le_mul_of_nonneg_left hraw (sq_nonneg ((2 : ℝ)^m))
  have hsave := mul_le_mul_of_nonneg_left
    (cofactorScale_bilinear_shape_saving a b l t m B ha hl ht hlevel hB)
    (show 0 ≤ (36*(256*(b : ℝ))*(256*(v : ℝ)+4)*(256*(t : ℝ)))*((m : ℝ)+1)^3 by positivity)
  apply hscaled.trans
  unfold cofactorProductMeanConstant
  convert hsave using 1 <;> ring

end Erdos821.AnalyticSieve
