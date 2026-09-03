import FormalConjecturesUtil
import Submission.UnsignedCorrectionLowerBound

/-! The coefficient norm in the aggregate CRT correction is unbounded.
Consequently uniform coordinatewise `o(N)` is not, by itself, a bound for
the aggregate normalized correction. This file makes no claim about the
actual signed aggregate. -/

namespace Erdos371CRTCorrectionCoefficientGrowth

open Finset Filter Erdos371PrimePowerRectangles
open Erdos371SubcriticalPrimePairCancellation (pairs)
open Erdos371WeightedLargeDivisorEnergy (weight weight_nonneg)
open scoped Topology

noncomputable def coefficientNorm (N : ℕ) : ℝ :=
  ∑ z ∈ pairs N, weight N z.1

lemma rectangle_coefficient_bound {X : ℕ} (hX : 1<X) :
    (X : ℝ)*piece X 1 ≤ coefficientNorm (X^20) := by
  have hs := mul_le_mul_of_nonneg_left (piece_le_rect hX (k := 1))
    (Nat.cast_nonneg (α := ℝ) X)
  apply hs.trans
  rw [mul_sum]
  apply le_trans _ (show (∑ z ∈ rect X 1, weight (X^20) z.1) ≤
      coefficientNorm (X^20) from ?_)
  · apply sum_le_sum
    rintro ⟨q,p⟩ hz
    obtain ⟨hq,hp⟩ := mem_product.mp hz
    have hq' := (Nat.mem_primesBelow.mp hq).2
    have hp' := mem_block.mp hp
    have hprod : X ≤ q*p := by
      have hx : X<p := by simpa only [pow_one] using hp'.2.1
      have hh : p ≤ q*p := Nat.le_mul_of_pos_left p hq'.pos
      omega
    have hpos : (0 : ℝ)<(q*p : ℕ) := Nat.cast_pos.mpr (Nat.mul_pos hq'.pos hp'.1.pos)
    have hratio : (X : ℝ)/(q*p : ℕ) ≤ 1 := (div_le_one hpos).mpr (Nat.cast_le.mpr hprod)
    have hh := mul_le_mul_of_nonneg_right hratio (weight_nonneg (X^20) q)
    dsimp only [Prod.fst,Prod.snd]
    calc
      (X : ℝ)*(weight (X^20) q/(q*p : ℕ)) =
          ((X : ℝ)/(q*p : ℕ))*weight (X^20) q := by ring
      _ ≤ weight (X^20) q := by simpa using hh
  · apply sum_le_sum_of_subset_of_nonneg
    · exact rect_subset (by omega) (by simp)
    · intro z _ _
      exact weight_nonneg _ _

lemma eventually_coefficient_lower : ∀ᶠ X : ℕ in atTop,
    (X : ℝ)/80 ≤ coefficientNorm (X^20) := by
  have ht : Tendsto (fun X : ℕ => piece X 1) atTop (𝓝 (1/40 : ℝ)) := by
    have ht := Erdos371UnsignedCorrectionLowerBound.piece_tendsto
      (k := 1) (by simp)
    norm_num [j] at ht ⊢
    exact ht
  have he := ht.eventually (lt_mem_nhds (by norm_num : (1/80 : ℝ)<1/40))
  filter_upwards [he,eventually_gt_atTop 1] with X hgood hX
  have hh := mul_le_mul_of_nonneg_left hgood.le (Nat.cast_nonneg (α := ℝ) X)
  have hh' : (X : ℝ)/80 ≤ (X : ℝ)*piece X 1 := by
    simpa only [mul_one_div] using hh
  exact hh'.trans (rectangle_coefficient_bound hX)

/-- Even on twentieth-power cutoffs, the sum of the nonnegative coefficients
tends to infinity. This is not a noncancellation theorem for the correction. -/
theorem coefficientNorm_tendsto_along_powers :
    Tendsto (fun X : ℕ => coefficientNorm (X^20)) atTop atTop := by
  apply tendsto_atTop.mpr
  intro B
  have he : ∀ᶠ X : ℕ in atTop, B*80 ≤ (X : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (B*80))
  filter_upwards [he,eventually_coefficient_lower] with X hX hbound
  linarith

end Erdos371CRTCorrectionCoefficientGrowth

#print axioms Erdos371CRTCorrectionCoefficientGrowth.coefficientNorm_tendsto_along_powers
