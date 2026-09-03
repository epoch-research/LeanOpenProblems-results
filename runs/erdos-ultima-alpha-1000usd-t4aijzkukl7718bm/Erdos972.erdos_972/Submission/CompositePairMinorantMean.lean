import Submission.MixedSmoothMean
import Submission.CompositeSmoothMean

/-! Removing prime coordinates does not change the fixed-parameter mean
of the signed two-scale expression. No moving-parameter lower bound or
prime-pair infinitude is asserted. -/
namespace Erdos972CompositePairMinorantMean

open Finset Filter
open scoped Topology
open Erdos972PrimePowerError Erdos972SmoothMangoldt Erdos972SmoothMangoldtPositive
open Erdos972FullSmoothL1Obstruction Erdos972CompositeSmoothMean
open Erdos972TwoScalePairMinorant Erdos972MixedSmoothMean

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable def deletePrimeCoordinates (α : ℝ) (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Ioc 0 N, if n.Prime ∨ (floorMul α n).Prime then 0 else a n

lemma bounded_removal_estimate {α C : ℝ} (hα : 1 ≤ α) (hC : 0 ≤ C)
    (a : ℕ → ℝ) (ha : ∀ n, |a n| ≤ C) (N : ℕ) :
    |(∑ n ∈ Ioc 0 N, a n) - deletePrimeCoordinates α a N| ≤
      C*((N.primeCounting : ℝ)+(floorMul α N).primeCounting) := by
  classical
  have hid : (∑ n ∈ Ioc 0 N, a n) - deletePrimeCoordinates α a N =
      ∑ n ∈ Ioc 0 N, if n.Prime ∨ (floorMul α n).Prime then a n else 0 := by
    simp only [deletePrimeCoordinates, ← sum_sub_distrib]
    apply sum_congr rfl
    intro n hn
    split_ifs <;> simp
  rw [hid]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ n ∈ Ioc 0 N,
        ((if n.Prime then C else 0)+(if (floorMul α n).Prime then C else 0)) := by
      apply sum_le_sum
      intro n hn
      by_cases hp : n.Prime <;> by_cases hq : (floorMul α n).Prime <;>
        simp only [hp, hq, or_self, true_or, false_or, if_true, if_false,
          abs_zero, add_zero, zero_add] <;> linarith only [ha n, hC]
    _ = C*((((Ioc 0 N).filter Nat.Prime).card : ℝ)+
        ((Ioc 0 N).filter (fun n => (floorMul α n).Prime)).card) := by
      rw [sum_add_distrib, ← sum_filter, ← sum_filter]
      simp only [sum_const, nsmul_eq_mul]
      ring
    _ ≤ _ := by
      rw [prime_card_eq]
      exact mul_le_mul_of_nonneg_left (add_le_add_right
        (Nat.cast_le.mpr (output_prime_card_le hα N)) _) hC

/-- Removing prime coordinates has zero normalized effect on ANY fixed
uniformly bounded signed sequence. The bounding constant is fixed. -/
theorem bounded_removal_mean_zero {α C : ℝ} (hα : 1 ≤ α) (hC : 0 ≤ C)
    (a : ℕ → ℝ) (ha : ∀ n, |a n| ≤ C) :
    Tendsto (fun N : ℕ =>
      ((∑ n ∈ Ioc 0 N, a n)-deletePrimeCoordinates α a N)/(N : ℝ))
      atTop (𝓝 0) := by
  have hh := (primeCounting_div_tendsto_zero.add
    (output_prime_density_tendsto_zero hα)).const_mul C
  simp only [zero_add, mul_zero] at hh
  apply squeeze_zero_norm' _ hh
  filter_upwards with N
  rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) N)]
  have hb := div_le_div_of_nonneg_right (bounded_removal_estimate hα hC a ha N)
    (Nat.cast_nonneg (α := ℝ) N)
  convert hb using 1
  ring

lemma pairMinorant_bounded {t : ℝ} (ht : 0 < t) (m n : ℕ) :
    |pairMinorant t m n| ≤ 16/t^2 := by
  have ht2 : 0 < 2*t := by positivity
  have hdouble (k : ℕ) : smoothMangoldt (2*t) k ≤ 1/t := by
    apply (smoothMangoldt_le_inv ht2 k).trans
    apply (div_le_div_iff₀ ht2 ht).mpr
    linarith only [ht]
  have hab (a b : ℝ) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b)
      (ha : a ≤ 1/t) (hb : b ≤ 1/t) : 0 ≤ a*b ∧ a*b ≤ 1/t^2 := by
    refine ⟨mul_nonneg ha0 hb0, ?_⟩
    have hh := mul_le_mul ha hb hb0 (one_div_nonneg.mpr ht.le)
    convert hh using 1
    ring
  have hA := hab _ _ (smoothMangoldt_nonneg ht m) (smoothMangoldt_nonneg ht n)
    (smoothMangoldt_le_inv ht m) (smoothMangoldt_le_inv ht n)
  have hB := hab _ _ (smoothMangoldt_nonneg ht2 m) (smoothMangoldt_nonneg ht n)
    (hdouble m) (smoothMangoldt_le_inv ht n)
  have hC := hab _ _ (smoothMangoldt_nonneg ht m) (smoothMangoldt_nonneg ht2 n)
    (smoothMangoldt_le_inv ht m) (hdouble n)
  have h0 : (0 : ℝ) ≤ 1/t^2 := by positivity
  unfold pairMinorant
  apply abs_le.mpr
  simp only [div_eq_mul_inv, one_mul] at hA hB hC h0 ⊢
  constructor <;> nlinarith only [hA.1, hA.2, hB.1, hB.2, hC.1, hC.2, h0]

noncomputable def compositePairMinorantSum (t α : ℝ) (N : ℕ) : ℝ :=
  deletePrimeCoordinates α (fun n => pairMinorant t n (floorMul α n)) N

/-- The difference contains every term with a prime input OR a prime output,
with its sign retained; its normalized mean tends to zero at fixed t. -/
theorem removed_pair_mean_zero {α t : ℝ} (hα : 1 ≤ α) (ht : 0 < t) :
    Tendsto (fun N : ℕ =>
      (pairMinorantSum t α N-compositePairMinorantSum t α N)/(N : ℝ)) atTop (𝓝 0) :=
  bounded_removal_mean_zero hα (show 0 ≤ 16/t^2 by positivity)
    (fun n => pairMinorant t n (floorMul α n)) (fun n => pairMinorant_bounded ht n _)

/-- The SAME fixed-parameter main term persists after deleting all prime
coordinates, so this mean alone does not establish any prime pairs. -/
theorem composite_pair_fixed_mean {α t : ℝ} (hα : 1 ≤ α) (hI : Irrational α)
    (ht : 0 < t) :
    Tendsto (fun N : ℕ => compositePairMinorantSum t α N/(N : ℝ)) atTop
      (𝓝 (pairMean t)) := by
  have hh := (pairMinorant_fixed_mean hα hI ht).sub (removed_pair_mean_zero hα ht)
  simp only [sub_zero] at hh
  convert hh using 1
  funext N
  ring

#print axioms bounded_removal_mean_zero
#print axioms pairMinorant_bounded
#print axioms composite_pair_fixed_mean

end Erdos972CompositePairMinorantMean
