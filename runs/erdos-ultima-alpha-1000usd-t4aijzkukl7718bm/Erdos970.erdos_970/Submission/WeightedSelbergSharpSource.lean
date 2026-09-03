import Submission.WeightedSelbergSource
import Submission.FirstHitSharpTransfer

/-! Exact normalizer-sensitive coefficient costs for weighted conditional
Selberg populations. No asymptotic estimate is asserted in this file. -/
namespace Erdos970.FiniteSelberg
open Finset Real
variable {ι α : Type*} [Fintype ι] [DecidableEq ι]

theorem majorant_weighted_error_cost (q : ι → ℝ) (hq : ∀ i, 0 < q i ∧ q i < 1)
    (S : Finset (Finset ι)) (hSn : S.Nonempty)
    (hS : ∀ T ∈ S, ∀ U ⊆ T, U ∈ S)
    (A : Finset α) (w : α → ℝ) (ω : α → ι → Bool) (X : ℝ)
    (herr : ∀ T : Finset ι,
      |(∑ j ∈ A, w j*hitMonomial T (ω j))-X*∏ i ∈ T, q i| ≤ 1) :
    |(∑ j ∈ A, w j*majorant q S (ω j))-X/normalizer q S| ≤ kernelCost q (canonicalOrthogonal q S)^2 := by
  classical
  have hmean := majorant_mean_expansion q S hS
  rw [majorant_average q hq S hSn] at hmean
  have heq : (∑ j ∈ A, w j*majorant q S (ω j))-X/normalizer q S =
      ∑ T ∈ S, ∑ U ∈ S, (coefficient q S T*coefficient q S U)*
        ((∑ j ∈ A, w j*hitMonomial (T∪U) (ω j))-X*∏ i ∈ T∪U, q i) := by
    simp_rw [majorant_expansion q S hS, mul_sum]
    rw [sum_comm]
    simp_rw [sum_comm (s := A)]
    rw [div_eq_mul_one_div, hmean]
    simp only [mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro T hT
    apply sum_congr rfl
    intro U hU
    rw [mul_sub, mul_sum]
    congr 1
    · apply sum_congr rfl
      intro j hj
      ring
    · ring
  rw [heq]
  calc
    _ ≤ ∑ T ∈ S, ∑ U ∈ S, |(coefficient q S T*coefficient q S U)*
        ((∑ j ∈ A, w j*hitMonomial (T∪U) (ω j))-X*∏ i ∈ T∪U, q i)| := by
      apply (abs_sum_le_sum_abs _ _).trans
      exact sum_le_sum (fun T hT => abs_sum_le_sum_abs _ _)
    _ ≤ ∑ T ∈ S, ∑ U ∈ S, |coefficient q S T| * |coefficient q S U| := by
      apply sum_le_sum
      intro T hT
      apply sum_le_sum
      intro U hU
      rw [abs_mul, abs_mul]
      exact mul_le_of_le_one_right (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (herr (T∪U))
    _ = _ := by
      rw [← sum_mul_sum, coefficient_abs_sum_eq_kernelCost q S hS, pow_two]

theorem weighted_survivors_le_cost (q : ι → ℝ) (hq : ∀ i, 0 < q i ∧ q i < 1)
    (S : Finset (Finset ι)) (hSn : S.Nonempty)
    (hS : ∀ T ∈ S, ∀ U ⊆ T, U ∈ S)
    (A : Finset α) (w : α → ℝ) (ω : α → ι → Bool) (X : ℝ)
    (hw : ∀ j ∈ A, 0 ≤ w j)
    (herr : ∀ T : Finset ι,
      |(∑ j ∈ A, w j*hitMonomial T (ω j))-X*∏ i ∈ T, q i| ≤ 1) :
    (∑ j ∈ A, w j*(if ∀ i, ω j i = false then 1 else 0)) ≤
      X/normalizer q S+kernelCost q (canonicalOrthogonal q S)^2 := by
  classical
  have he := (abs_le.mp (majorant_weighted_error_cost q hq S hSn hS A w ω X herr)).2
  have hh : (∑ j ∈ A, w j*(if ∀ i, ω j i = false then 1 else 0)) ≤
      ∑ j ∈ A, w j*majorant q S (ω j) := by
    apply sum_le_sum
    intro j hj
    apply mul_le_mul_of_nonneg_left _ (hw j hj)
    simpa only [funext_iff] using indicator_empty_le_majorant q hq S hSn (ω j)
  linarith


lemma canonical_cost_le_card (q : ι → ℝ) (hq : ∀ i, 0 < q i ∧ q i < 1)
    (S : Finset (Finset ι)) (hSn : S.Nonempty)
    (hS : ∀ T ∈ S, ∀ U ⊆ T, U ∈ S) :
    kernelCost q (canonicalOrthogonal q S) ≤ S.card := by
  rw [← coefficient_abs_sum_eq_kernelCost q S hS]
  calc
    _ ≤ ∑ _T ∈ S, (1 : ℝ) := sum_le_sum (fun T _ => coefficient_abs_le_one q hq S hSn hS T)
    _ = _ := by simp

#print axioms majorant_weighted_error_cost
#print axioms weighted_survivors_le_cost
#print axioms canonical_cost_le_card
end Erdos970.FiniteSelberg
