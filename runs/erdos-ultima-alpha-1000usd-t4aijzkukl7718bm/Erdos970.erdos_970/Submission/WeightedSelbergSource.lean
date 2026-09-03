import Submission.SelbergInterval
import Submission.SelbergPrimes

/-! A finite Selberg upper source for arbitrary nonnegative weighted populations.
This version permits a nonintegral expected mass and conditional populations.
Every unit intersection error is charged in the support-squared remainder. -/
namespace Erdos970.FiniteSelberg
open Finset
variable {ι α : Type*} [Fintype ι] [DecidableEq ι]

/-- Weighted analogue of `majorant_interval_error`. -/
theorem majorant_weighted_error (q : ι → ℝ) (hq : ∀ i, 0 < q i ∧ q i < 1)
    (S : Finset (Finset ι)) (hSn : S.Nonempty)
    (hS : ∀ T ∈ S, ∀ U ⊆ T, U ∈ S)
    (A : Finset α) (w : α → ℝ) (ω : α → ι → Bool) (X : ℝ)
    (herr : ∀ T : Finset ι,
      |(∑ j ∈ A, w j*hitMonomial T (ω j))-X*∏ i ∈ T, q i| ≤ 1) :
    |(∑ j ∈ A, w j*majorant q S (ω j))-X/normalizer q S| ≤ (S.card : ℝ)^2 := by
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
    _ ≤ ∑ T ∈ S, ∑ U ∈ S, (1 : ℝ) := by
      apply sum_le_sum
      intro T hT
      apply sum_le_sum
      intro U hU
      rw [abs_mul, abs_mul]
      have hc : |coefficient q S T| * |coefficient q S U| ≤ 1 := by
        simpa using mul_le_mul (coefficient_abs_le_one q hq S hSn hS T)
          (coefficient_abs_le_one q hq S hSn hS U) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      simpa using mul_le_mul hc (herr (T∪U)) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    _ = _ := by simp [pow_two]

/-- A conditional population can use the same upper square, independently of
whether its expected mass is an integer or its total weight is exact. -/
theorem weighted_survivors_le (q : ι → ℝ) (hq : ∀ i, 0 < q i ∧ q i < 1)
    (S : Finset (Finset ι)) (hSn : S.Nonempty)
    (hS : ∀ T ∈ S, ∀ U ⊆ T, U ∈ S)
    (A : Finset α) (w : α → ℝ) (ω : α → ι → Bool) (X : ℝ)
    (hw : ∀ j ∈ A, 0 ≤ w j)
    (herr : ∀ T : Finset ι,
      |(∑ j ∈ A, w j*hitMonomial T (ω j))-X*∏ i ∈ T, q i| ≤ 1) :
    (∑ j ∈ A, w j*(if ∀ i, ω j i = false then 1 else 0)) ≤
      X/normalizer q S+(S.card : ℝ)^2 := by
  classical
  have he := (abs_le.mp (majorant_weighted_error q hq S hSn hS A w ω X herr)).2
  have hh : (∑ j ∈ A, w j*(if ∀ i, ω j i = false then 1 else 0)) ≤
      ∑ j ∈ A, w j*majorant q S (ω j) := by
    apply sum_le_sum
    intro j hj
    apply mul_le_mul_of_nonneg_left _ (hw j hj)
    simpa only [funext_iff] using indicator_empty_le_majorant q hq S hSn (ω j)
  linarith

/-- At square-root divisor cutoff the base error is no greater than the level. -/
theorem prime_weighted_survivors_le_level (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hpinj : Function.Injective p) (A : Finset α) (w : α → ℝ)
    (ω : α → ι → Bool) (X D : ℝ) (hD : 1 ≤ D) (hw : ∀ j ∈ A, 0 ≤ w j)
    (herr : ∀ T : Finset ι,
      |(∑ j ∈ A, w j*hitMonomial T (ω j))-X*∏ i ∈ T, 1/(p i : ℝ)| ≤ 1) :
    (∑ j ∈ A, w j*(if ∀ i, ω j i = false then 1 else 0)) ≤
      X/normalizer (fun i => 1/(p i : ℝ)) (divisorSupport p ⌊Real.sqrt D⌋₊)+D := by
  have hR : 0 < ⌊Real.sqrt D⌋₊ := Nat.floor_pos.mpr (by
    simpa using Real.sqrt_le_sqrt hD)
  have hq (i : ι) : 0 < 1/(p i : ℝ) ∧ 1/(p i : ℝ) < 1 := by
    have hi : (1 : ℝ) < p i := by exact_mod_cast (hp i).one_lt
    exact ⟨by positivity, (div_lt_one (by linarith)).mpr hi⟩
  have hs := weighted_survivors_le (fun i => 1/(p i : ℝ)) hq
    (divisorSupport p ⌊Real.sqrt D⌋₊) (divisorSupport_nonempty p _ hR)
      (divisorSupport_downward p (fun i => (hp i).pos) _) A w ω X hw herr
  have hc := divisorSupport_card_le p hp hpinj ⌊Real.sqrt D⌋₊
  have hcR : ((divisorSupport p ⌊Real.sqrt D⌋₊).card : ℝ) ≤ Real.sqrt D :=
    (Nat.cast_le.mpr hc).trans (Nat.floor_le (Real.sqrt_nonneg D))
  have hsq : ((divisorSupport p ⌊Real.sqrt D⌋₊).card : ℝ)^2 ≤ D := by
    have hh := sq_le_sq₀ (Nat.cast_nonneg _) (Real.sqrt_nonneg D) |>.mpr hcR
    simpa only [Real.sq_sqrt (by linarith : 0 ≤ D)] using hh
  linarith

#print axioms majorant_weighted_error
#print axioms prime_weighted_survivors_le_level
end Erdos970.FiniteSelberg
