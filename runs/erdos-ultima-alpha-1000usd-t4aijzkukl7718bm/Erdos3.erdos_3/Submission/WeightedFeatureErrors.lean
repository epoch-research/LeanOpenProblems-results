import Submission.FeatureLipschitzEnvelope

/-! Finite weighted Minkowski estimates for feature-factor approximation.
Different coordinates retain different L2 error budgets; no maximum-error
replacement or extra factor of the number of features is introduced. -/
namespace Erdos3WeightedFeatureErrors
open Finset Erdos3FeatureLipschitzEnvelope
open scoped BigOperators Classical
set_option maxHeartbeats 4000000

variable {I X : Type*} [Fintype I] [Fintype X]

lemma mean_abs_product_le (f g : X → ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hf : (𝔼 x : X, (f x)^2) ≤ a^2) (hg : (𝔼 x : X, (g x)^2) ≤ b^2) :
    (𝔼 x : X, |f x| * |g x|) ≤ a*b := by
  have h := expect_mul_sq_le_sq_mul_sq univ (fun x : X ↦ |f x|) (fun x ↦ |g x|)
  simp only [sq_abs] at h
  have hp : (𝔼 x : X, (f x)^2)*(𝔼 x : X, (g x)^2) ≤ a^2*b^2 :=
    mul_le_mul hf hg (expect_nonneg (fun _ _ ↦ sq_nonneg _)) (sq_nonneg a)
  rw [← mul_pow] at hp
  exact le_of_pow_le_pow_left₀ (by decide : (2 : ℕ) ≠ 0) (mul_nonneg ha hb) (h.trans hp)

lemma square_sum (f : I → ℝ) : (∑ i : I, f i)^2 = ∑ i : I, ∑ j : I, f i*f j := by
  rw [sq,sum_mul]
  simp only [mul_sum]

/-- Normalized L2 errors add according to their weighted L2 sizes. -/
theorem weighted_minkowski_square (w : I → NNReal) (f : I → X → ℝ)
    (ε : I → ℝ) (hε : ∀ i, 0 ≤ ε i)
    (hf : ∀ i, (𝔼 x : X, (f i x)^2) ≤ (ε i)^2) :
    (𝔼 x : X, (∑ i : I, (w i : ℝ)*|f i x|)^2) ≤
      (∑ i : I, (w i : ℝ)*ε i)^2 := by
  simp only [square_sum]
  rw [expect_sum_comm]
  apply sum_le_sum
  intro i _
  rw [expect_sum_comm]
  apply sum_le_sum
  intro j _
  have he (x : X) : ((w i : ℝ)*|f i x|)*((w j : ℝ)*|f j x|) =
      ((w i : ℝ)*(w j : ℝ))*(|f i x| * |f j x|) := by ring
  simp only [he,← mul_expect]
  have h := mul_le_mul_of_nonneg_left
    (mean_abs_product_le (f i) (f j) (hε i) (hε j) (hf i) (hf j))
    (mul_nonneg (w i).coe_nonneg (w j).coe_nonneg)
  convert h using 1 <;> ring

/-- A factor controlled by weighted coordinate distance inherits the weighted
sum of coordinate L2 errors, with no dimension loss. -/
theorem weighted_factor_mean_square (w : I → NNReal) (Φ : (I → ℝ) → ℝ)
    (hΦ : ∀ v u, |Φ v-Φ u| ≤ weightedDistance w v u)
    (f g : I → X → ℝ) (ε : I → ℝ) (hε : ∀ i, 0 ≤ ε i)
    (herr : ∀ i, (𝔼 x : X, (f i x-g i x)^2) ≤ (ε i)^2) :
    (𝔼 x : X, (Φ (fun i ↦ f i x)-Φ (fun i ↦ g i x))^2) ≤
      (∑ i : I, (w i : ℝ)*ε i)^2 := by
  calc
    _ ≤ 𝔼 x : X, (∑ i : I, (w i : ℝ)*|f i x-g i x|)^2 := by
      apply expect_le_expect
      intro x _
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _)
        (hΦ (fun i ↦ f i x) (fun i ↦ g i x)) 2
    _ ≤ _ := weighted_minkowski_square w (fun i x ↦ f i x-g i x) ε hε herr

/-- A total error budget can be enforced before choosing the final feature
count, provided the individual weighted budgets have a bounded sum. -/
theorem weighted_factor_error_budget (w : I → NNReal) (Φ : (I → ℝ) → ℝ)
    (hΦ : ∀ v u, |Φ v-Φ u| ≤ weightedDistance w v u)
    (f g : I → X → ℝ) (ε : I → ℝ) (hε : ∀ i, 0 ≤ ε i) {τ : ℝ}
    (hτ : 0 ≤ τ) (hbudget : (∑ i : I, (w i : ℝ)*ε i) ≤ τ)
    (herr : ∀ i, (𝔼 x : X, (f i x-g i x)^2) ≤ (ε i)^2) :
    (𝔼 x : X, (Φ (fun i ↦ f i x)-Φ (fun i ↦ g i x))^2) ≤ τ^2 := by
  apply (weighted_factor_mean_square w Φ hΦ f g ε hε herr).trans
  exact pow_le_pow_left₀ (sum_nonneg (fun i _ ↦ mul_nonneg (w i).coe_nonneg (hε i))) hbudget 2

#print axioms weighted_minkowski_square
#print axioms weighted_factor_mean_square
end Erdos3WeightedFeatureErrors
