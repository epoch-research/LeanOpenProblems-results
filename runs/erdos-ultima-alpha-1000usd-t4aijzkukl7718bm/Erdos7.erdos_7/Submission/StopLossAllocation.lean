import Submission.ExclusiveGroupCompression

/-! Stop-loss bounds with freely allocated thresholds. This avoids asserting
independence or a common extremizer for distinct level families. -/
namespace Erdos7StopLossAllocation
open scoped BigOperators
open Erdos7ExclusiveGroupCompression
set_option autoImplicit false
set_option maxHeartbeats 1500000

lemma stopLoss_sum_le {J : Type*} [Fintype J] (v θ : J → ℝ) (k : ℝ)
    (hθ : (∑ j, θ j) ≤ k) :
    max ((∑ j, v j)-k) 0 ≤ ∑ j, max (v j-θ j) 0 := by
  apply max_le
  · calc
      _ ≤ (∑ j, v j)-(∑ j, θ j) := by linarith
      _ = ∑ j, (v j-θ j) := by rw [Finset.sum_sub_distrib]
      _ ≤ _ := Finset.sum_le_sum (fun _ _ => le_max_left _ _)
  · exact Finset.sum_nonneg (fun _ _ => le_max_right _ _)

/-- For a nonnegative threshold, the zero atom contributes nothing. -/
theorem exclusive_stopLoss {Ω : Type*} [Fintype Ω]
    (μ : Ω → ℝ) (hμ : ∀ y, 0 ≤ μ y) (hm : (∑ y, μ y)=1)
    (T S qt qs θ : ℝ) (hT : 0 ≤ T) (hS : 0 ≤ S) (hθ : 0 ≤ θ)
    (t s : Ω → ℝ) (ht : ∀ y, 0 ≤ t y ∧ t y ≤ T)
    (hs : ∀ y, 0 ≤ s y ∧ s y ≤ S) (he : ∀ y, t y*s y=0)
    (hmt : (∑ y, μ y*t y) ≤ qt*T)
    (hms : (∑ y, μ y*s y) ≤ qs*S) :
    (∑ y, μ y*max (t y+s y-θ) 0) ≤ qt*max (T-θ) 0+qs*max (S-θ) 0 := by
  have hc : ConvexOn ℝ Set.univ (fun x : ℝ => max (x-θ) 0) := by
    have ha : ConvexOn ℝ Set.univ (fun x : ℝ => x-θ) := by
      refine ⟨convex_univ, ?_⟩
      intro x hx y hy a b ha hb hab
      simp only [smul_eq_mul]
      nlinarith
    exact ha.sup (convexOn_const 0 convex_univ)
  have hmono : Monotone (fun x : ℝ => max (x-θ) 0) := by
    intro x y hxy
    exact max_le_max (sub_le_sub_right hxy θ) le_rfl
  have hh := exclusive_group_compression μ hμ hm (fun x => max (x-θ) 0)
    hc hmono 0 T S qt qs hT hS t s ht hs he hmt hms
  have hz : max (0-θ) 0=0 := max_eq_right (by linarith)
  simpa only [zero_add, hz, mul_zero, zero_mul] using hh

/-- A finite level sum is bounded by the sum of its exclusive-group stop-loss
costs for ANY nonnegative threshold allocation with total at most k. -/
theorem allocated_exclusive_stopLoss {Ω J : Type*} [Fintype Ω] [Fintype J]
    (μ : Ω → ℝ) (hμ : ∀ y, 0 ≤ μ y) (hm : (∑ y, μ y)=1)
    (T S qt qs θ : J → ℝ) (k : ℝ)
    (hT : ∀ j, 0 ≤ T j) (hS : ∀ j, 0 ≤ S j)
    (hθ : ∀ j, 0 ≤ θ j) (hθk : (∑ j, θ j) ≤ k)
    (t s : J → Ω → ℝ) (ht : ∀ j y, 0 ≤ t j y ∧ t j y ≤ T j)
    (hs : ∀ j y, 0 ≤ s j y ∧ s j y ≤ S j) (he : ∀ j y, t j y*s j y=0)
    (hmt : ∀ j, (∑ y, μ y*t j y) ≤ qt j*T j)
    (hms : ∀ j, (∑ y, μ y*s j y) ≤ qs j*S j) :
    (∑ y, μ y*max ((∑ j, (t j y+s j y))-k) 0) ≤
      ∑ j, (qt j*max (T j-θ j) 0+qs j*max (S j-θ j) 0) := by
  calc
    _ ≤ ∑ y, μ y*(∑ j, max (t j y+s j y-θ j) 0) := by
      apply Finset.sum_le_sum
      intro y _
      exact mul_le_mul_of_nonneg_left (stopLoss_sum_le _ θ k hθk) (hμ y)
    _ = ∑ j, ∑ y, μ y*max (t j y+s j y-θ j) 0 := by
      simp only [Finset.mul_sum]
      exact Finset.sum_comm
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro j _
      exact exclusive_stopLoss μ hμ hm (T j) (S j) (qt j) (qs j) (θ j)
        (hT j) (hS j) (hθ j) (t j) (s j) (ht j) (hs j) (he j) (hmt j) (hms j)

#print axioms stopLoss_sum_le
#print axioms exclusive_stopLoss
#print axioms allocated_exclusive_stopLoss
end Erdos7StopLossAllocation
