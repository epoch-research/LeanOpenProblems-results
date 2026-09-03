import Submission.SupportMomentMatrix
import Submission.LowerLawLoss

/-! Safe residual losses from a genuine lower sublaw and upper moments.
This module does not assert any unrestricted covering obstruction. -/
namespace Erdos7SupportLossBound
open scoped BigOperators
open Erdos7SupportCompression Erdos7SupportLowerLaw Erdos7SupportTailIteration
open Erdos7SupportMomentMatrix Erdos7Distortion
set_option autoImplicit false
set_option maxHeartbeats 2000000

lemma pairExpect_test_sub (μ : TripleState →₀ ℚ) (f g : TripleState → ℚ) :
    pairExpect μ (fun x => f x-g x)=pairExpect μ f-pairExpect μ g := by
  simp only [pairExpect,Finsupp.sum,mul_sub,Finset.sum_sub_distrib]

lemma pairExpect_law_mono {μ ν : TripleState →₀ ℚ} (h : μ ≤ ν)
    (f : TripleState → ℚ) (hf : ∀ x, 0 ≤ f x) : pairExpect μ f ≤ pairExpect ν f := by
  unfold pairExpect
  exact Finsupp.sum_le_sum_index h (fun x _ a b hab => mul_le_mul_of_nonneg_right hab (hf x))
    (fun _ _ => by simp)

lemma tripleCount_moments (x : TripleState) : (tripleCount x:ℚ)=mono 0 x+mono 1 x+mono 4 x := by
  norm_num [tripleCount,mono,monoR]
  ring

lemma mean_bound (μ : TripleState →₀ ℚ) (H : Fin 10 → ℚ)
    (h : ∀ i,pairExpect μ (mono i) ≤ H i) :
    pairExpect μ (fun x => (tripleCount x:ℚ)) ≤ H 0+H 1+H 4 := by
  simp only [tripleCount_moments,pairExpect_test_add]
  exact add_le_add (add_le_add (h 0) (h 1)) (h 4)

/-- The lower sublaw is used only in a bounded nonnegative subtraction.
Its missing mass is not silently treated as if it had zero residual loss. -/
theorem residual_loss_upper {I : Type*} [Fintype I] (repr : I → TripleState)
    (D : I → ℚ) (μ : TripleState →₀ ℚ) (hD : encode repr D ≤ μ)
    (c q M : ℚ) (hc : 1 ≤ c) (hq : 0 < q)
    (hM : pairExpect μ (fun x => (tripleCount x:ℚ)) ≤ M) :
    pairExpect μ (fun x => residual c ((tripleCount x:ℚ)/q)) ≤
      c/q*M-∑ j,D j*min (c-1) (c/q*(tripleCount (repr j):ℚ)) := by
  have hc0 : 0 ≤ c := by linarith
  have he (x : TripleState) : residual c ((tripleCount x:ℚ)/q)=
      c/q*(tripleCount x:ℚ)-min (c-1) (c/q*(tripleCount x:ℚ)) := by
    unfold Erdos7Distortion.residual
    rw [show c*((tripleCount x:ℚ)/q)=c/q*(tripleCount x:ℚ) by ring]
    exact Erdos7LowerLawLoss.hinge_sub_min _ _
  have hh := pairExpect_law_mono hD (fun x => min (c-1) (c/q*(tripleCount x:ℚ)))
    (fun x => le_min (by linarith) (by positivity))
  rw [pairExpect_encode] at hh
  simp only [he,pairExpect_test_sub,pairExpect_test_mul]
  exact sub_le_sub (mul_le_mul_of_nonneg_left hM (div_nonneg hc0 hq.le)) hh

#print axioms residual_loss_upper
end Erdos7SupportLossBound
