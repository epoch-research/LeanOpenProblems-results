import Submission.GreedyWeightedDissipation

/-!
A deterministic coupled quadratic budget for normalized residual-degree
errors. The leading t^2 self damping absorbs the higher-degree neighbor
coupling, leaving only growth of order 1+t. This is an operator inequality,
not an assertion that a random trajectory satisfies its hypotheses.
-/
namespace Erdos773.GreedyNormalizedEnergyBudget
open Finset GreedyWeightedDissipation
set_option maxHeartbeats 2500000

lemma scalar_budget (A t M2 M3 M4 T23 T34 T32 T42 : ℝ)
    (hA : 0 ≤ A) (ht : 0 ≤ t) (hM2 : 0 ≤ M2) (hM3 : 0 ≤ M3) (hM4 : 0 ≤ M4)
    (h23 : 2*T23 ≤ M2+M3) (h34 : 2*T34 ≤ M3+M4)
    (h32 : 2*(t+1)*T32 ≤ A*(6*t+2)*((t+1)^2*M3+M2))
    (h42 : 2*T42 ≤ 6*A*(M4+M2)) :
    2*A*T23+3*A*T34+T32+T42-3*A*t^2*(M3+M4) ≤
      A*(8+4*t)*(M2+M3+M4) := by
  have hb32 : T32 ≤ A*((3*t^2+4*t+1)*M3+3*M2) := by
    apply le_of_mul_le_mul_left (a := 2*(t+1)) ?_ (by positivity)
    apply h32.trans
    have he : 2*(t+1)*(A*((3*t^2+4*t+1)*M3+3*M2))-
        A*(6*t+2)*((t+1)^2*M3+M2) = 4*A*M2 := by ring
    have hp : 0 ≤ 4*A*M2 := by positivity
    linarith only [he,hp]
  have hb23 : 2*A*T23 ≤ A*(M2+M3) := by
    nlinarith only [mul_le_mul_of_nonneg_left h23 hA]
  have hb34 : 3*A*T34 ≤ (3/2:ℝ)*A*(M3+M4) := by
    nlinarith only [mul_le_mul_of_nonneg_left h34 (show 0 ≤ (3/2:ℝ)*A by positivity)]
  have hb42 : T42 ≤ 3*A*(M4+M2) := by linarith only [h42]
  have hscalar :
      A*(M2+M3)+(3/2:ℝ)*A*(M3+M4)+A*((3*t^2+4*t+1)*M3+3*M2)+
        3*A*(M4+M2)-3*A*t^2*(M3+M4) ≤ A*(8+4*t)*(M2+M3+M4) := by
    have he : A*(8+4*t)*(M2+M3+M4)-
        (A*(M2+M3)+(3/2:ℝ)*A*(M3+M4)+A*((3*t^2+4*t+1)*M3+3*M2)+
          3*A*(M4+M2)-3*A*t^2*(M3+M4)) =
        A*((1+4*t)*M2+(9/2:ℝ)*M3+((7/2:ℝ)+4*t+3*t^2)*M4) := by ring
    have hp : 0 ≤ A*((1+4*t)*M2+(9/2:ℝ)*M3+((7/2:ℝ)+4*t+3*t^2)*M4) := by positivity
    linarith only [he,hp]
  linarith only [hb23,hb34,hb32,hb42,hscalar]

/-- Bilinear cross-component terms at the normalizations A and A^2 have
no t^2 growth left after the self damping is retained. -/
theorem coupled_budget {α : Type*} (S : Finset α) (x2 x3 x4 : α → ℝ)
    (W2 W3 W4 : α → α → ℝ) (A t : ℝ) (hA : 0 ≤ A) (ht : 0 ≤ t)
    (hS2 : ∀ u ∈ S, ∀ v ∈ S, W2 u v = W2 v u)
    (hS3 : ∀ u ∈ S, ∀ v ∈ S, W3 u v = W3 v u)
    (hS4 : ∀ u ∈ S, ∀ v ∈ S, W4 u v = W4 v u)
    (hW2 : ∀ u ∈ S, ∀ v ∈ S, 0 ≤ W2 u v)
    (hW3 : ∀ u ∈ S, ∀ v ∈ S, 0 ≤ W3 u v)
    (hW4 : ∀ u ∈ S, ∀ v ∈ S, 0 ≤ W4 u v)
    (hrow3 : ∀ u ∈ S, (∑ v ∈ S, W3 u v) ≤ A*(6*t+2))
    (hrow4 : ∀ u ∈ S, (∑ v ∈ S, W4 u v) ≤ 6*A) :
    (∑ u ∈ S, x2 u*(2*A*x3 u-
      ((∑ v ∈ S, W2 u v)*x2 u+∑ v ∈ S, W2 u v*x2 v)))+
    (∑ u ∈ S, x3 u*(3*A*x4 u-3*A*t^2*x3 u-∑ v ∈ S, W3 u v*x2 v))+
    (∑ u ∈ S, x4 u*(-3*A*t^2*x4 u-∑ v ∈ S, W4 u v*x2 v)) ≤
      A*(8+4*t)*((∑ u ∈ S, (x2 u)^2)+(∑ u ∈ S, (x3 u)^2)+(∑ u ∈ S, (x4 u)^2)) := by
  let M2 := ∑ u ∈ S, (x2 u)^2
  let M3 := ∑ u ∈ S, (x3 u)^2
  let M4 := ∑ u ∈ S, (x4 u)^2
  let T23 := ∑ u ∈ S, x2 u*x3 u
  let T34 := ∑ u ∈ S, x3 u*x4 u
  let T32 := ∑ u ∈ S, ∑ v ∈ S, W3 u v*(-x3 u)*x2 v
  let T42 := ∑ u ∈ S, ∑ v ∈ S, W4 u v*(-x4 u)*x2 v
  have h23 : 2*T23 ≤ M2+M3 := by
    have hh := sum_le_sum (s := S) (fun u _ =>
      show 2*(x2 u*x3 u) ≤ (x2 u)^2+(x3 u)^2 by nlinarith only [sq_nonneg (x2 u-x3 u)])
    simpa only [← mul_sum,sum_add_distrib] using hh
  have h34 : 2*T34 ≤ M3+M4 := by
    have hh := sum_le_sum (s := S) (fun u _ =>
      show 2*(x3 u*x4 u) ≤ (x3 u)^2+(x4 u)^2 by nlinarith only [sq_nonneg (x3 u-x4 u)])
    simpa only [← mul_sum,sum_add_distrib] using hh
  have h32 : 2*(t+1)*T32 ≤ A*(6*t+2)*((t+1)^2*M3+M2) := by
    simpa only [even_two.neg_pow] using
      bilinear_bound S W3 (fun u => -x3 u) x2 hS3 hW3 (A*(6*t+2)) (t+1) hrow3
  have h42 : 2*T42 ≤ 6*A*(M4+M2) := by
    simpa only [even_two.neg_pow,one_pow,mul_one,one_mul] using
      bilinear_bound S W4 (fun u => -x4 u) x2 hS4 hW4 (6*A) 1 hrow4
  have hb := scalar_budget A t M2 M3 M4 T23 T34 T32 T42 hA ht
    (sum_nonneg (fun u _ => sq_nonneg (x2 u)))
    (sum_nonneg (fun u _ => sq_nonneg (x3 u)))
    (sum_nonneg (fun u _ => sq_nonneg (x4 u))) h23 h34 h32 h42
  have hd := nonnegative S W2 x2 id hS2 hW2 monotone_id (fun _ => rfl)
  have he2 : (∑ u ∈ S, x2 u*(2*A*x3 u-
      ((∑ v ∈ S, W2 u v)*x2 u+∑ v ∈ S, W2 u v*x2 v))) =
      2*A*T23-(∑ u ∈ S, x2 u*((∑ v ∈ S, W2 u v)*x2 u+∑ v ∈ S, W2 u v*x2 v)) := by
    rw [mul_sum,← sum_sub_distrib]
    apply sum_congr rfl
    intro u hu
    ring
  have he3 : (∑ u ∈ S, x3 u*(3*A*x4 u-3*A*t^2*x3 u-∑ v ∈ S, W3 u v*x2 v)) =
      3*A*T34-3*A*t^2*M3+T32 := by
    dsimp only [T34,M3,T32]
    rw [mul_sum,mul_sum,← sum_sub_distrib,← sum_add_distrib]
    apply sum_congr rfl
    intro u hu
    have hh : (∑ v ∈ S, W3 u v*(-x3 u)*x2 v) =
        -x3 u*(∑ v ∈ S, W3 u v*x2 v) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro v hv
      ring
    rw [hh]
    ring
  have he4 : (∑ u ∈ S, x4 u*(-3*A*t^2*x4 u-∑ v ∈ S, W4 u v*x2 v)) =
      -3*A*t^2*M4+T42 := by
    dsimp only [M4,T42]
    rw [mul_sum,← sum_add_distrib]
    apply sum_congr rfl
    intro u hu
    have hh : (∑ v ∈ S, W4 u v*(-x4 u)*x2 v) =
        -x4 u*(∑ v ∈ S, W4 u v*x2 v) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro v hv
      ring
    rw [hh]
    ring
  rw [he2,he3,he4]
  change _ ≤ A*(8+4*t)*(M2+M3+M4)
  simp only [id_eq] at hd
  nlinarith only [hb,hd]

#print axioms scalar_budget
#print axioms coupled_budget
end Erdos773.GreedyNormalizedEnergyBudget
