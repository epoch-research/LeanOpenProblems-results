import FormalConjecturesUtil
import Submission.FiniteOccupancy

/-! The finite occupancy variance bound only needs pairwise nonpositive
covariance, not independence. -/
open Finset
open scoped BigOperators Classical
namespace Erdos713FiniteNegCovOccupancy
variable {I Ω : Type*} [Fintype Ω] [Nonempty Ω]
set_option maxHeartbeats 1000000

lemma variance_le (S : Finset I) (g : I → Ω → ℝ) (p : ℝ)
    (hg : ∀ i ∈ S, ∀ ω, (g i ω)^2 = g i ω)
    (hp : ∀ i ∈ S, (𝔼 ω, g i ω) = p)
    (hij : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → (𝔼 ω, g i ω*g j ω) ≤ p^2) :
    (𝔼 ω, (∑ i ∈ S, g i ω - S.card*p)^2) ≤ S.card*p*(1-p) := by
  classical
  have hd (i : I) (hi : i ∈ S) : (𝔼 ω, (g i ω-p)^2) = p*(1-p) := by
    have he (ω : Ω) : (g i ω-p)^2 = g i ω-2*p*g i ω+p^2 := by
      nlinarith only [hg i hi ω]
    simp_rw [he]
    rw [expect_add_distrib,expect_sub_distrib,← mul_expect,hp i hi,Fintype.expect_const]
    ring
  have ho (i : I) (hi : i ∈ S) (j : I) (hj : j ∈ S) (hne : i ≠ j) :
      (𝔼 ω, (g i ω-p)*(g j ω-p)) ≤ 0 := by
    have he (ω : Ω) : (g i ω-p)*(g j ω-p) =
        g i ω*g j ω-p*g i ω-p*g j ω+p^2 := by ring
    simp_rw [he]
    rw [expect_add_distrib,expect_sub_distrib,expect_sub_distrib,
      ← mul_expect,← mul_expect,hp i hi,hp j hj,Fintype.expect_const]
    nlinarith only [hij i hi j hj hne]
  have he (ω : Ω) : (∑ i ∈ S, g i ω - S.card*p)^2 =
      ∑ i ∈ S, ∑ j ∈ S, (g i ω-p)*(g j ω-p) := by
    rw [← sum_mul_sum,sum_sub_distrib]
    simp only [sum_const,nsmul_eq_mul,pow_two]
  simp_rw [he,expect_sum_comm]
  calc
    _ ≤ ∑ _i ∈ S, p*(1-p) := by
      apply sum_le_sum
      intro i hi
      calc
        _ ≤ ∑ j ∈ S, if j=i then p*(1-p) else 0 := by
          apply sum_le_sum
          intro j hj
          by_cases hji : j = i
          · subst j
            simp only [ite_true,← pow_two,hd i hi,le_refl]
          · simp only [hji,ite_false]
            exact ho i hi j hj (Ne.symm hji)
        _ = _ := by simp only [sum_ite_eq',hi,ite_true]
    _ = _ := by simp only [sum_const,nsmul_eq_mul]; ring

#print axioms variance_le
end Erdos713FiniteNegCovOccupancy
