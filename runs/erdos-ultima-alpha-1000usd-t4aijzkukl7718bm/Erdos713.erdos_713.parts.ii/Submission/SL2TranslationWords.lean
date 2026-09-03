import FormalConjecturesUtil
import Submission.SL2DifferenceCommutation
import Submission.C8InvolutiveSidonWord

/-! A two-parameter SL2 word identity in characteristic two, together
with its exact voltage condition. No extremal exponent is asserted. -/
open SimpleGraph
open scoped MatrixGroups
namespace Erdos713SL2TranslationWords
open Erdos713C8SL2SectionObstruction Erdos713SL2DifferenceCommutation
variable {K W : Type*} [Field K] [CharP K 2] [CommGroup W]
set_option maxHeartbeats 2000000

lemma shift_involutive : Function.Involutive (fun a : K => a+1) := by
  intro a
  linear_combination CharTwo.two_eq_zero (R := K)

omit [CharP K 2] in
lemma shift_ne (a : K) : a+1 ≠ a := by
  intro h
  exact one_ne_zero (add_left_cancel (h.trans (add_zero a).symm))

lemma curve_word (r c d : K) :
    curve (r+1)*(curve r)⁻¹*curve c*(curve d)⁻¹ =
      curve r*(curve (c+1))⁻¹*curve d*(curve (d+1))⁻¹ := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [curve,Matrix.SpecialLinearGroup.SL2_inv_expl,Matrix.mul_apply,Fin.sum_univ_two,
      CharTwo.neg_eq,Matrix.vecMul,dotProduct] <;> ring_nf <;> reduce_mod_char!

def ratio (f : K → W) (a : K) : W := f a^2*(f (a+1))⁻¹

lemma ratio_pair (f : K → W) (a : K) : ratio f a*ratio f (a+1) = f a*f (a+1) := by
  simp [ratio,shift_involutive a,pow_two,mul_comm,mul_left_comm,mul_assoc]

lemma voltage_word (f : K → W) (r c d : K)
    (hv : ratio f c*ratio f (c+1) = ratio f r*ratio f d) :
    f (r+1)*(f r)⁻¹*f c*(f d)⁻¹ =
      f r*(f (c+1))⁻¹*f d*(f (d+1))⁻¹ := by
  rw [ratio_pair] at hv
  have hc : f c = (ratio f r*ratio f d)*(f (c+1))⁻¹ := by
    rw [← hv]
    simp [mul_assoc]
  conv_lhs => rw [hc]
  calc
    _ = (f r*(f r)⁻¹)*(f d*(f d)⁻¹)*(f (r+1)*(f (r+1))⁻¹)*
        (f r*(f (c+1))⁻¹*f d*(f (d+1))⁻¹) := by
      simp only [ratio,pow_two]
      ac_rfl
    _ = _ := by simp

/-- Only c outside the two parameter pairs is needed. The two endpoint
parameters r and d may coincide. -/
theorem contains_at (f : K → W) (r c d : K)
    (hcr : c ≠ r) (hcr' : c ≠ r+1) (hcd : c ≠ d) (hcd' : c ≠ d+1)
    (hv : ratio f c*ratio f (c+1) = ratio f r*ratio f d) :
    cycleGraph 8 ⊑ Erdos713C8CommutingDifferences.graph (generator f) := by
  apply Erdos713C8InvolutiveSidonWord.contains (generator f)
    (fun _ _ h => curve_injective (congrArg Prod.fst h))
    (fun a b c d hab h => difference_injective_of_ne hab (congrArg Prod.fst h))
    (fun a => a+1) shift_involutive shift_ne r c d hcr hcr' hcd hcd'
  apply Prod.ext
  · exact curve_word r c d
  · exact voltage_word f r c d hv

#print axioms curve_word
#print axioms contains_at
end Erdos713SL2TranslationWords
