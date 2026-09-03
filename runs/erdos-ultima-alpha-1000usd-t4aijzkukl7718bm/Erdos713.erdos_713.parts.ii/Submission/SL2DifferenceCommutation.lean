import FormalConjecturesUtil
import Submission.C8SL2SectionObstruction

/-! Exact commuting differences for the SL2 curve. This verifies an algebraic
limitation of one C8-construction strategy; it is not an extremal bound. -/
open scoped MatrixGroups
namespace Erdos713SL2DifferenceCommutation
open Erdos713C8SL2SectionObstruction
variable {K : Type*} [Field K]
set_option maxHeartbeats 1000000

lemma difference_matrix (a b : K) :
    (↑(curve a*(curve b)⁻¹) : Matrix (Fin 2) (Fin 2) K) =
      !![1+a*(a-b),(a-b)*(1-a*b); a-b,1-b*(a-b)] := by
  rw [Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.SL2_inv_expl]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [curve,Matrix.mul_apply,Fin.sum_univ_two] <;> ring

lemma curve_injective : Function.Injective (curve (K := K)) := by
  intro a b h
  have hh := congrArg (fun M : SL(2,K) => M 0 1) h
  simpa [curve] using hh

/-- Every nonidentity normalized difference remembers its ordered pair. -/
lemma difference_injective_of_ne {a b c d : K} (hab : a ≠ b)
    (h : curve a*(curve b)⁻¹ = curve c*(curve d)⁻¹) : a=c ∧ b=d := by
  have hm := congrArg (fun M : SL(2,K) => (M : Matrix (Fin 2) (Fin 2) K)) h
  simp only [difference_matrix] at hm
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 0) hm
  have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 1 0) hm
  norm_num at h00 h10
  have hz : (a-c)*(a-b) = 0 := by linear_combination h00-c*h10
  have hac : a = c := sub_eq_zero.mp
    ((mul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr hab))
  refine ⟨hac,?_⟩
  linear_combination hac-h10

lemma sum_and_product_of_commute {a b c d : K} (hab : a ≠ b) (hcd : c ≠ d)
    (h : Commute (curve a*(curve b)⁻¹) (curve c*(curve d)⁻¹)) :
    a+b = c+d ∧ a*b = c*d := by
  have hm := congrArg (fun M : SL(2,K) => (M : Matrix (Fin 2) (Fin 2) K)) h.eq
  change (↑(curve a*(curve b)⁻¹) : Matrix (Fin 2) (Fin 2) K)*
      (↑(curve c*(curve d)⁻¹) : Matrix (Fin 2) (Fin 2) K) =
      (↑(curve c*(curve d)⁻¹) : Matrix (Fin 2) (Fin 2) K)*
      (↑(curve a*(curve b)⁻¹) : Matrix (Fin 2) (Fin 2) K) at hm
  simp only [difference_matrix] at hm
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 0) hm
  have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 1 0) hm
  norm_num [Matrix.mul_apply,Fin.sum_univ_two] at h00 h10
  have hzprod : (a-b)*(c-d)*(a*b-c*d) = 0 := by linear_combination -h00
  have hzsum : (a-b)*(c-d)*(a+b-c-d) = 0 := by linear_combination -h10
  have hn : (a-b)*(c-d) ≠ 0 := mul_ne_zero (sub_ne_zero.mpr hab) (sub_ne_zero.mpr hcd)
  have hp := (mul_eq_zero.mp hzprod).resolve_left hn
  have hs := (mul_eq_zero.mp hzsum).resolve_left hn
  constructor
  · linear_combination hs
  · exact sub_eq_zero.mp hp

lemma unordered_pair_of_sum_product {a b c d : K}
    (hs : a+b = c+d) (hp : a*b = c*d) :
    (a=c ∧ b=d) ∨ (a=d ∧ b=c) := by
  have hz : (a-c)*(a-d) = 0 := by linear_combination a*hs-hp
  rcases mul_eq_zero.mp hz with he | he
  · have ha : a = c := sub_eq_zero.mp he
    left
    refine ⟨ha,?_⟩
    rw [ha] at hs
    exact add_left_cancel hs
  · have ha : a = d := sub_eq_zero.mp he
    right
    refine ⟨ha,?_⟩
    rw [ha,add_comm c d] at hs
    exact add_left_cancel hs

lemma commute_iff (a b c d : K) :
    Commute (curve a*(curve b)⁻¹) (curve c*(curve d)⁻¹) ↔
      a=b ∨ c=d ∨ (a=c ∧ b=d) ∨ (a=d ∧ b=c) := by
  constructor
  · intro h
    by_cases hab : a = b
    · exact Or.inl hab
    by_cases hcd : c = d
    · exact Or.inr (Or.inl hcd)
    obtain ⟨hs,hp⟩ := sum_and_product_of_commute hab hcd h
    exact Or.inr (Or.inr (unordered_pair_of_sum_product hs hp))
  · rintro (rfl | rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
    · simp
    · simp
    · exact Commute.refl _
    · simpa only [mul_inv_rev,inv_inv] using
        (Commute.refl (curve a*(curve b)⁻¹)).inv_right

/-- Adding arbitrary group coordinates cannot produce two commuting
normalized differences except identities, repeats, or inverses. Thus it does
not repair this particular commuting-difference construction route. -/
lemma lifted_commuting_degenerate {W : Type*} [Group W] (f : K → W)
    (a b c d : K)
    (h : Commute (generator f a*(generator f b)⁻¹)
      (generator f c*(generator f d)⁻¹)) :
    generator f a*(generator f b)⁻¹ = 1 ∨
      generator f c*(generator f d)⁻¹ = 1 ∨
      generator f a*(generator f b)⁻¹ = generator f c*(generator f d)⁻¹ ∨
      generator f a*(generator f b)⁻¹ = (generator f c*(generator f d)⁻¹)⁻¹ := by
  have hc : Commute (curve a*(curve b)⁻¹) (curve c*(curve d)⁻¹) := by
    change (curve a*(curve b)⁻¹)*(curve c*(curve d)⁻¹) =
      (curve c*(curve d)⁻¹)*(curve a*(curve b)⁻¹)
    exact congrArg Prod.fst h.eq
  rcases (commute_iff a b c d).mp hc with hab | hcd | ⟨hac,hbd⟩ | ⟨had,hbc⟩
  · left
    simp [hab]
  · right
    left
    simp [hcd]
  · right
    right
    left
    simp only [hac,hbd]
  · right
    right
    right
    simp only [had,hbc,mul_inv_rev,inv_inv]

#print axioms difference_matrix
#print axioms difference_injective_of_ne
#print axioms sum_and_product_of_commute
#print axioms commute_iff
#print axioms lifted_commuting_degenerate
end Erdos713SL2DifferenceCommutation
