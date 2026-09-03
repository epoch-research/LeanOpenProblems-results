import FormalConjecturesUtil
import Submission.C8InvolutionProduct

/-! A full characteristic-two SL2 section with arbitrary exponent-two
auxiliary coordinates always contains C8. This is a construction obstruction,
not a proof or disproof of the rational-exponent conjecture. -/
open SimpleGraph
open scoped MatrixGroups
namespace Erdos713C8SL2SectionObstruction
variable {K : Type*} [Field K]
set_option maxHeartbeats 1000000

def curve (a : K) : SL(2,K) :=
  ⟨!![1+a^2,a; a,1],by simp only [Matrix.det_fin_two_of]; ring⟩

@[simp] lemma curve_zero : curve (0 : K) = 1 := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [curve]

lemma curve_ne_one {a : K} (ha : a ≠ 0) : curve a ≠ 1 := by
  intro h
  have he := congrArg (fun M : SL(2,K) => M 0 1) h
  exact ha (by simpa only [curve,Matrix.SpecialLinearGroup.coe_mk,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,Matrix.head_fin_const,
    Matrix.SpecialLinearGroup.coe_one,Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1)] using he)

lemma curve_pair_ne_one {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) : curve a*curve b ≠ 1 := by
  intro h
  have he := congrArg (fun M : SL(2,K) => M 1 1) h
  have hh : a*b+1 = (1 : K) := by
    simpa [curve,Matrix.mul_apply,Fin.sum_univ_two] using he
  exact (mul_ne_zero ha hb) (add_right_cancel (hh.trans (zero_add 1).symm))

variable [CharP K 2]

lemma sl2_involution_of_diagonal_eq (M : SL(2,K)) (hdiag : M 0 0 = M 1 1) : M^2 = 1 := by
  have hi : M⁻¹ = M := by
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [CharTwo.neg_eq,hdiag]
  calc
    M^2 = M*M := pow_two _
    _ = M*M⁻¹ := congrArg (fun x => M*x) hi.symm
    _ = 1 := mul_inv_cancel _

lemma curve_pair_square {a b : K} (hab : a*b+a+b = 0) : (curve a*curve b)^2 = 1 := by
  apply sl2_involution_of_diagonal_eq
  simp only [curve,Matrix.SpecialLinearGroup.coe_mul,
    Matrix.mul_apply,Fin.sum_univ_two]
  change ((1+a^2)*(1+b^2)+a*b) = a*b+1*1
  rw [one_mul]
  have hs := congrArg (fun x : K => x^2) hab
  ring_nf at hs ⊢
  reduce_mod_char! at hs ⊢
  linear_combination hs

lemma partner_relation {a : K} (ha : a ≠ 1) : a*(a/(a+1))+a+a/(a+1) = 0 := by
  have hden : a+1 ≠ 0 := by simpa only [← CharTwo.sub_eq_add,sub_ne_zero] using ha
  field_simp
  ring_nf
  reduce_mod_char!

variable {W : Type*} [Group W]

def generator (f : K → W) (a : K) : SL(2,K) × W := (curve a,f a)

omit [CharP K 2] in
@[simp] lemma fst_normalized (f : K → W) (a : K) :
    ((generator f a)*(generator f 0)⁻¹).1 = curve a := by
  simp [generator]

/-- No regularity, additivity, or polynomial form is required of the
auxiliary coordinate function. Its codomain only needs exponent two. -/
theorem contains_section_at (f : K → W) (hW : ∀ w : W, w^2 = 1)
    (a : K) (ha : a ≠ 0) (ha1 : a ≠ 1) :
    cycleGraph 8 ⊑ Erdos713C8CommutingDifferences.graph (generator f) := by
  let b := a/(a+1)
  have hden : a+1 ≠ 0 := by simpa only [← CharTwo.sub_eq_add,sub_ne_zero] using ha1
  have hb : b ≠ 0 := div_ne_zero ha hden
  apply Erdos713C8InvolutionProduct.contains (generator f) a b 0
  · intro h
    apply curve_ne_one ha
    simpa only [Prod.fst_one,fst_normalized] using congrArg Prod.fst h
  · intro h
    apply curve_ne_one hb
    simpa only [Prod.fst_one,fst_normalized] using congrArg Prod.fst h
  · intro h
    apply curve_pair_ne_one ha hb
    simpa [generator] using congrArg Prod.fst h
  · apply Prod.ext
    · change ((curve a*(curve 0)⁻¹)*(curve b*(curve 0)⁻¹))^2 = 1
      simpa only [curve_zero,inv_one,mul_one] using curve_pair_square (partner_relation ha1)
    · exact hW _

/-- In particular this rules out every full section over a finite
characteristic-two field larger than F2, even with extra coordinates. -/
theorem contains_section [Fintype K] (f : K → W) (hW : ∀ w : W, w^2 = 1)
    (hq : 2 < Fintype.card K) :
    cycleGraph 8 ⊑ Erdos713C8CommutingDifferences.graph (generator f) := by
  classical
  obtain ⟨a,_ha,ha⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show ({0,1} : Finset K).card < (Finset.univ : Finset K).card from
      Finset.card_le_two.trans_lt (by simpa using hq))
  simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at ha
  exact contains_section_at f hW a ha.1 ha.2

/-- Arbitrary scalar additive potentials are included. -/
theorem contains_scalar_potential [Fintype K] (f : K → K) (hq : 2 < Fintype.card K) :
    cycleGraph 8 ⊑ Erdos713C8CommutingDifferences.graph
      (generator (fun a => Multiplicative.ofAdd (f a))) := by
  apply contains_section _ ?_ hq
  intro w
  rw [pow_two]
  change Multiplicative.ofAdd (Multiplicative.toAdd w+Multiplicative.toAdd w) =
    Multiplicative.ofAdd (0 : K)
  exact congrArg Multiplicative.ofAdd (CharTwo.add_self_eq_zero _)

#print axioms curve_pair_square
#print axioms contains_section
#print axioms contains_scalar_potential
end Erdos713C8SL2SectionObstruction
