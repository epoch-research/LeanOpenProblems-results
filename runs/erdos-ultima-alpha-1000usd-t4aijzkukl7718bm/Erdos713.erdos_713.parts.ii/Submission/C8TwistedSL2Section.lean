import FormalConjecturesUtil
import Submission.C8SL2SectionObstruction

/-! A field-endomorphism twist does not rescue the SL2 section with
exponent-two auxiliary voltages. This is a construction obstruction only,
not a proof of the rationality conjecture. -/
open SimpleGraph
open scoped MatrixGroups
namespace Erdos713C8TwistedSL2Section
variable {K : Type*} [Field K]
set_option maxHeartbeats 2000000

/-- The product of the upper unipotent at a and the lower unipotent at φ(a). -/
def curve (φ : K →+* K) (a : K) : SL(2,K) :=
  ⟨!![1+a*φ a,a; φ a,1],by simp only [Matrix.det_fin_two_of]; ring⟩

@[simp] lemma curve_zero (φ : K →+* K) : curve φ 0 = 1 := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [curve]

lemma curve_injective (φ : K →+* K) : Function.Injective (curve φ) := by
  intro a b h
  have he := congrArg (fun M : SL(2,K) => M 0 1) h
  simpa [curve] using he

lemma curve_ne_one (φ : K →+* K) {a : K} (ha : a ≠ 0) : curve φ a ≠ 1 := by
  intro h
  apply ha
  apply curve_injective φ
  simpa only [curve_zero] using h

lemma curve_pair_ne_one (φ : K →+* K) {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) :
    curve φ a*curve φ b ≠ 1 := by
  intro h
  have he := congrArg (fun M : SL(2,K) => M 1 1) h
  have hh : φ a*b+1 = (1 : K) := by
    simpa [curve,Matrix.mul_apply,Fin.sum_univ_two] using he
  exact (mul_ne_zero ((map_ne_zero φ).mpr ha) hb)
    (add_right_cancel (hh.trans (zero_add 1).symm))

variable [CharP K 2]

/-- The trace is (a+b)φ(a+b)+(ab)φ(ab), so ab=a+b makes it zero. -/
lemma curve_pair_square (φ : K →+* K) {a b : K} (hab : a*b+a+b = 0) :
    (curve φ a*curve φ b)^2 = 1 := by
  apply Erdos713C8SL2SectionObstruction.sl2_involution_of_diagonal_eq
  have he : a*b = a+b := by
    linear_combination hab - (a+b)*(CharP.cast_eq_zero K 2)
  have hp : φ a*φ b = φ a+φ b := by
    simpa only [map_mul,map_add] using congrArg φ he
  simp only [curve,Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two]
  change (1+a*φ a)*(1+b*φ b)+a*φ b = φ a*b+1*1
  linear_combination (φ a*φ b)*he + (a+b)*hp +
    (a*φ a+a*φ b+b*φ b)*(CharP.cast_eq_zero K 2)

variable {W : Type*} [Group W]

def generator (φ : K →+* K) (f : K → W) (a : K) : SL(2,K) × W :=
  (curve φ a,f a)

omit [CharP K 2] in
@[simp] lemma fst_normalized (φ : K →+* K) (f : K → W) (a : K) :
    ((generator φ f a)*(generator φ f 0)⁻¹).1 = curve φ a := by
  simp [generator]

/-- The twist and the auxiliary function are arbitrary. -/
theorem contains_at (φ : K →+* K) (f : K → W) (hW : ∀ w : W, w^2 = 1)
    (a : K) (ha : a ≠ 0) (ha1 : a ≠ 1) :
    cycleGraph 8 ⊑ Erdos713C8CommutingDifferences.graph (generator φ f) := by
  let b := a/(a+1)
  have hden : a+1 ≠ 0 := by simpa only [← CharTwo.sub_eq_add,sub_ne_zero] using ha1
  have hb : b ≠ 0 := div_ne_zero ha hden
  apply Erdos713C8InvolutionProduct.contains (generator φ f) a b 0
  · intro h
    apply curve_ne_one φ ha
    simpa only [Prod.fst_one,fst_normalized] using congrArg Prod.fst h
  · intro h
    apply curve_ne_one φ hb
    simpa only [Prod.fst_one,fst_normalized] using congrArg Prod.fst h
  · intro h
    apply curve_pair_ne_one φ ha hb
    simpa [generator] using congrArg Prod.fst h
  · apply Prod.ext
    · change ((curve φ a*(curve φ 0)⁻¹)*(curve φ b*(curve φ 0)⁻¹))^2 = 1
      simpa only [curve_zero,inv_one,mul_one] using
        curve_pair_square φ (Erdos713C8SL2SectionObstruction.partner_relation ha1)
    · exact hW _

/-- This includes all Frobenius twists, in every finite characteristic-two
field with more than two elements. No finiteness of W is required. -/
theorem contains [Fintype K] (φ : K →+* K) (f : K → W)
    (hW : ∀ w : W, w^2 = 1) (hq : 2 < Fintype.card K) :
    cycleGraph 8 ⊑ Erdos713C8CommutingDifferences.graph (generator φ f) := by
  classical
  obtain ⟨a,_,ha⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show ({0,1} : Finset K).card < (Finset.univ : Finset K).card from
      Finset.card_le_two.trans_lt (by simpa using hq))
  simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at ha
  exact contains_at φ f hW a ha.1 ha.2

/-- In particular an arbitrary additive scalar voltage cannot rescue it. -/
theorem contains_scalar [Fintype K] (φ : K →+* K) (f : K → K)
    (hq : 2 < Fintype.card K) :
    cycleGraph 8 ⊑ Erdos713C8CommutingDifferences.graph
      (generator φ (fun a => Multiplicative.ofAdd (f a))) := by
  apply contains _ _ ?_ hq
  intro w
  rw [pow_two]
  exact congrArg Multiplicative.ofAdd (CharTwo.add_self_eq_zero (Multiplicative.toAdd w))

#print axioms curve_pair_square
#print axioms contains
#print axioms contains_scalar
end Erdos713C8TwistedSL2Section
