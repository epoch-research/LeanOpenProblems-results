import FormalConjecturesUtil
import Submission.SL2DifferenceCommutation

/-! A characteristic-two inverse-pair octagon survives multiplicative voltage
homomorphisms, with no exponent-two assumption on the voltage group.
This excludes a candidate construction, not an extremal exponent. -/
open SimpleGraph
open scoped MatrixGroups
namespace Erdos713C8SL2MultiplicativeVoltage
open Erdos713C8SL2SectionObstruction Erdos713SL2DifferenceCommutation
variable {K : Type*} [Field K]
set_option maxHeartbeats 1000000

def upper (c : K) : SL(2,K) :=
  ⟨!![1,c; 0,1],by simp only [Matrix.det_fin_two_of]; ring⟩

lemma normalized_translate (a c : K) :
    curve a*(curve c)⁻¹ = upper c*curve (a-c)*(upper c)⁻¹ := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  have hd := difference_matrix a c
  change (↑(curve a*(curve c)⁻¹) : Matrix (Fin 2) (Fin 2) K) i j = _
  rw [hd]
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  fin_cases i <;> fin_cases j <;>
    simp [upper,curve,Matrix.mul_apply,Fin.sum_univ_two] <;> ring

lemma normalized_pair (a b c : K) :
    (curve a*(curve c)⁻¹)*(curve b*(curve c)⁻¹) =
      upper c*(curve (a-c)*curve (b-c))*(upper c)⁻¹ := by
  rw [normalized_translate,normalized_translate]
  group

lemma normalized_ne_one {a c : K} (h : a ≠ c) : curve a*(curve c)⁻¹ ≠ 1 := by
  rw [ne_eq,normalized_translate,conj_eq_one_iff]
  exact curve_ne_one (sub_ne_zero.mpr h)

lemma normalized_pair_ne_one {a b c : K} (ha : a ≠ c) (hb : b ≠ c) :
    (curve a*(curve c)⁻¹)*(curve b*(curve c)⁻¹) ≠ 1 := by
  rw [ne_eq,normalized_pair,conj_eq_one_iff]
  exact curve_pair_ne_one (sub_ne_zero.mpr ha) (sub_ne_zero.mpr hb)

variable [CharP K 2]

lemma normalized_inverse_pair_square {a : K} (ha : a ≠ 0) :
    ((curve a*(curve 1)⁻¹)*(curve a⁻¹*(curve 1)⁻¹))^2 = 1 := by
  have hrel : (a-1)*(a⁻¹-1)+(a-1)+(a⁻¹-1) = 0 := by
    have hh := mul_inv_cancel₀ ha
    linear_combination hh
  rw [normalized_pair]
  calc
    (upper 1*(curve (a-1)*curve (a⁻¹-1))*(upper 1)⁻¹)^2 =
      upper 1*((curve (a-1)*curve (a⁻¹-1))^2)*(upper 1)⁻¹ := by
        simp only [pow_two]
        group
    _ = 1 := by rw [curve_pair_square hrel]; simp

variable {W : Type*} [Group W]

def unitGenerator (f : Kˣ → W) (a : Kˣ) : SL(2,K) × W := (curve (a : K),f a)

/-- Only the parameters a, a^(-1), and 1 are needed. The voltage function
may be arbitrary provided its normalized inverse pair has product one. -/
theorem contains_inverse_pair (f : Kˣ → W) (a : Kˣ) (ha : a ≠ 1)
    (hvol : (f a*(f 1)⁻¹)*(f a⁻¹*(f 1)⁻¹) = 1) :
    cycleGraph 8 ⊑ Erdos713C8CommutingDifferences.graph (unitGenerator f) := by
  have haK : (a : K) ≠ 1 := fun hh => ha (Units.ext hh)
  have hai : (a : K)⁻¹ ≠ 1 := by
    intro hh
    apply haK
    calc
      (a : K) = ((a : K)⁻¹)⁻¹ := (inv_inv _).symm
      _ = 1 := by rw [hh,inv_one]
  apply Erdos713C8InvolutionProduct.contains (unitGenerator f) a a⁻¹ 1
  · intro hh
    apply normalized_ne_one haK
    simpa [unitGenerator] using congrArg Prod.fst hh
  · intro hh
    apply normalized_ne_one hai
    simpa [unitGenerator] using congrArg Prod.fst hh
  · intro hh
    apply normalized_pair_ne_one haK hai
    simpa [unitGenerator] using congrArg Prod.fst hh
  · apply Prod.ext
    · simpa [unitGenerator] using normalized_inverse_pair_square a.ne_zero
    · change ((f a*(f 1)⁻¹)*(f a⁻¹*(f 1)⁻¹))^2 = 1
      rw [hvol,one_pow]

/-- Every full multiplicative-homomorphism voltage section contains C8.
The target group need not have exponent two, be abelian, or be finite. -/
theorem contains_multiplicative_section [Fintype K] (f : Kˣ →* W)
    (hq : 2 < Fintype.card K) :
    cycleGraph 8 ⊑ Erdos713C8CommutingDifferences.graph (unitGenerator f) := by
  classical
  obtain ⟨a,_ha,ha⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show ({0,1} : Finset K).card < (Finset.univ : Finset K).card from
      Finset.card_le_two.trans_lt (by simpa using hq))
  simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at ha
  let u : Kˣ := Units.mk0 a ha.1
  have hu : u ≠ 1 := by
    intro hh
    exact ha.2 (congrArg Units.val hh)
  apply contains_inverse_pair (fun x => f x) u hu
  simp

/-- In particular the natural unit-coordinate lift does not give C8-free
hosts on the q^4 scale. -/
theorem contains_unit_coordinate [Fintype K] (hq : 2 < Fintype.card K) :
    cycleGraph 8 ⊑ Erdos713C8CommutingDifferences.graph
      (unitGenerator (fun a : Kˣ => a)) :=
  contains_multiplicative_section (MonoidHom.id (Kˣ)) hq

#print axioms normalized_translate
#print axioms normalized_inverse_pair_square
#print axioms contains_inverse_pair
#print axioms contains_multiplicative_section
#print axioms contains_unit_coordinate
end Erdos713C8SL2MultiplicativeVoltage
