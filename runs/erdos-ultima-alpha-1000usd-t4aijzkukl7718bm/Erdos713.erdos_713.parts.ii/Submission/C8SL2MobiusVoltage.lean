import FormalConjecturesUtil
import Submission.SL2DifferenceCommutation
import Submission.C8SidonWord

/-! A specific Möbius multiplicative voltage still leaves an injective C8.
The field calculations are exact; no general extremal exponent is asserted. -/
open SimpleGraph
open scoped MatrixGroups
namespace Erdos713C8SL2MobiusVoltage
open Erdos713C8SL2SectionObstruction Erdos713SL2DifferenceCommutation
variable {K : Type*} [Field K] [CharP K 2]
set_option maxHeartbeats 2000000

lemma curve_word (z : K) :
    curve (z+1)*(curve z)⁻¹*curve (z^2)*(curve (z+1))⁻¹ =
      curve z*(curve (z^2+1))⁻¹*curve (z+1)*(curve z)⁻¹ := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [curve,Matrix.SpecialLinearGroup.SL2_inv_expl,Matrix.mul_apply,Fin.sum_univ_two,
      CharTwo.neg_eq,Matrix.vecMul,dotProduct] <;> ring_nf <;> reduce_mod_char!

abbrev Params (K : Type*) [Zero K] [One K] := {a : K // a ≠ 0 ∧ a ≠ 1}

def voltage (a : Params K) : Kˣ := Units.mk0 (a.val/(a.val+1))
  (div_ne_zero a.property.1 (by
    simpa only [← CharTwo.sub_eq_add,sub_ne_zero] using a.property.2))

def generator (a : Params K) : SL(2,K) × Kˣ := (curve a.val,voltage a)

lemma generator_injective : Function.Injective (generator (K := K)) := by
  intro a b h
  exact Subtype.ext (curve_injective (congrArg Prod.fst h))

lemma generator_sidon (a b c d : Params K) (hab : a ≠ b)
    (h : generator a*(generator b)⁻¹ = generator c*(generator d)⁻¹) : a=c ∧ b=d := by
  have hne : a.val ≠ b.val := fun he => hab (Subtype.ext he)
  have hh := difference_injective_of_ne hne (congrArg Prod.fst h)
  exact ⟨Subtype.ext hh.1,Subtype.ext hh.2⟩

lemma plus_one_twice (a : K) : a+1+1 = a := by
  linear_combination CharTwo.two_eq_zero (R := K)

lemma voltage_inverse_pair (a b : Params K) (hb : b.val = a.val+1) :
    voltage a*voltage b = 1 := by
  apply Units.ext
  change (a.val/(a.val+1))*(b.val/(b.val+1)) = 1
  rw [hb,plus_one_twice]
  have hden : a.val+1 ≠ 0 := by simpa only [hb] using b.property.1
  field_simp [a.property.1,hden]

/-- Four explicit parameters suffice; the only extra exclusion is the
nontrivial F4 polynomial z^2+z+1. -/
theorem contains_at (z : K) (hz : z ≠ 0) (hz1 : z ≠ 1) (hzq : z^2+z+1 ≠ 0) :
    cycleGraph 8 ⊑ Erdos713C8CommutingDifferences.graph (generator (K := K)) := by
  have hzp : z+1 ≠ 0 := by simpa only [← CharTwo.sub_eq_add,sub_ne_zero] using hz1
  have hzp1 : z+1 ≠ 1 := by simpa using hz
  have hz2 : z^2 ≠ 0 := pow_ne_zero _ hz
  have hz21 : z^2 ≠ 1 := by
    intro hh
    have he : (z+1)^2 = 0 := by
      calc
        _ = z^2+1 := by ring_nf; reduce_mod_char!
        _ = 0 := by rw [hh]; exact CharTwo.add_self_eq_zero _
    exact (pow_ne_zero 2 hzp) he
  have hz2p : z^2+1 ≠ 0 := by simpa only [← CharTwo.sub_eq_add,sub_ne_zero] using hz21
  have hz2p1 : z^2+1 ≠ 1 := by simpa using hz2
  have hzz2 : z ≠ z^2 := by
    intro hh
    apply mul_ne_zero hz (sub_ne_zero.mpr hz1)
    linear_combination -hh
  let a : Params K := ⟨z+1,hzp,hzp1⟩
  let b : Params K := ⟨z,hz,hz1⟩
  let c : Params K := ⟨z^2,hz2,hz21⟩
  let d : Params K := ⟨z^2+1,hz2p,hz2p1⟩
  have hab : a ≠ b := by
    intro hh
    have he : z+1 = z := congrArg Subtype.val hh
    exact one_ne_zero (add_left_cancel (he.trans (add_zero z).symm))
  have hac : a ≠ c := by
    intro hh
    have he : z+1 = z^2 := congrArg Subtype.val hh
    apply hzq
    calc
      z^2+z+1 = z^2+(z+1) := by ring
      _ = 0 := by rw [he]; exact CharTwo.add_self_eq_zero _
  have had : a ≠ d := fun hh => hzz2 (add_right_cancel (congrArg Subtype.val hh))
  have hbc : b ≠ c := fun hh => hzz2 (congrArg Subtype.val hh)
  have hbd : b ≠ d := by
    intro hh
    have he : z = z^2+1 := congrArg Subtype.val hh
    apply hzq
    calc
      z^2+z+1 = z+(z^2+1) := by ring
      _ = 0 := by rw [← he]; exact CharTwo.add_self_eq_zero _
  have hvolab : voltage a*voltage b = 1 := by
    have hh := voltage_inverse_pair b a (by rfl)
    simpa only [mul_comm] using hh
  have hvolcd : voltage c*voltage d = 1 := voltage_inverse_pair c d (by rfl)
  have hword : generator a*(generator b)⁻¹*generator c*(generator a)⁻¹ =
      generator b*(generator d)⁻¹*generator a*(generator b)⁻¹ := by
    apply Prod.ext
    · exact curve_word z
    · change voltage a*(voltage b)⁻¹*voltage c*(voltage a)⁻¹ =
        voltage b*(voltage d)⁻¹*voltage a*(voltage b)⁻¹
      have heab : voltage b = (voltage a)⁻¹ := eq_inv_of_mul_eq_one_right hvolab
      have hecd : voltage d = (voltage c)⁻¹ := eq_inv_of_mul_eq_one_right hvolcd
      rw [heab,hecd]
      simp only [inv_inv]
      ac_rfl
  exact Erdos713C8SidonWord.contains generator generator_injective generator_sidon
    a b c d hab hac had hbc hbd hword

lemma exists_good_parameter [Fintype K] (hq : 4 < Fintype.card K) :
    ∃ z : K, z ≠ 0 ∧ z ≠ 1 ∧ z^2+z+1 ≠ 0 := by
  classical
  by_cases hr : ∃ w : K, w^2+w+1 = 0
  · obtain ⟨w,hw⟩ := hr
    have hfour : ({0,1,w,w+1} : Finset K).card ≤ 4 := by
      have h1 := Finset.card_insert_le (0 : K) {1,w,w+1}
      have h2 := Finset.card_insert_le (1 : K) {w,w+1}
      have h3 := Finset.card_le_two (a := w) (b := w+1)
      omega
    obtain ⟨z,_hz,hz⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (show ({0,1,w,w+1} : Finset K).card < (Finset.univ : Finset K).card from
        hfour.trans_lt (by simpa using hq))
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hz
    refine ⟨z,hz.1,hz.2.1,?_⟩
    intro hzq
    have he : (z-w)*(z-(w+1)) = (z^2+z+1)+(w^2+w+1) := by
      ring_nf
      reduce_mod_char!
    rw [hzq,hw,zero_add] at he
    rcases mul_eq_zero.mp he with hh | hh
    · exact hz.2.2.1 (sub_eq_zero.mp hh)
    · exact hz.2.2.2 (sub_eq_zero.mp hh)
  · obtain ⟨z,_hz,hz⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (show ({0,1} : Finset K).card < (Finset.univ : Finset K).card from
        Finset.card_le_two.trans_lt (by simpa using (show 2 < Fintype.card K by omega)))
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hz
    exact ⟨z,hz.1,hz.2,fun hh => hr ⟨z,hh⟩⟩

/-- Every finite characteristic-two field larger than F4 is covered,
including odd extension degrees where the earlier inverse-pair mechanism
need not apply to this Möbius voltage. -/
theorem contains_finite [Fintype K] (hq : 4 < Fintype.card K) :
    cycleGraph 8 ⊑ Erdos713C8CommutingDifferences.graph (generator (K := K)) := by
  obtain ⟨z,hz,hz1,hzq⟩ := exists_good_parameter hq
  exact contains_at z hz hz1 hzq

#print axioms curve_word
#print axioms contains_at
#print axioms contains_finite
end Erdos713C8SL2MobiusVoltage
