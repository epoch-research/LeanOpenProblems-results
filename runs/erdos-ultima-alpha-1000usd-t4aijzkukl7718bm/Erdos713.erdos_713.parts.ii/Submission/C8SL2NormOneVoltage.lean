import FormalConjecturesUtil
import Submission.SL2MobiusVoltageBounds

/-! A full quadratic-extension norm-one voltage does not remove C8 from
the SL2 curve section. This is an auxiliary construction obstruction. -/
open SimpleGraph Polynomial Finset
open scoped MatrixGroups
namespace Erdos713C8SL2NormOneVoltage
open Erdos713C8SL2SectionObstruction
variable {K L : Type*} [Field K] [CharP K 2] [Fintype K]
    [Field L] [Algebra K L]
set_option maxHeartbeats 2000000

omit [CharP K 2] in
lemma numerator_ne (t : K) (w : L) (ht : t ≠ 0)
    (hw : FiniteField.frobeniusAlgHom K L w = w+algebraMap K L t) (a : K) :
    algebraMap K L a+w ≠ 0 := by
  intro h
  have hh := congrArg (FiniteField.frobeniusAlgHom K L) h
  simp only [map_add,AlgHom.commutes,hw,map_zero] at hh
  have htL : algebraMap K L t = 0 := by linear_combination hh-h
  exact ht ((algebraMap K L).injective (htL.trans (map_zero _).symm))

omit [CharP K 2] in
lemma denominator_ne (t : K) (w : L) (ht : t ≠ 0)
    (hw : FiniteField.frobeniusAlgHom K L w = w+algebraMap K L t) (a : K) :
    algebraMap K L a+w+algebraMap K L t ≠ 0 := by
  simpa only [map_add,add_right_comm] using numerator_ne t w ht hw (a+t)

lemma ratio_pow (t : K) (w : L) (ht : t ≠ 0)
    (hw : FiniteField.frobeniusAlgHom K L w = w+algebraMap K L t) (a : K) :
    ((algebraMap K L a+w)/(algebraMap K L a+w+algebraMap K L t))^
      (Fintype.card K+1) = 1 := by
  let σ := FiniteField.frobeniusAlgHom K L
  have hn : σ (algebraMap K L a+w) = algebraMap K L a+w+algebraMap K L t := by
    simp only [σ,map_add,AlgHom.commutes,hw,add_assoc]
  have hd : σ (algebraMap K L a+w+algebraMap K L t) = algebraMap K L a+w := by
    simp only [map_add,σ,AlgHom.commutes,hw]
    rw [add_assoc,add_assoc,← map_add,CharTwo.add_self_eq_zero,map_zero,add_zero]
  have hs := map_div₀ σ (algebraMap K L a+w) (algebraMap K L a+w+algebraMap K L t)
  rw [hn,hd] at hs
  change ((algebraMap K L a+w)/(algebraMap K L a+w+algebraMap K L t))^
    Fintype.card K = _ at hs
  rw [pow_succ,hs]
  field_simp [numerator_ne t w ht hw a,denominator_ne t w ht hw a]

noncomputable def voltage (t : K) (w : L) (ht : t ≠ 0)
    (hw : FiniteField.frobeniusAlgHom K L w = w+algebraMap K L t) (a : K) :
    rootsOfUnity (Fintype.card K+1) L :=
  rootsOfUnity.mkOfPowEq _ (ratio_pow t w ht hw a)

/-- The norm-one group is represented as the (q+1)-st roots of unity.
Only its polynomial root-count upper bound is needed. -/
theorem contains (t : K) (w : L) (ht : t ≠ 0)
    (hw : FiniteField.frobeniusAlgHom K L w = w+algebraMap K L t)
    (hq : 27 < Fintype.card K) :
    cycleGraph 8 ⊑ Erdos713C8CommutingDifferences.graph (generator (voltage t w ht hw)) := by
  apply Erdos713SL2MobiusVoltageBounds.contains (voltage t w ht hw)
    (rootsOfUnity (Fintype.card K+1) L).subtype w (algebraMap K L t)
    (fun _ => rfl) (numerator_ne t w ht hw) (denominator_ne t w ht hw)
    ((_root_.map_ne_zero (algebraMap K L)).mpr ht) (card_rootsOfUnity L (Fintype.card K+1)) hq

omit [CharP K 2] in
lemma frobenius_fixed_mem_range (w : L)
    (hw : FiniteField.frobeniusAlgHom K L w = w) :
    w ∈ Set.range (algebraMap K L) := by
  classical
  let A := Finset.univ.image (algebraMap K L)
  have hA : A.card = Fintype.card K := by
    simpa only [card_univ] using
      (Finset.card_image_of_injective Finset.univ (algebraMap K L).injective)
  by_contra h
  have hwA : w ∉ A := by simpa [A] using h
  let P : L[X] := X^Fintype.card K-X
  have hp : P ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero L Fintype.one_lt_card
  have hd : P.natDegree ≤ Fintype.card K := by
    dsimp [P]
    compute_degree!
    exact Fintype.card_pos
  have hb : (insert w A).card ≤ P.natDegree := by
    apply Polynomial.card_le_degree_of_subset_roots
    intro x hx
    apply (Polynomial.mem_roots hp).mpr
    rcases mem_insert.mp hx with rfl | hx
    · change x^Fintype.card K = x at hw
      simpa only [Polynomial.IsRoot,P,eval_sub,eval_pow,eval_X] using sub_eq_zero.mpr hw
    · obtain ⟨a,_,rfl⟩ := mem_image.mp hx
      simp [P,← map_pow,FiniteField.pow_card]
  rw [card_insert_of_notMem hwA,hA] at hb
  omega

lemma quadratic_frobenius (t n : K) (w : L)
    (hroot : w^2+algebraMap K L t*w+algebraMap K L n = 0)
    (hno : ∀ a : K, a^2+t*a+n ≠ 0) :
    FiniteField.frobeniusAlgHom K L w = w+algebraMap K L t := by
  haveI : CharP L 2 := charP_of_injective_algebraMap' K 2
  let σ := FiniteField.frobeniusAlgHom K L
  have hs := congrArg σ hroot
  simp only [map_add,map_mul,map_pow,map_zero,AlgHom.commutes] at hs
  have hprod : (σ w-w)*(σ w-(w+algebraMap K L t)) = 0 := by
    calc
      _ = (σ w^2+algebraMap K L t*σ w+algebraMap K L n)+
          (w^2+algebraMap K L t*w+algebraMap K L n) := by
        ring_nf
        reduce_mod_char!
      _ = 0 := by rw [hs,hroot,zero_add]
  rcases mul_eq_zero.mp hprod with he | he
  · obtain ⟨a,ha⟩ := frobenius_fixed_mem_range w (sub_eq_zero.mp he)
    have hz : algebraMap K L (a^2+t*a+n) = 0 := by
      simpa only [map_add,map_mul,map_pow,ha] using hroot
    exact (hno a ((algebraMap K L).injective (hz.trans (map_zero _).symm))).elim
  · exact sub_eq_zero.mp he

/-- Every irreducible quadratic-extension instance of the proposed
norm-one voltage is excluded, irrespective of the twist's trace. -/
theorem contains_quadratic (t n : K) (w : L) (ht : t ≠ 0)
    (hroot : w^2+algebraMap K L t*w+algebraMap K L n = 0)
    (hno : ∀ a : K, a^2+t*a+n ≠ 0) (hq : 27 < Fintype.card K) :
    cycleGraph 8 ⊑ Erdos713C8CommutingDifferences.graph
      (generator (voltage t w ht (quadratic_frobenius t n w hroot hno))) :=
  contains t w ht (quadratic_frobenius t n w hroot hno) hq

#print axioms ratio_pow
#print axioms contains
#print axioms quadratic_frobenius
#print axioms contains_quadratic
end Erdos713C8SL2NormOneVoltage
