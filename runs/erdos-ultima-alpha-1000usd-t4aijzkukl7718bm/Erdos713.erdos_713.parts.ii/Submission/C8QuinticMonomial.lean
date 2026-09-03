import FormalConjecturesUtil
import Submission.C8FiniteCubic

/-! A construction obstruction for the potential a²b³ in characteristic two.
This auxiliary result does not settle the extremal exponent of C8 or Erdős 713. -/

open SimpleGraph
namespace Erdos713C8QuinticMonomial
open Erdos713C8FiniteQuadratic Erdos713C8FiniteCubic
variable {K : Type*} [Field K]
set_option maxHeartbeats 2000000

lemma cubic_shear_moment [CharP K 2] (u τ : K) :
    moment u (1+u) 1 1 (fun a b => (b+τ*a)^3) =
      u*(u+1)*τ*(τ+1)*(τ+u) := by
  dsimp [moment]
  linear_combination
    (-2*τ^3*u^2-2*τ^3*u-2*τ^2*u^3-τ^2*u^2-2*τ^2*u+
      τ*u^3+τ*u^2-u^3)*(CharTwo.two_eq_zero (R := K))

lemma quintic_translate_moment [CharP K 2] (u τ s : K) :
    moment u (1+u) 1 1 (fun a b => (a+s)^2*(b+τ*a)^3) =
      moment u (1+u) 1 1 (fun a b => a^2*(b+τ*a)^3) +
        s^2*moment u (1+u) 1 1 (fun a b => (b+τ*a)^3) := by
  dsimp [moment]
  simp only [CharTwo.add_sq]
  ring

/-- Four distinct slopes and a translated/sheared moment give an injective
    octagon for a²b³ over any finite field of characteristic two of size > 4. -/
theorem quintic_octagon_char_two [Fintype K] [CharP K 2]
    (hq : 4 < Fintype.card K) : Octagon (fun a b : K => a^2*b^3) := by
  classical
  have hcard2 : ({0,1} : Finset K).card ≤ 2 := by
    simp
  obtain ⟨u,_,hu⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({0,1} : Finset K)) (t := Finset.univ) (by
      simpa only [Finset.card_univ] using
        hcard2.trans_lt (show 2 < Fintype.card K by omega))
  simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hu
  have hcard3 : ({0,1,u} : Finset K).card ≤ 3 := by
    simpa using List.toFinset_card_le ([0,1,u] : List K)
  obtain ⟨τ,_,hτ⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({0,1,u} : Finset K)) (t := Finset.univ) (by
      simpa only [Finset.card_univ] using
        hcard3.trans_lt (show 3 < Fintype.card K by omega))
  simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hτ
  have hu1 : u+1 ≠ 0 := by
    rw [← CharTwo.sub_eq_add]
    exact sub_ne_zero.mpr hu.2
  have hτ1 : τ+1 ≠ 0 := by
    rw [← CharTwo.sub_eq_add]
    exact sub_ne_zero.mpr hτ.2.1
  have hτu : τ+u ≠ 0 := by
    rw [← CharTwo.sub_eq_add]
    exact sub_ne_zero.mpr hτ.2.2
  let N := moment u (1+u) 1 1 (fun a b => (b+τ*a)^3)
  let M := moment u (1+u) 1 1 (fun a b => a^2*(b+τ*a)^3)
  have hN : N ≠ 0 := by
    dsimp [N]
    rw [cubic_shear_moment]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hu.1 hu1) hτ.1) hτ1) hτu
  have hSq : Function.Surjective (fun z : K => z^2) :=
    Finite.surjective_of_injective (frobenius_inj K 2)
  obtain ⟨s,hs⟩ := hSq (-M/N)
  change s^2 = -M/N at hs
  have hM : moment u (1+u) 1 1 (fun a b => (a+s)^2*(b+τ*a)^3) = 0 := by
    rw [quintic_translate_moment]
    change M+s^2*N=0
    rw [hs,div_mul_cancel₀ _ hN]
    ring
  have hv : 1+u ≠ 0 := by simpa only [add_comm] using hu1
  have hv1 : 1+u ≠ 1 := by
    intro h
    apply hu.1
    linear_combination h
  have huv : u ≠ 1+u := by
    intro h
    have : (0 : K) = 1 := by linear_combination h
    exact zero_ne_one this
  have hB : (1 : K)^2*(1+u)*(1-(1+u))-1^2*u*(1-u) = 0 := by
    linear_combination -u*(CharTwo.two_eq_zero (R := K))
  have ho := octagon_of_moment (fun a b => (a+s)^2*(b+τ*a)^3)
    u (1+u) 1 1 hu.1 hv hu.2 hv1 huv one_ne_zero one_ne_zero hB hM
  have hshift : Octagon (fun a b => (a+s)^2*b^3) :=
    shift_octagon τ (fun _ _ => rfl) ho
  exact offset_octagon (fun a b : K => a^2*b^3) s 0
    (by simpa only [add_zero] using hshift)

theorem contains_quintic_char_two [Fintype K] [CharP K 2]
    (hq : 4 < Fintype.card K) :
    cycleGraph 8 ⊑ graph (fun a b : K => a^2*b^3) :=
  contains_of_octagon (quintic_octagon_char_two hq)

#print axioms cubic_shear_moment
#print axioms quintic_translate_moment
#print axioms quintic_octagon_char_two
#print axioms contains_quintic_char_two
end Erdos713C8QuinticMonomial
