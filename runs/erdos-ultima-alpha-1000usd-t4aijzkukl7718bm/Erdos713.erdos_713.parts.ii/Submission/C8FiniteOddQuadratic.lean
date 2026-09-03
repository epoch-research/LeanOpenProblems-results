import FormalConjecturesUtil
import Submission.C8FiniteQuadratic

/-! Arbitrary intercept potentials and the remaining odd-characteristic
quadratic diagnostic. These results give no new extremal lower bound. -/
open SimpleGraph Finset
namespace Erdos713C8FiniteQuadratic
variable {K : Type*} [Field K]
set_option maxHeartbeats 2000000

/-- Four distinct line slopes, without division by a characteristic-dependent
integer. The corresponding points are distinguished by two coordinates. -/
lemma intercept_octagon (A : K) (P : K → K) (u : K)
    (hu : u ≠ 0) (hu1 : u ≠ 1) (huv : u ≠ 1-u) :
    Octagon (fun a b => A*a^2+P b) := by
  let v := 1-u
  let B := u*(u-1)
  let Q : K → K → K := fun a b => A*a^2+P b
  let p : Fin 4 → Vertex K :=
    ![(-u,![0,0,0]), (u-1,![0,0,(2*u-1)*P 0]),
      (u,![u,B,(2*u-1)*P 0+A*u^2+P B]), (v,![v,B,A*v^2+P B])]
  let l : Fin 4 → Vertex K :=
    ![(0,![0,0,-u*P 0]),
      (u,![B,B*(u-1),(A*u^2+P B)*(u-1)-(2*u-1)*P 0]),
      (1,![0,-B,-A*B+v*P 0-P B]),
      (v,![B,-u*B,-u*(A*v^2+P B)])]
  have hv : v ≠ 0 := sub_ne_zero.mpr hu1.symm
  have hv1 : v ≠ 1 := by intro he; apply hu; dsimp [v] at he; linear_combination -he
  have htwo : 2*u-1 ≠ 0 := by
    intro he
    apply huv
    linear_combination he
  refine ⟨p,l,?_,?_,?_,?_⟩
  · intro i j hij
    have hx := congrArg (fun w : Vertex K => w.1) hij
    have hy := congrArg (fun w : Vertex K => w.2 0) hij
    fin_cases i <;> fin_cases j <;> first | rfl | (
      dsimp [p] at hx hy
      first | exact (hu hy).elim | exact (hu hy.symm).elim |
        exact (hv hy).elim | exact (hv hy.symm).elim |
        (exfalso; apply htwo; linear_combination hx) |
        (exfalso; apply htwo; linear_combination -hx))
  · intro i j hij
    have ha := congrArg (fun w : Vertex K => w.1) hij
    fin_cases i <;> fin_cases j <;> first | rfl | (
      dsimp [l] at ha
      first | exact (hu ha).elim | exact (hu ha.symm).elim |
        exact (hu1 ha).elim | exact (hu1 ha.symm).elim |
        exact (hv ha).elim | exact (hv ha.symm).elim |
        exact (hv1 ha).elim | exact (hv1 ha.symm).elim |
        exact (huv ha).elim | exact (huv ha.symm).elim |
        exact (zero_ne_one ha).elim | exact (zero_ne_one ha.symm).elim)
  · intro i
    fin_cases i <;> dsimp [Inc,p,l,Q,v,B]
    all_goals refine ⟨?_,?_,?_⟩ <;> ring
  · intro i
    fin_cases i <;> dsimp [Inc,p,l,Q,v,B]
    all_goals refine ⟨?_,?_,?_⟩ <;> ring

lemma exists_four_slopes [Fintype K] (hq : 3 < Fintype.card K) :
    ∃ u : K, u ≠ 0 ∧ u ≠ 1 ∧ u ≠ 1-u := by
  classical
  by_cases htwo : (2 : K) = 0
  · have hc : ({0,1} : Finset K).card ≤ 2 := by
      simpa using List.toFinset_card_le ([0,1] : List K)
    obtain ⟨u,_,hu⟩ := exists_mem_notMem_of_card_lt_card
      (s := ({0,1} : Finset K)) (t := univ) (by simpa using hc.trans_lt (show 2 < Fintype.card K by omega))
    simp only [mem_insert,mem_singleton,not_or] at hu
    refine ⟨u,hu.1,hu.2,?_⟩
    intro he
    have hh : (2 : K)*u = 1 := by linear_combination he
    rw [htwo,zero_mul] at hh
    exact zero_ne_one hh
  · have hc : ({0,1,1/2} : Finset K).card ≤ 3 := by
      simpa using List.toFinset_card_le ([0,1,1/2] : List K)
    obtain ⟨u,_,hu⟩ := exists_mem_notMem_of_card_lt_card
      (s := ({0,1,1/2} : Finset K)) (t := univ) (by simpa using hc.trans_lt hq)
    simp only [mem_insert,mem_singleton,not_or] at hu
    refine ⟨u,hu.1,hu.2.1,?_⟩
    intro he
    apply hu.2.2
    apply (eq_div_iff htwo).mpr
    linear_combination he

/-- No degree bound, regularity, or polynomial assumption on P is needed. -/
lemma contains_intercept [Fintype K] (A : K) (P : K → K) (hq : 3 < Fintype.card K) :
    cycleGraph 8 ⊑ graph (fun a b => A*a^2+P b) := by
  obtain ⟨u,hu,hu1,huv⟩ := exists_four_slopes hq
  exact contains_of_octagon (intercept_octagon A P u hu hu1 huv)

lemma homogeneous_quadratic_odd [Fintype K] (htwo : (2 : K) ≠ 0)
    (A B C : K) (hq : 3 < Fintype.card K) :
    Octagon (fun a b => A*a^2+B*a*b+C*b^2) := by
  obtain ⟨u,hu,hu1,huv⟩ := exists_four_slopes hq
  by_cases hC : C = 0
  · subst C
    by_cases hB : B = 0
    · subst B
      simpa using intercept_octagon A (fun _ => (0 : K)) u hu hu1 huv
    · apply scaled_sheared_octagon A B 0 u (1-u) 1 (-1) 1 (-A/B-1/2)
        hu (sub_ne_zero.mpr hu1.symm) hu1
        (by intro he; apply hu; linear_combination -he) huv one_ne_zero (neg_ne_zero.mpr one_ne_zero) one_ne_zero
      · ring
      · dsimp [D,E,J]
        field_simp
        <;> ring
  · apply shift_octagon (-B/(2*C))
      (Q := fun a b => (A-B^2/(4*C))*a^2+C*b^2)
    · intro a b
      have hfour : (4 : K) ≠ 0 := by
        have hh := mul_ne_zero htwo htwo
        norm_num only [show (2 : K)*2 = 4 by ring] at hh
        exact hh
      field_simp
      <;> ring
    · simpa using intercept_octagon (A-B^2/(4*C)) (fun b => C*b^2) u hu hu1 huv

lemma quadratic_odd [Fintype K] (htwo : (2 : K) ≠ 0)
    (A B C D E F : K) (hq : 3 < Fintype.card K) :
    cycleGraph 8 ⊑ graph (fun a b => A*a^2+B*a*b+C*b^2+D*a+E*b+F) :=
  contains_of_octagon (linear_octagon D E F (homogeneous_quadratic_odd htwo A B C hq))

/-- Combining the checked characteristic-two and odd-characteristic cases.
This refutes the quadratic construction, not the original conjecture. -/
theorem quadratic_finite [Fintype K] (A B C D E F : K) (hq : 4 < Fintype.card K) :
    cycleGraph 8 ⊑ graph (fun a b => A*a^2+B*a*b+C*b^2+D*a+E*b+F) := by
  by_cases htwo : (2 : K) = 0
  · haveI : CharP K 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).mpr htwo
    exact quadratic_char_two A B C D E F hq
  · exact quadratic_odd htwo A B C D E F (by omega)

#print axioms intercept_octagon
#print axioms contains_intercept
#print axioms quadratic_odd
#print axioms quadratic_finite
end Erdos713C8FiniteQuadratic
