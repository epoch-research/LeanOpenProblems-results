import FormalConjecturesUtil
import Submission.C8Voltage

/-! A failed four-coordinate construction: a diagonal quadratic potential still admits C8.
Research only; this does not disprove the original conjecture. -/
open SimpleGraph
namespace Erdos713C8QuadraticPotential
set_option maxHeartbeats 1000000

abbrev Vertex (F : Type*) := F × (Fin 3 → F)

def Rel {F : Type*} [Field F] (k : F) (p l : Vertex F) : Prop :=
  p.2 0+l.2 0 = l.1*p.1 ∧
  p.2 1+l.2 1 = l.2 0*p.1 ∧
  p.2 2+l.2 2 = (l.1^2+k*(l.2 0)^2)*p.1

abbrev graph {F : Type*} [Field F] (k : F) := Erdos713C6.bipGraph (Rel k)

def points {F : Type*} [Field F] (k u v h : F) : Fin 4 → Vertex F :=
  let t := (u+v)*h
  let A := u^2+k*(u*v*h)^2
  let B := v^2+k*(u*v*h)^2
  ![(-u*h,![0,0,0]), (-v*h,![0,0,0]),
    (u*h,![u*t,-u*v*h*t,A*t]), (v*h,![v*t,-u*v*h*t,B*t])]

def lines {F : Type*} [Field F] (k u v h : F) : Fin 4 → Vertex F :=
  let t := (u+v)*h
  let A := u^2+k*(u*v*h)^2
  let B := v^2+k*(u*v*h)^2
  ![(0,![0,0,0]), (u,![-u*v*h,u*v^2*h^2,-v*h*A]),
    (u+v,![0,u*v*h*t,(u+v)^2*u*h-A*t]), (v,![-u*v*h,u^2*v*h^2,-u*h*B])]

lemma contains {F : Type*} [Field F] (k u v h : F)
    (hu : u ≠ 0) (hv : v ≠ 0) (hh : h ≠ 0) (hm : u-v ≠ 0) (hp : u+v ≠ 0) :
    cycleGraph 8 ⊑ graph k := by
  have huv : u ≠ v := sub_ne_zero.mp hm
  have hprod : u*h ≠ v*h := fun he => huv (mul_right_cancel₀ hh he)
  have hneg : -u*h ≠ -v*h := by
    intro he
    apply hprod
    linear_combination -he
  have hut : u*((u+v)*h) ≠ 0 := mul_ne_zero hu (mul_ne_zero hp hh)
  have hvt : v*((u+v)*h) ≠ 0 := mul_ne_zero hv (mul_ne_zero hp hh)
  apply Erdos713C8Voltage.contains_of_octagon (Rel k) (points k u v h) (lines k u v h)
  · intro i j hij
    have hx := congrArg (fun p : Vertex F => p.1) hij
    have hy := congrArg (fun p : Vertex F => p.2 0) hij
    fin_cases i <;> fin_cases j <;> first | rfl | (
      dsimp [points] at hx hy
      first | exact (hneg hx).elim | exact (hneg hx.symm).elim |
        exact (hprod hx).elim | exact (hprod hx.symm).elim |
        exact (hut hy).elim | exact (hut hy.symm).elim |
        exact (hvt hy).elim | exact (hvt hy.symm).elim)
  · intro i j hij
    have hx := congrArg (fun p : Vertex F => p.1) hij
    have hsu : u+v ≠ u := by simpa using hv
    have hsv : u+v ≠ v := by simpa using hu
    fin_cases i <;> fin_cases j <;> first | rfl | (
      dsimp [lines] at hx
      first | exact (hu hx).elim | exact (hu hx.symm).elim |
        exact (hv hx).elim | exact (hv hx.symm).elim |
        exact (hp hx).elim | exact (hp hx.symm).elim |
        exact (huv hx).elim | exact (huv hx.symm).elim |
        exact (hsu hx).elim | exact (hsu hx.symm).elim |
        exact (hsv hx).elim | exact (hsv hx.symm).elim)
  · intro i
    fin_cases i <;> dsimp [Rel,points,lines]
    all_goals refine ⟨?_,?_,?_⟩ <;> ring
  · intro i
    fin_cases i <;> dsimp [Rel,points,lines]
    all_goals refine ⟨?_,?_,?_⟩ <;> ring

lemma contains_large_field {F : Type*} [Field F] [Fintype F]
    (hF : 3 < Fintype.card F) (k : F) : cycleGraph 8 ⊑ graph k := by
  classical
  have hS : ({0,1,-1} : Finset F).card ≤ 3 := by
    simpa using List.toFinset_card_le ([0,1,-1] : List F)
  obtain ⟨u,_,hu⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({0,1,-1} : Finset F)) (t := Finset.univ)
    (by simpa only [Finset.card_univ] using hS.trans_lt hF)
  simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hu
  apply contains k u 1 1 hu.1 one_ne_zero one_ne_zero (sub_ne_zero.mpr hu.2.1)
  intro he
  apply hu.2.2
  linear_combination he

#print axioms contains_large_field
end Erdos713C8QuadraticPotential
