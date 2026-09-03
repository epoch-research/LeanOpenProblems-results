import FormalConjecturesUtil
import Submission.DeterminantQuadraticLinks

/-! An explicit theta in the determinant-one quadratic family. The column
link conditions from the preceding file do not imply theta exclusion. -/
open Finset
open scoped Classical
namespace Erdos713DeterminantQuadraticTheta
open Erdos713DeterminantQuadraticGeometry Erdos713DeterminantQuadraticIncidence
open Erdos713ThetaGram (HasTheta)
variable {K : Type*} [Field K]
set_option maxHeartbeats 2000000

/-- The three rows interpolate at the four parameters 0,1,2,3. -/
theorem contains_theta (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) (h11 : (11 : K) ≠ 0) :
    HasTheta (incidence (K := K)) := by
  let a : Rows K := ((1,0,0),(0,0))
  let b : Rows K := ((Units.mk0 2 h2,1,-1),(0,0))
  let c : Rows K := ((1,6/11,6),(-12,-96/11))
  have h6 : (6 : K) ≠ 0 := by
    simpa only [show (6 : K) = 2*3 by norm_num] using mul_ne_zero h2 h3
  have h12 : (1 : K) ≠ 2 := by
    intro h
    apply one_ne_zero (α := K)
    linear_combination -h
  have h13 : (1 : K) ≠ 3 := by
    intro h
    apply h2
    linear_combination -h
  have h23 : (2 : K) ≠ 3 := by
    intro h
    apply one_ne_zero (α := K)
    linear_combination -h
  have hab : a ≠ b := by
    intro h
    exact h12 (congrArg (fun p : Rows K => (p.1.1 : K)) h)
  have hac : a ≠ c := by
    intro h
    exact h6 (congrArg (fun p : Rows K => p.1.2.2) h).symm
  have hbc : b ≠ c := by
    intro h
    exact h12 (congrArg (fun p : Rows K => (p.1.1 : K)) h).symm
  let f : Fin 3 → Rows K := ![a,b,c]
  let g : Fin 4 → Cols K := ![(0,(0,0)),(1,(1,1)),(2,(4,2)),(3,(15,9))]
  have hf : Function.Injective f := by
    intro i j he
    fin_cases i <;> fin_cases j <;> simp_all [f]
  have ht : Function.Injective (fun i : Fin 4 => (![0,1,2,3] : Fin 4 → K) i) := by
    intro i j he
    fin_cases i <;> fin_cases j <;>
      simp_all [Ne.symm h2,Ne.symm h3,Ne.symm h12,Ne.symm h13,Ne.symm h23]
  have hfirst (i : Fin 4) : (g i).1 = (![0,1,2,3] : Fin 4 → K) i := by
    fin_cases i <;> rfl
  have hg : Function.Injective g := by
    intro i j he
    apply ht
    simpa only [hfirst] using congrArg Prod.fst he
  refine ⟨f,g,hf,hg,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;>
    norm_num [f,g,incidence,eval,coeff,a,b,c,Matrix.cons_val_two,Matrix.cons_val_three] <;>
    (try field_simp [h2,h11]) <;> ring

#print axioms contains_theta
end Erdos713DeterminantQuadraticTheta
