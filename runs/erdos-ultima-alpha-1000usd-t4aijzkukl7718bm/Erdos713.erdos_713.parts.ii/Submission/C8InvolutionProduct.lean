import FormalConjecturesUtil
import Submission.C8CommutingDifferences

/-! An involution-product octagon in a bipartite Cayley incidence graph.
This is an auxiliary construction lemma, not a proof of Erdos 713. -/
open SimpleGraph
namespace Erdos713C8InvolutionProduct
open Erdos713C8CommutingDifferences
variable {G I : Type*} [Group G]
set_option maxHeartbeats 1000000

/-- If two nontrivial normalized generators have nontrivial product of
order two, repeating the two generator steps gives an injective octagon. -/
theorem contains (g : I → G) (a b c : I)
    (hX : g a*(g c)⁻¹ ≠ 1) (hY : g b*(g c)⁻¹ ≠ 1)
    (hZ : (g a*(g c)⁻¹)*(g b*(g c)⁻¹) ≠ 1)
    (hZZ : ((g a*(g c)⁻¹)*(g b*(g c)⁻¹))^2 = 1) :
    cycleGraph 8 ⊑ graph g := by
  let X := g a*(g c)⁻¹
  let Y := g b*(g c)⁻¹
  let Z := X*Y
  have hzz : Z*Z = 1 := by simpa only [pow_two] using hZZ
  have hXc : X*g c = g a := by simp [X]
  have hYc : Y*g c = g b := by simp [Y]
  have hZc : Z*g c = X*g b := by rw [show Z = X*Y from rfl,mul_assoc,hYc]
  have hXZ : X ≠ Z := by
    intro he
    apply hY
    apply mul_left_cancel (a := X)
    simpa only [mul_one] using he.symm
  have hZX : Z*X ≠ 1 := by
    intro he
    have he' : X = Z := mul_left_cancel (he.trans hzz.symm)
    exact hXZ he'
  have hXZX : X ≠ Z*X := by
    intro he
    apply hZ
    apply mul_right_cancel (b := X)
    simpa only [one_mul] using he.symm
  have hZZX : Z ≠ Z*X := by
    intro he
    apply hX
    apply mul_left_cancel (a := Z)
    simpa only [mul_one] using he.symm
  let p : Fin 4 → G := ![1,X,Z,Z*X]
  let l : Fin 4 → G := fun i => p (i+1)*g c
  have hp : Function.Injective p := by
    intro i j he
    fin_cases i <;> fin_cases j <;> first | rfl | (
      dsimp [p] at he
      first | exact (hX he).elim | exact (hX he.symm).elim |
        exact (hZ he).elim | exact (hZ he.symm).elim |
        exact (hZX he).elim | exact (hZX he.symm).elim |
        exact (hXZ he).elim | exact (hXZ he.symm).elim |
        exact (hXZX he).elim | exact (hXZX he.symm).elim |
        exact (hZZX he).elim | exact (hZZX he.symm).elim)
  have hl : Function.Injective l := by
    intro i j he
    exact add_right_cancel (hp (mul_right_cancel he))
  apply contains_of_octagon g p l hp hl
  · intro i
    fin_cases i
    · refine ⟨a,?_⟩
      change X*g c = 1*g a
      simpa only [one_mul] using hXc
    · refine ⟨b,?_⟩
      change Z*g c = X*g b
      exact hZc
    · refine ⟨a,?_⟩
      change (Z*X)*g c = Z*g a
      rw [mul_assoc,hXc]
    · refine ⟨b,?_⟩
      change 1*g c = (Z*X)*g b
      calc
        _ = (Z*Z)*g c := by rw [hzz]
        _ = Z*(Z*g c) := mul_assoc _ _ _
        _ = Z*(X*g b) := by rw [hZc]
        _ = _ := (mul_assoc _ _ _).symm
  · intro i
    exact ⟨c,rfl⟩

#print axioms contains
end Erdos713C8InvolutionProduct
