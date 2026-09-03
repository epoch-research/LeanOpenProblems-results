import FormalConjecturesUtil
import Submission.C8CommutingDifferences

/-! A repeated four-generator block producing an injective octagon.
This is an auxiliary obstruction, not a solution of Erdős 713. -/
open SimpleGraph
namespace Erdos713C8InvolutiveBlock
open Erdos713C8CommutingDifferences
variable {G I : Type*} [Group G]
set_option maxHeartbeats 1000000

lemma orbit_injective (P x y : G) (hP : P ≠ 1) (hPP : P*P = 1)
    (hxy : x ≠ y) (hPy : P*x ≠ y) :
    Function.Injective (![x,y,P*x,P*y] : Fin 4 → G) := by
  have hxPx : x ≠ P*x := by
    intro h
    exact hP (mul_right_cancel (show P*x = 1*x by simpa using h.symm))
  have hyPy : y ≠ P*y := by
    intro h
    exact hP (mul_right_cancel (show P*y = 1*y by simpa using h.symm))
  have hxPy : x ≠ P*y := by
    intro h
    apply hPy
    rw [h,← mul_assoc,hPP,one_mul]
  have hPxPy : P*x ≠ P*y := fun h => hxy (mul_left_cancel h)
  intro i j h
  fin_cases i <;> fin_cases j <;> first | rfl | (
    dsimp at h
    first | exact (hxy h).elim | exact (hxy h.symm).elim |
      exact (hPy h).elim | exact (hPy h.symm).elim |
      exact (hxPx h).elim | exact (hxPx h.symm).elim |
      exact (hyPy h).elim | exact (hyPy h.symm).elim |
      exact (hxPy h).elim | exact (hxPy h.symm).elim |
      exact (hPxPy h).elim | exact (hPxPy h.symm).elim)

/-- The alternating block `(a,b,c,d)` repeated twice is a simple cycle
when its product is a nontrivial involution and the indicated degeneracies
are excluded. No commutativity is assumed. -/
theorem contains (g : I → G) (a b c d : I)
    (hX : (g a*(g b)⁻¹)^2 ≠ 1)
    (hP : (g a*(g b)⁻¹)*(g c*(g d)⁻¹) ≠ 1)
    (hPP : ((g a*(g b)⁻¹)*(g c*(g d)⁻¹))^2 = 1)
    (hcb : g c ≠ g b) (hda : g d ≠ g a) :
    cycleGraph 8 ⊑ graph g := by
  let X := g a*(g b)⁻¹
  let P := X*(g c*(g d)⁻¹)
  have hpp : P*P = 1 := by simpa only [pow_two] using hPP
  have hx : X ≠ 1 := by intro h; apply hX; change X^2 = 1; simp [h]
  have hpx : P ≠ X := by
    intro h
    apply hX
    calc X^2 = P^2 := congrArg (fun z : G => z^2) h.symm
         _ = 1 := hPP
  have hXb : X*g b = g a := by simp [X]
  have hPd : P*g d = X*g c := by simp [P,mul_assoc]
  have hPXc : (P*X)*g c = g d := by
    rw [mul_assoc,← hPd,← mul_assoc,hpp,one_mul]
  have haXc : g a ≠ X*g c := by
    intro h
    exact hcb (mul_left_cancel (h.symm.trans hXb.symm))
  have hPaXc : P*g a ≠ X*g c := by
    intro h
    exact hda (mul_left_cancel (h.trans hPd.symm)).symm
  let p : Fin 4 → G := ![1,X,P,P*X]
  let l : Fin 4 → G := ![g a,X*g c,P*g a,g d]
  have hp : Function.Injective p := by
    simpa only [mul_one] using orbit_injective P 1 X hP hpp hx.symm
      (by simpa only [mul_one] using hpx)
  have hl : Function.Injective l := by
    have hh := orbit_injective P (g a) (X*g c) hP hpp haXc hPaXc
    simpa only [← mul_assoc,hPXc] using hh
  apply contains_of_octagon g p l hp hl
  · intro i
    fin_cases i
    · exact ⟨a,(one_mul _).symm⟩
    · exact ⟨c,rfl⟩
    · exact ⟨a,rfl⟩
    · exact ⟨c,hPXc.symm⟩
  · intro i
    fin_cases i
    · exact ⟨b,hXb.symm⟩
    · exact ⟨d,hPd.symm⟩
    · refine ⟨b,?_⟩
      change P*g a = (P*X)*g b
      rw [mul_assoc P X (g b),hXb]
    · exact ⟨d,(one_mul _).symm⟩

end Erdos713C8InvolutiveBlock
