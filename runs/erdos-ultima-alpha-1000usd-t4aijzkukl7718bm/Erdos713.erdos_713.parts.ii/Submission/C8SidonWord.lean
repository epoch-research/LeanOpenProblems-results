import FormalConjecturesUtil
import Submission.C8CommutingDifferences

/-! A two-path word relation in a Sidon generator family gives an injective
C8. This helper checks the vertex distinctness, not only walk closure. -/
open SimpleGraph
namespace Erdos713C8SidonWord
open Erdos713C8CommutingDifferences
variable {G I : Type*} [Group G]
set_option maxHeartbeats 1000000

theorem contains (g : I → G) (hg : Function.Injective g)
    (hS : ∀ a b c d, a ≠ b → g a*(g b)⁻¹ = g c*(g d)⁻¹ → a=c ∧ b=d)
    (a b c d : I) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d)
    (hword : g a*(g b)⁻¹*g c*(g a)⁻¹ = g b*(g d)⁻¹*g a*(g b)⁻¹) :
    cycleGraph 8 ⊑ graph g := by
  let X := g a*(g b)⁻¹
  let Y := g b*(g d)⁻¹
  let Z := X*g c*(g a)⁻¹
  have hZY : Z = Y*g a*(g b)⁻¹ := hword
  have hX : X ≠ 1 := fun h => hab (hg (eq_of_mul_inv_eq_one h))
  have hY : Y ≠ 1 := fun h => hbd (hg (eq_of_mul_inv_eq_one h))
  have hZ : Z ≠ 1 := by
    intro h
    have hh : g a*((g b)⁻¹*g c)*(g a)⁻¹ = 1 := by
      simpa only [Z,X,mul_assoc] using h
    exact hbc (hg (eq_of_inv_mul_eq_one (conj_eq_one_iff.mp hh)))
  have hXY : X ≠ Y := fun h => hab (hS a b b d hab h).1
  have hZX : Z ≠ X := by
    intro h
    have hh : g c*(g a)⁻¹ = 1 := by
      apply mul_left_cancel (a := X)
      simpa only [Z,mul_assoc,mul_one] using h
    exact hac (hg (eq_of_mul_inv_eq_one hh)).symm
  have hZYne : Z ≠ Y := by
    intro h
    have hh : g a*(g b)⁻¹ = 1 := by
      apply mul_left_cancel (a := Y)
      simpa only [hZY,mul_assoc,mul_one] using h
    exact hab (hg (eq_of_mul_inv_eq_one hh))
  have hXc : X*g c = Z*g a := by simp [Z,mul_assoc]
  have hYa : Y*g a = Z*g b := by rw [hZY]; simp [mul_assoc]
  have hL01 : g a ≠ X*g c := by
    intro h
    have hh : (g b)⁻¹*g c = 1 := by
      apply mul_left_cancel (a := g a)
      simpa only [X,mul_assoc,mul_one] using h.symm
    exact hbc (hg (eq_of_inv_mul_eq_one hh))
  have hL02 : g a ≠ Y*g a := by
    intro h
    apply hY
    apply mul_right_cancel (b := g a)
    simpa only [one_mul] using h.symm
  have hL03 : g a ≠ g b := fun h => hab (hg h)
  have hL12 : X*g c ≠ Y*g a := by
    rw [hXc,hYa]
    exact fun h => hL03 (mul_left_cancel h)
  have hL13 : X*g c ≠ g b := by
    intro h
    have hh : g a*(g b)⁻¹ = g b*(g c)⁻¹ := by
      calc
        _ = (X*g c)*(g c)⁻¹ := by simp [X,mul_assoc]
        _ = _ := by rw [h]
    exact hab (hS a b b c hab hh).1
  have hL23 : Y*g a ≠ g b := by
    intro h
    have hh : (g d)⁻¹*g a = 1 := by
      apply mul_left_cancel (a := g b)
      simpa only [Y,mul_assoc,mul_one] using h
    exact had (hg (eq_of_inv_mul_eq_one hh)).symm
  let p : Fin 4 → G := ![1,X,Z,Y]
  let l : Fin 4 → G := ![g a,X*g c,Y*g a,g b]
  have hp : Function.Injective p := by
    intro i j he
    fin_cases i <;> fin_cases j <;> first | rfl | (
      dsimp [p] at he
      first | exact (hX he).elim | exact (hX he.symm).elim |
        exact (hY he).elim | exact (hY he.symm).elim |
        exact (hZ he).elim | exact (hZ he.symm).elim |
        exact (hXY he).elim | exact (hXY he.symm).elim |
        exact (hZX he).elim | exact (hZX he.symm).elim |
        exact (hZYne he).elim | exact (hZYne he.symm).elim)
  have hl : Function.Injective l := by
    intro i j he
    fin_cases i <;> fin_cases j <;> first | rfl | (
      dsimp [l] at he
      first | exact (hL01 he).elim | exact (hL01 he.symm).elim |
        exact (hL02 he).elim | exact (hL02 he.symm).elim |
        exact (hL03 he).elim | exact (hL03 he.symm).elim |
        exact (hL12 he).elim | exact (hL12 he.symm).elim |
        exact (hL13 he).elim | exact (hL13 he.symm).elim |
        exact (hL23 he).elim | exact (hL23 he.symm).elim)
  apply contains_of_octagon g p l hp hl
  · intro i
    fin_cases i
    · exact ⟨a,(one_mul _).symm⟩
    · exact ⟨c,rfl⟩
    · exact ⟨b,hYa⟩
    · refine ⟨d,?_⟩
      change g b = Y*g d
      simp [Y]
  · intro i
    fin_cases i
    · refine ⟨b,?_⟩
      change g a = X*g b
      simp [X]
    · exact ⟨a,hXc⟩
    · exact ⟨a,rfl⟩
    · exact ⟨b,(one_mul _).symm⟩

#print axioms contains
end Erdos713C8SidonWord
