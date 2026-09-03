import FormalConjecturesUtil
import Submission.C8CommutingDifferences

/-! An involutive-parameter word supplies an injective octagon. This is
an auxiliary construction obstruction, not a solution of Erdős 713. -/
open SimpleGraph
namespace Erdos713C8InvolutiveSidonWord
open Erdos713C8CommutingDifferences
variable {G I : Type*} [Group G]
set_option maxHeartbeats 1000000

theorem contains (g : I → G) (hg : Function.Injective g)
    (hS : ∀ a b c d, a ≠ b → g a*(g b)⁻¹ = g c*(g d)⁻¹ → a=c ∧ b=d)
    (τ : I → I) (hτ : Function.Involutive τ) (hfix : ∀ i, τ i ≠ i)
    (r c d : I) (hcr : c ≠ r) (hcr' : c ≠ τ r)
    (hcd : c ≠ d) (hcd' : c ≠ τ d)
    (hword : g (τ r)*(g r)⁻¹*g c*(g d)⁻¹ =
      g r*(g (τ c))⁻¹*g d*(g (τ d))⁻¹) :
    cycleGraph 8 ⊑ graph g := by
  let X := g (τ r)*(g r)⁻¹
  let Y := g r*(g (τ c))⁻¹
  let Z := X*g c*(g d)⁻¹
  have hZY : Z = Y*g d*(g (τ d))⁻¹ := hword
  have hX : X ≠ 1 := fun h => hfix r (hg (eq_of_mul_inv_eq_one h))
  have hY : Y ≠ 1 := by
    intro h
    have he := congrArg τ (hg (eq_of_mul_inv_eq_one h))
    exact hcr' (by simpa only [hτ c] using he.symm)
  have hZ : Z ≠ 1 := by
    intro h
    have hh : X = g d*(g c)⁻¹ := by
      calc
        X = Z*g d*(g c)⁻¹ := by simp [Z,mul_assoc]
        _ = _ := by rw [h,one_mul]
    exact hcr (hS (τ r) r d c (hfix r) hh).2.symm
  have hXY : X ≠ Y := fun h => hfix r (hS (τ r) r r (τ c) (hfix r) h).1
  have hZX : Z ≠ X := by
    intro h
    have hh : g c*(g d)⁻¹ = 1 := by
      apply mul_left_cancel (a := X)
      simpa only [Z,mul_assoc,mul_one] using h
    exact hcd (hg (eq_of_mul_inv_eq_one hh))
  have hZYne : Z ≠ Y := by
    intro h
    have hh : g d*(g (τ d))⁻¹ = 1 := by
      apply mul_left_cancel (a := Y)
      simpa only [hZY,mul_assoc,mul_one] using h
    exact hfix d (hg (eq_of_mul_inv_eq_one hh)).symm
  have hXc : X*g c = Z*g d := by simp [Z,mul_assoc]
  have hYd : Y*g d = Z*g (τ d) := by rw [hZY]; simp [mul_assoc]
  have hL01 : g (τ r) ≠ X*g c := by
    intro h
    have hh : (g r)⁻¹*g c = 1 := by
      apply mul_left_cancel (a := g (τ r))
      simpa only [X,mul_assoc,mul_one] using h.symm
    exact hcr (hg (eq_of_inv_mul_eq_one hh)).symm
  have hL02 : g (τ r) ≠ Y*g d := by
    intro h
    have hh : g (τ r)*(g d)⁻¹ = g r*(g (τ c))⁻¹ := by
      rw [h]
      simp only [mul_assoc,mul_inv_cancel,mul_one]
      rfl
    have hrd : τ r ≠ d := by
      intro he
      apply hY
      simpa only [he,mul_inv_cancel] using hh.symm
    exact hfix r (hS (τ r) d r (τ c) hrd hh).1
  have hL03 : g (τ r) ≠ g r := fun h => hfix r (hg h)
  have hL12 : X*g c ≠ Y*g d := by
    rw [hXc]
    exact fun h => hZYne (mul_right_cancel h)
  have hL13 : X*g c ≠ g r := by
    intro h
    have hh : g (τ r)*(g r)⁻¹ = g r*(g c)⁻¹ := by
      calc
        _ = (X*g c)*(g c)⁻¹ := by simp [X,mul_assoc]
        _ = _ := by rw [h]
    exact hfix r (hS (τ r) r r c (hfix r) hh).1
  have hL23 : Y*g d ≠ g r := by
    intro h
    have hh : (g (τ c))⁻¹*g d = 1 := by
      apply mul_left_cancel (a := g r)
      simpa only [Y,mul_assoc,mul_one] using h
    have he := congrArg τ (hg (eq_of_inv_mul_eq_one hh))
    exact hcd' (by simpa only [hτ c] using he)
  let p : Fin 4 → G := ![1,X,Z,Y]
  let l : Fin 4 → G := ![g (τ r),X*g c,Y*g d,g r]
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
    · exact ⟨τ r,(one_mul _).symm⟩
    · exact ⟨c,rfl⟩
    · exact ⟨τ d,hYd⟩
    · refine ⟨τ c,?_⟩
      change g r = Y*g (τ c)
      simp [Y]
  · intro i
    fin_cases i
    · refine ⟨r,?_⟩
      change g (τ r) = X*g r
      simp [X]
    · exact ⟨d,hXc⟩
    · exact ⟨d,rfl⟩
    · exact ⟨r,(one_mul _).symm⟩

#print axioms contains
end Erdos713C8InvolutiveSidonWord
