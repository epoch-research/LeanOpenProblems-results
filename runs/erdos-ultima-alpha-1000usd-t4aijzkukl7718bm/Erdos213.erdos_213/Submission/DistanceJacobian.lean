import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-! The length-variable Jacobian minor for the full planar distance equations.
A nonzero edge-length assignment makes this minor nonsingular, including at
collinear configurations with distinct vertices. This does not prove a
rational parametrization or a rational-point existence theorem. -/
namespace Erdos213.DistanceJacobian
open MvPolynomial
noncomputable section

variable {V E : Type*} [DecidableEq E]

abbrev Variables (V E : Type*) := (V × Fin 2) ⊕ E

def equation (s t : E → V) (e : E) : MvPolynomial (Variables V E) ℚ :=
  (X (Sum.inl (s e,0))-X (Sum.inl (t e,0)))^2+
  (X (Sum.inl (s e,1))-X (Sum.inl (t e,1)))^2-X (Sum.inr e)^2

lemma length_pderiv (s t : E → V) (e f : E) :
    pderiv (Sum.inr f) (equation s t e) =
      if e=f then -2*X (Sum.inr e) else 0 := by
  by_cases he : e=f
  · subst f
    simp [equation]
  · simp [equation,he]

def assignment (x y : V → ℚ) (d : E → ℚ) : Variables V E → ℚ :=
  Sum.elim (fun p => if p.2=0 then x p.1 else y p.1) d

omit [DecidableEq E] in
lemma equation_eval (s t : E → V) (x y : V → ℚ) (d : E → ℚ) (e : E) :
    eval (assignment x y d) (equation s t e)=
      (x (s e)-x (t e))^2+(y (s e)-y (t e))^2-d e^2 := by
  simp [equation,assignment]

/-- The square submatrix with one row per edge equation and one column per
length variable. Coordinate-variable columns are not part of this minor. -/
def lengthJacobian (s t : E → V) (x y : V → ℚ) (d : E → ℚ) : Matrix E E ℚ :=
  fun e f => eval (assignment x y d) (pderiv (Sum.inr f) (equation s t e))

lemma lengthJacobian_eq_diagonal (s t : E → V) (x y : V → ℚ) (d : E → ℚ) :
    lengthJacobian s t x y d=Matrix.diagonal (fun e => -2*d e) := by
  ext e f
  by_cases h : e=f
  · subst f
    simp [lengthJacobian,length_pderiv,assignment]
  · simp [lengthJacobian,length_pderiv,assignment,h]

/-- All equations have independent length-variable differentials as soon as
no edge length vanishes. No noncollinearity assumption is needed. -/
theorem lengthJacobian_det_ne_zero [Fintype E] (s t : E → V) (x y : V → ℚ)
    (d : E → ℚ) (hd : ∀ e, d e ≠ 0) : (lengthJacobian s t x y d).det ≠ 0 := by
  rw [lengthJacobian_eq_diagonal,Matrix.det_diagonal]
  apply Finset.prod_ne_zero_iff.mpr
  intro e _
  exact mul_ne_zero (by norm_num) (hd e)

/-- Every distinct-ended collinear rational configuration satisfies the full
distance equations and has a nonsingular length-variable minor. The signed
lengths are a convenient algebraic branch; their squares are the same as the
squares of the actual nonnegative real distances. -/
theorem collinear_nonsingular [Fintype E] (s t : E → V) (hst : ∀ e, s e ≠ t e)
    (a : V → ℚ) (ha : Function.Injective a) :
    (∀ e, eval (assignment a (fun _ => 0) (fun e => a (s e)-a (t e)))
      (equation s t e)=0) ∧
    (lengthJacobian s t a (fun _ => 0) (fun e => a (s e)-a (t e))).det ≠ 0 := by
  constructor
  · intro e
    simp [equation_eval]
  · apply lengthJacobian_det_ne_zero
    intro e
    exact sub_ne_zero.mpr (ha.ne (hst e))

#print axioms length_pderiv
#print axioms lengthJacobian_det_ne_zero
#print axioms collinear_nonsingular
end
end Erdos213.DistanceJacobian
