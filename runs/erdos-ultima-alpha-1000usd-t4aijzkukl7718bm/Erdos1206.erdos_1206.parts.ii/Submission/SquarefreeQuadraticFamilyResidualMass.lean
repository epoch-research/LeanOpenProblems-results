import Submission.QuadraticFamilyResidualMass
import Submission.RoughSquarefreePrimitiveMass

/-!
Squarefree roots and avoidance of any prescribed finite set of primes do
not restore per-collision reciprocal summability outside finitely many
quadratic families. This is not an independence or Sidon-density theorem.
-/
namespace Erdos1206.SquarefreeQuadraticFamilyResidualMass
open FermatCubicConics QuadraticFamilyAvoidance QuadraticFamilyResidualMass
open PrimitiveCollisionMass (Collision)

/-- The reciprocal maximum-root mass over distinct primitive collisions
outside finitely many quadratic planes still diverges when every root is
squarefree and coprime to Q. The sum is NOT over distinct maximum roots. -/
theorem outside_reciprocal_heights_not_summable {ι : Type*} [Finite ι]
    (a b c d : ι → Vec)
    (hc : ∀ i, quad (a i)^3+quad (d i)^3=quad (b i)^3+quad (c i)^3)
    (Q : ℕ) (hQ : 0 < Q) :
    ¬ Summable (fun e : {e : Collision // Outside a b c d e ∧
      (Squarefree e.val.1 ∧ Nat.Coprime e.val.1 Q) ∧
      (Squarefree e.val.2.1 ∧ Nat.Coprime e.val.2.1 Q) ∧
      (Squarefree e.val.2.2.1 ∧ Nat.Coprime e.val.2.2.1 Q) ∧
      (Squarefree e.val.2.2.2 ∧ Nat.Coprime e.val.2.2.2 Q)} =>
      (1:ℝ)/e.val.val.2.2.2) := by
  intro hs
  obtain ⟨H,hH,hbound⟩ := finite_uniform_gap_bound a b c d hc
  let S := {e : Collision // Outside a b c d e ∧
      (Squarefree e.val.1 ∧ Nat.Coprime e.val.1 Q) ∧
      (Squarefree e.val.2.1 ∧ Nat.Coprime e.val.2.1 Q) ∧
      (Squarefree e.val.2.2.1 ∧ Nat.Coprime e.val.2.2.1 Q) ∧
      (Squarefree e.val.2.2.2 ∧ Nat.Coprime e.val.2.2.2 Q)}
  let f : RoughSquarefreePrimitiveMass.Residual Q H → S := fun e => ⟨e.val,
    residual_outside a b c d H (fun i x hx => (hbound i x hx).1) ⟨e.val,e.property.1⟩,
    e.property.2⟩
  have hf : Function.Injective f := by
    intro x y he
    have hh : (f x).val=(f y).val := congrArg (fun e : S => e.val) he
    exact Subtype.ext hh
  have hcomp := hs.comp_injective hf
  exact RoughSquarefreePrimitiveMass.residual_reciprocal_heights_not_summable Q H hQ hcomp

#print axioms outside_reciprocal_heights_not_summable
end Erdos1206.SquarefreeQuadraticFamilyResidualMass
