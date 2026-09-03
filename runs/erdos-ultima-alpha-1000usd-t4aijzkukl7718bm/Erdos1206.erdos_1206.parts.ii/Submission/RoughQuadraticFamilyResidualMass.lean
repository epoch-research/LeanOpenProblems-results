import Submission.QuadraticFamilyResidualMass
import Submission.RoughNearUnitPrimitiveMass

/-! Finite quadratic-family removal and any fixed finite-prime sieve together
still leave divergent per-collision reciprocal height mass. This does not
settle the positive-density cube-Sidon conjecture. -/
namespace Erdos1206.RoughQuadraticFamilyResidualMass
open FermatCubicConics QuadraticFamilyAvoidance QuadraticFamilyResidualMass
open PrimitiveCollisionMass (Collision)

/-- Collision-wise reciprocal summability is unavailable even after BOTH
finite-family removal and a fixed finite-prime source restriction. This says
nothing about the cost of a cover that reuses vertices or divisors. -/
theorem outside_reciprocal_heights_not_summable {ι : Type*} [Finite ι]
    (a b c d : ι → Vec)
    (hc : ∀ i, quad (a i)^3+quad (d i)^3=quad (b i)^3+quad (c i)^3)
    (Q : ℕ) (hQ : 0<Q) :
    ¬ Summable (fun e : {e : Collision // Outside a b c d e ∧
      Nat.Coprime e.val.1 Q ∧ Nat.Coprime e.val.2.1 Q ∧
      Nat.Coprime e.val.2.2.1 Q ∧ Nat.Coprime e.val.2.2.2 Q} =>
      (1:ℝ)/e.val.val.2.2.2) := by
  intro hs
  obtain ⟨H,hH,hbound⟩ := finite_uniform_gap_bound a b c d hc
  let f : RoughNearUnitPrimitiveMass.Residual Q H →
      {e : Collision // Outside a b c d e ∧
        Nat.Coprime e.val.1 Q ∧ Nat.Coprime e.val.2.1 Q ∧
        Nat.Coprime e.val.2.2.1 Q ∧ Nat.Coprime e.val.2.2.2 Q} :=
    fun e => ⟨e.val,
      residual_outside a b c d H (fun i x hx => (hbound i x hx).1) ⟨e.val,e.property.1⟩,
      e.property.2⟩
  have hf : Function.Injective f := by
    intro x y he
    have hh : (f x).val=(f y).val := congrArg
      (fun e : {e : Collision // Outside a b c d e ∧
        Nat.Coprime e.val.1 Q ∧ Nat.Coprime e.val.2.1 Q ∧
        Nat.Coprime e.val.2.2.1 Q ∧ Nat.Coprime e.val.2.2.2 Q} => e.val) he
    exact Subtype.ext hh
  have hcomp := hs.comp_injective hf
  exact RoughNearUnitPrimitiveMass.residual_reciprocal_heights_not_summable Q H hQ hcomp

#print axioms outside_reciprocal_heights_not_summable
end Erdos1206.RoughQuadraticFamilyResidualMass
