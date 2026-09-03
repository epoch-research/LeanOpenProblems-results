import Submission.HigherLocalPolynomialProgressions
import Submission.BohrPatternGeometry

/-! A locally quadratic unit complex phase is a degree-two locally polynomial
map into the additive circle. This bridges the quadratic inverse output and
the existing all-degree recurrence/partition language. -/
namespace Erdos3QuadraticCircleBridge
open Finset Erdos3HigherPhaseDifferences Erdos3HigherLocalPolynomialProgressions
  Erdos3LocalQuadraticInverse Erdos3FiniteUniformity
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 4000000

lemma phase_injective : Function.Injective phase := by
  intro x y h
  have he : Additive.toMul x = Additive.toMul y := Subtype.ext h
  exact he

lemma phase_zero : phase (0 : Additive Circle) = 1 := rfl

variable {G : Type*} [AddCommGroup G]

noncomputable def circleLift (q : G → ℂ) (hq : ∀ x, ‖q x‖ = 1) : G → Additive Circle :=
  fun x ↦ Additive.ofMul (⟨q x,mem_sphere_zero_iff_norm.mpr (hq x)⟩ : Circle)

lemma phase_circleLift (q : G → ℂ) (hq : ∀ x, ‖q x‖ = 1) (x : G) :
    phase (circleLift q hq x) = q x := rfl

lemma phase_cube_three (Q : G → Additive Circle) (h : Fin 3 → G) (x : G) :
    phase (cubeDifference 3 Q h x) =
      derivative (derivative (derivative (fun t ↦ phase (Q t)) (h 0)) (h 1)) (h 2) x := by
  simp only [cubeDifference,fwdDiff,phase_sub,derivative]
  rfl

/-- The eight local quadraticity hypotheses are exactly the vertices of a
complete three-dimensional cube, with arbitrary ordered directions. -/
theorem local_quadratic_circle_polynomial {R : Set G} (q : G → ℂ)
    (hq : ∀ x, ‖q x‖ = 1) (hquad : IsLocallyQuadratic R q) :
    IsLocallyPolynomial R 2 (circleLift q hq) := by
  intro x h hR
  apply phase_injective
  rw [phase_zero,phase_cube_three]
  simp only [phase_circleLift]
  apply hquad
  · simpa using hR ∅
  · simpa using hR {0}
  · simpa using hR {1}
  · simpa [add_assoc] using hR {1,0}
  · simpa using hR {2}
  · simpa [add_assoc] using hR {2,0}
  · simpa [add_assoc] using hR {2,1}
  · simpa [add_assoc] using hR {2,1,0}

/-- A family of unit quadratic phases can be converted without changing any
complex coordinate value, hence without affecting factor approximation error. -/
theorem family_circle_lift {I : Type*} {R : Set G} (q : I → G → ℂ)
    (hq : ∀ i x, ‖q i x‖ = 1) (hquad : ∀ i, IsLocallyQuadratic R (q i)) :
    ∃ Q : I → G → Additive Circle,
      (∀ i, IsLocallyPolynomial R 2 (Q i)) ∧ (∀ i x, phase (Q i x) = q i x) :=
  ⟨fun i ↦ circleLift (q i) (hq i),
    fun i ↦ local_quadratic_circle_polynomial (q i) (hq i) (hquad i),fun _ _ ↦ rfl⟩

#print axioms local_quadratic_circle_polynomial
#print axioms family_circle_lift
end Erdos3QuadraticCircleBridge
