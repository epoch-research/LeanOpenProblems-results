import Submission.JointQuadraticConeAnisotropy
import Submission.FilteredQuadraticAlgebra

/-! All-degree rigidity of a constant quartic norm in the deformed
biquadratic coordinate algebras of the explicit pencil. -/
namespace Erdos322Research.JointQuadraticCone
noncomputable section
open MvPolynomial FilteredFourthNorm
set_option Elab.async false
set_option maxHeartbeats 0

abbrev FiberFirst (v : K) := QuadraticAlgebra Base (radicand₁+C v) 0
abbrev FiberRing (u v : K) :=
  QuadraticAlgebra (FiberFirst v) (algebraMap Base (FiberFirst v) (radicand₀+C u)) 0

def fiberBase (u v : K) : Base →+* FiberRing u v :=
  (algebraMap (FiberFirst v) (FiberRing u v)).comp (algebraMap Base (FiberFirst v))

lemma radicand₀_homogeneous : IsHomogeneous radicand₀ 2 := by
  exact ((isHomogeneous_C_mul_X_pow _ _ _).sub (isHomogeneous_C_mul_X_pow _ _ _)).sub
    (isHomogeneous_C_mul_X_pow _ _ _)

lemma radicand₁_homogeneous : IsHomogeneous radicand₁ 2 := by
  have hc : IsHomogeneous (-C (25/16:K) : Base) 0 :=
    (isHomogeneous_C (Fin 3) (25/16:K)).neg
  have hx : IsHomogeneous (X (0:Fin 3)^2 : Base) 2 := isHomogeneous_X_pow _ _
  have ht : IsHomogeneous (-C (25/16:K)*X (0:Fin 3)^2 : Base) 2 := hc.mul hx
  exact (ht.sub (isHomogeneous_C_mul_X_pow _ _ _)).sub (isHomogeneous_C_mul_X_pow _ _ _)

private lemma deformed_bound (a : Base) (ha : IsHomogeneous a 2) (c : K) :
    polynomialSystem.bounded 2 (a+C c) := by
  apply polynomialSystem.add_bounded
  · right
    exact_mod_cast ha.totalDegree_le
  · exact polynomialSystem.mono (by norm_num : (0:ℤ) ≤ 2) (polynomial_bound_C c)

private lemma deformed_top (a : Base) (ha : IsHomogeneous a 2) (c : K) :
    polynomialSystem.top 2 (a+C c) = a := by
  rw [show (2:ℤ) = ((2:ℕ):ℤ) from rfl,polynomial_top_nat,map_add]
  rw [homogeneousComponent_of_mem (show a ∈ homogeneousSubmodule (Fin 3) K 2 from ha)]
  rw [homogeneousComponent_eq_zero 2 (C c) (by simp)]
  simp

private def firstSystem (v : K) : LeadingSystem (FiberFirst v) FirstRoot :=
  quadraticSystem polynomialSystem (radicand₁+C v) radicand₁
    (deformed_bound radicand₁ radicand₁_homogeneous v)
    (deformed_top radicand₁ radicand₁_homogeneous v)

private lemma second_bound (u v : K) :
    (firstSystem v).bounded 2 (algebraMap Base (FiberFirst v) (radicand₀+C u)) := by
  exact quadratic_bound_base _ _ _ _ _ (deformed_bound radicand₀ radicand₀_homogeneous u)

private lemma second_top (u v : K) :
    (firstSystem v).top 2 (algebraMap Base (FiberFirst v) (radicand₀+C u)) =
      algebraMap Base FirstRoot radicand₀ := by
  rw [firstSystem,quadratic_top_base,deformed_top radicand₀ radicand₀_homogeneous u]

private def fiberSystem (u v : K) : LeadingSystem (FiberRing u v) ConeRing :=
  quadraticSystem (firstSystem v) (algebraMap Base (FiberFirst v) (radicand₀+C u))
    (algebraMap Base FirstRoot radicand₀) (second_bound u v) (second_top u v)

private lemma fiberBase_bound (u v : K) (c : K) :
    (fiberSystem u v).bounded 0 (fiberBase u v (C c)) := by
  apply quadratic_bound_base
  exact quadratic_bound_base _ _ _ _ _ (polynomial_bound_C c)

private lemma fiber_bounded_zero (u v : K) (p : FiberRing u v)
    (h : (fiberSystem u v).bounded 0 p) :
    p = fiberBase u v (C (coeff 0 p.re.re)) := by
  change (polynomialSystem.bounded 0 p.re.re ∧ polynomialSystem.bounded (0-1) p.re.im) ∧
    (polynomialSystem.bounded (0-1) p.im.re ∧ polynomialSystem.bounded ((0-1)-1) p.im.im) at h
  have h00 := polynomial_bound_zero p.re.re h.1.1
  have h01 := polynomial_bound_negative (by norm_num : (0:ℤ)-1 < 0) p.re.im h.1.2
  have h10 := polynomial_bound_negative (by norm_num : (0:ℤ)-1 < 0) p.im.re h.2.1
  have h11 := polynomial_bound_negative (by norm_num : ((0:ℤ)-1)-1 < 0) p.im.im h.2.2
  apply QuadraticAlgebra.ext
  · apply QuadraticAlgebra.ext
    · exact h00
    · exact h01
  · apply QuadraticAlgebra.ext
    · exact h10
    · exact h11

/-- Every element of a constant-norm quadruple in a fixed fiber algebra is
constant. There is no bound on the degrees of its four normal-form coefficients. -/
theorem fiber_constant_norm (u v : K) (p : Fin 4 → FiberRing u v) (c : K)
    (h : (∑ i, p i^4) = fiberBase u v (C c)) :
    ∀ i, p i = fiberBase u v (C (coeff 0 (p i).re.re)) := by
  have hb := (fiberSystem u v).constant_norm_bounded_zero cone_ring_anisotropic p
    (by rw [h]; exact fiberBase_bound u v c)
  exact fun i ↦ fiber_bounded_zero u v (p i) (hb i)

end
end Erdos322Research.JointQuadraticCone
