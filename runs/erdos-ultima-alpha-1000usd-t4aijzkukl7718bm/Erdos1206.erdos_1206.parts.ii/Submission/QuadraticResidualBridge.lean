import Submission.VeroneseQuadrics
import Submission.QuadraticTriplePlaneObstructions

/-!
Residual quadrics for normalized difference relations on a rational
quadratic four-cube family. Polynomial cancellation is used before evaluation.
-/
namespace Erdos1206.QuadraticResidualBridge
open Polynomial FermatCubicConics FermatCubicSubspaces VeroneseQuadrics

noncomputable def differenceResidual (r : ℚ) (a b c d : Vec) (x : Vec) : ℚ :=
  r*((linear a x)^2+linear a x*linear c x+(linear c x)^2)+
    ((linear b x)^2+linear b x*linear d x+(linear d x)^2)

noncomputable def residualPolynomial (r : ℚ) (a b c d : Vec) : ℚ[X] :=
  C r*(quad a^2+quad a*quad c+quad c^2)+(quad b^2+quad b*quad d+quad d^2)

lemma quad_eval (a : Vec) (t : ℚ) :
    (quad a).eval t=linear a ![t^2,t,1] := by simp [quad,linear]

lemma polynomial_relation {a b c d : Vec} {r : ℚ}
    (h : ∀ x, linear a x-linear c x=r*(linear b x-linear d x)) :
    quad a-quad c=C r*(quad b-quad d) := by
  apply Polynomial.funext
  intro t
  simpa only [eval_sub,eval_mul,eval_C,quad_eval] using h ![t^2,t,1]

lemma residual_isQuad (r : ℚ) (a b c d : Vec) :
    IsQuad (differenceResidual r a b c d) := by
  unfold differenceResidual
  simpa only [pow_two] using
    ((((linear_product a a).add (linear_product a c)).add (linear_product c c)).smul r).add
      (((linear_product b b).add (linear_product b d)).add (linear_product d d))

private lemma factor_identity {K : Type*} [CommRing K] {A B C D r : K}
    (h : A-C=r*(B-D)) :
    A^3+B^3-C^3-D^3=(B-D)*(r*(A^2+A*C+C^2)+(B^2+B*D+D^2)) := by
  linear_combination (A^2+A*C+C^2)*h

/-- The residual vanishes even at parameter values where the canceled
pair difference vanishes: cancellation takes place in Q[X]. -/
theorem residual_vanishes {a b c d : Vec} {r : ℚ}
    (h : ∀ x, linear a x-linear c x=r*(linear b x-linear d x))
    (he : quad a^3+quad b^3=quad c^3+quad d^3) (hd : quad b ≠ quad d) :
    ∀ t : ℚ, differenceResidual r a b c d ![t^2,t,1]=0 := by
  have hp : (quad b-quad d)*residualPolynomial r a b c d=0 := by
    dsimp only [residualPolynomial]
    rw [← factor_identity (polynomial_relation h)]
    linear_combination he
  have hz : residualPolynomial r a b c d=0 :=
    (mul_eq_zero.mp hp).resolve_left (sub_ne_zero.mpr hd)
  intro t
  have hh := congrArg (fun p : ℚ[X] => p.eval t) hz
  simpa only [residualPolynomial,eval_add,eval_mul,eval_pow,eval_C,eval_zero,
    quad_eval,differenceResidual] using hh

/-- Joint injectivity rules out an identically zero residual. -/
theorem residual_nonzero {a b c d : Vec} {r : ℚ}
    (h : ∀ x, linear a x-linear c x=r*(linear b x-linear d x))
    (hj : JointlyInjective (linear a) (linear b) (linear c) (linear d)) :
    ∃ x, differenceResidual r a b c d x ≠ 0 := by
  by_contra! hz
  have hh : ∀ x, (linear a x)^3+(linear b x)^3+
      ((-linear c) x)^3+((-linear d) x)^3=0 := by
    intro x
    have hf := factor_identity (h x)
    change _ = (linear b x-linear d x)*differenceResidual r a b c d x at hf
    rw [hz x,mul_zero] at hf
    simp only [LinearMap.neg_apply]
    linear_combination hf
  have hj' : JointlyInjective (linear a) (linear b) (-linear c) (-linear d) := by
    intro x ha hb hc hd
    apply hj x ha hb
    · simpa using hc
    · simpa using hd
  have hf := subspace_finrank_le_two hj' hh
  norm_num [Vec,Module.finrank_pi] at hf

/-- Two normalized nondegenerate identities for a common pair produce
proportional residual quadrics on the full three-dimensional space. -/
theorem residuals_proportional {a b c d e f : Vec} {r s : ℚ}
    (h₁ : ∀ x, linear a x-linear c x=r*(linear b x-linear d x))
    (h₂ : ∀ x, linear a x-linear e x=s*(linear b x-linear f x))
    (he₁ : quad a^3+quad b^3=quad c^3+quad d^3)
    (he₂ : quad a^3+quad b^3=quad e^3+quad f^3)
    (hd : quad b ≠ quad d) (hf : quad b ≠ quad f)
    (hj : JointlyInjective (linear a) (linear b) (linear e) (linear f)) :
    ∃ l : ℚ, ∀ x, differenceResidual r a b c d x=l*differenceResidual s a b e f x := by
  exact vanishing_proportional (residual_isQuad r a b c d) (residual_isQuad s a b e f)
    (residual_vanishes h₁ he₁ hd) (residual_vanishes h₂ he₂ hf) (residual_nonzero h₂ hj)

#print axioms residual_vanishes
#print axioms residual_nonzero
#print axioms residuals_proportional
end Erdos1206.QuadraticResidualBridge
