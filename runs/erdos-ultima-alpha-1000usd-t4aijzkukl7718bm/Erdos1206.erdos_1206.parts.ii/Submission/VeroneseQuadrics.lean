import Submission.FermatCubicConics

/-!
The space of quadratic forms vanishing on the Veronese conic has dimension
one. This verifies the proportionality step needed in the conic analysis.
-/

namespace Erdos1206.VeroneseQuadrics
open Polynomial FermatCubicConics

def form (z : Fin 6 → ℚ) (x : Vec) : ℚ :=
  z 0*(x 0)^2+z 1*x 0*x 1+z 2*x 0*x 2+
  z 3*(x 1)^2+z 4*x 1*x 2+z 5*(x 2)^2

private noncomputable def poly (z : Fin 6 → ℚ) : ℚ[X] :=
  C (z 0)*X^4+C (z 1)*X^3+C (z 2+z 3)*X^2+C (z 4)*X+C (z 5)

/-- A scalar-valued homogeneous quadratic form on the three coordinates. -/
def IsQuad (F : Vec → ℚ) : Prop := ∃ z : Fin 6 → ℚ, ∀ x, F x=form z x

lemma IsQuad.add {F G : Vec → ℚ} (hF : IsQuad F) (hG : IsQuad G) :
    IsQuad (fun x => F x+G x) := by
  obtain ⟨a,ha⟩ := hF
  obtain ⟨b,hb⟩ := hG
  refine ⟨a+b,fun x => ?_⟩
  dsimp only
  rw [ha,hb]
  dsimp [form]
  ring

lemma IsQuad.smul {F : Vec → ℚ} (hF : IsQuad F) (r : ℚ) :
    IsQuad (fun x => r*F x) := by
  obtain ⟨a,ha⟩ := hF
  refine ⟨r • a,fun x => ?_⟩
  dsimp only
  rw [ha]
  simp only [form,Pi.smul_apply,smul_eq_mul]
  ring

lemma linear_product (a b : Vec) : IsQuad (fun x => linear a x*linear b x) := by
  refine ⟨![a 0*b 0,a 0*b 1+a 1*b 0,a 0*b 2+a 2*b 0,
    a 1*b 1,a 1*b 2+a 2*b 1,a 2*b 2],fun x => ?_⟩
  dsimp [form,linear]
  ring

/-- Every quadratic form vanishing on the rational Veronese parametrization
is a scalar multiple of its defining conic. -/
theorem vanishing_scalar {F : Vec → ℚ} (hF : IsQuad F)
    (hz : ∀ t : ℚ, F ![t^2,t,1]=0) :
    ∃ r : ℚ, ∀ x, F x=r*(x 0*x 2-(x 1)^2) := by
  obtain ⟨a,ha⟩ := hF
  have hp : poly a=0 := by
    apply Polynomial.funext
    intro t
    rw [eval_zero]
    have hh := hz t
    rw [ha] at hh
    have he : (poly a).eval t=form a ![t^2,t,1] := by
      dsimp [poly,form]
      simp only [eval_add,eval_mul,eval_C,eval_pow,eval_X]
      ring
    exact he.trans hh
  have h₀ := congrArg (fun p : ℚ[X] => p.coeff 0) hp
  have h₁ := congrArg (fun p : ℚ[X] => p.coeff 1) hp
  have h₂ := congrArg (fun p : ℚ[X] => p.coeff 2) hp
  have h₃ := congrArg (fun p : ℚ[X] => p.coeff 3) hp
  have h₄ := congrArg (fun p : ℚ[X] => p.coeff 4) hp
  norm_num only [poly,coeff_add,coeff_C_mul_X_pow,coeff_C_mul_X,coeff_C,coeff_zero,
    ite_true,ite_false,zero_add,add_zero] at h₀ h₁ h₂ h₃ h₄
  refine ⟨a 2,fun x => ?_⟩
  rw [ha]
  dsimp [form]
  linear_combination (x 0)^2*h₄+x 0*x 1*h₃+(x 1)^2*h₂+x 1*x 2*h₁+(x 2)^2*h₀

/-- Two such quadrics are proportional, as long as the second is not the
zero form. Both hypotheses are needed when applying this to plane sections. -/
theorem vanishing_proportional {F G : Vec → ℚ} (hF : IsQuad F) (hG : IsQuad G)
    (hFz : ∀ t : ℚ, F ![t^2,t,1]=0) (hGz : ∀ t : ℚ, G ![t^2,t,1]=0)
    (hGn : ∃ x, G x ≠ 0) : ∃ r : ℚ, ∀ x, F x=r*G x := by
  obtain ⟨r,hr⟩ := vanishing_scalar hF hFz
  obtain ⟨s,hs⟩ := vanishing_scalar hG hGz
  have hs0 : s ≠ 0 := by
    intro he
    obtain ⟨x,hx⟩ := hGn
    exact hx (by rw [hs,he,zero_mul])
  refine ⟨r/s,fun x => ?_⟩
  rw [hr,hs]
  field_simp

#print axioms vanishing_scalar
#print axioms vanishing_proportional
end Erdos1206.VeroneseQuadrics
