import Submission.FermatCubicSubspaces

/-!
The residual rational line of a nondegenerate quadratic family on the Fermat
cubic. This supplies a conic-plane reduction, not a density construction.
-/

namespace Erdos1206.FermatCubicConics
open Polynomial Module FermatCubicSubspaces
abbrev Vec := Fin 3 → ℚ

noncomputable def linear (a : Vec) : Vec →ₗ[ℚ] ℚ where
  toFun x := a 0*x 0+a 1*x 1+a 2*x 2
  map_add' := by intro x y; simp; ring
  map_smul' := by intro c x; simp; ring

noncomputable def quad (a : Vec) : ℚ[X] := C (a 0)*X^2+C (a 1)*X+C (a 2)

private def cubicCoeffs (a b c d : Vec) : Fin 10 → ℚ :=
  ![a 0^3+b 0^3+c 0^3+d 0^3,
    3*(a 0^2*a 1+b 0^2*b 1+c 0^2*c 1+d 0^2*d 1),
    3*(a 0^2*a 2+b 0^2*b 2+c 0^2*c 2+d 0^2*d 2),
    3*(a 0*a 1^2+b 0*b 1^2+c 0*c 1^2+d 0*d 1^2),
    6*(a 0*a 1*a 2+b 0*b 1*b 2+c 0*c 1*c 2+d 0*d 1*d 2),
    3*(a 0*a 2^2+b 0*b 2^2+c 0*c 2^2+d 0*d 2^2),
    a 1^3+b 1^3+c 1^3+d 1^3,
    3*(a 1^2*a 2+b 1^2*b 2+c 1^2*c 2+d 1^2*d 2),
    3*(a 1*a 2^2+b 1*b 2^2+c 1*c 2^2+d 1*d 2^2),
    a 2^3+b 2^3+c 2^3+d 2^3]

private def cubicForm (z : Fin 10 → ℚ) (x : Vec) : ℚ :=
  z 0*(x 0)^3+z 1*(x 0)^2*x 1+z 2*(x 0)^2*x 2+
  z 3*x 0*(x 1)^2+z 4*x 0*x 1*x 2+z 5*x 0*(x 2)^2+
  z 6*(x 1)^3+z 7*(x 1)^2*x 2+z 8*x 1*(x 2)^2+z 9*(x 2)^3

private noncomputable def veronesePolynomial (z : Fin 10 → ℚ) : ℚ[X] :=
  C (z 0)*X^6+C (z 1)*X^5+C (z 2+z 3)*X^4+C (z 4+z 6)*X^3+
  C (z 5+z 7)*X^2+C (z 8)*X+C (z 9)

private lemma cube_expansion (a b c d x : Vec) :
    (linear a x)^3+(linear b x)^3+(linear c x)^3+(linear d x)^3=
      cubicForm (cubicCoeffs a b c d) x := by
  dsimp [linear,cubicForm,cubicCoeffs]
  ring

private lemma veronese_expansion (a b c d : Vec) :
    veronesePolynomial (cubicCoeffs a b c d)=quad a^3+quad b^3+quad c^3+quad d^3 := by
  dsimp [veronesePolynomial,cubicCoeffs,quad]
  simp only [map_add,map_mul,map_pow,map_ofNat]
  ring

private lemma residual_identity {z : Fin 10 → ℚ} (he : veronesePolynomial z=0) (x : Vec) :
    cubicForm z x=(x 0*x 2-(x 1)^2)*(z 2*x 0+z 4*x 1+z 5*x 2) := by
  have h₀ := congrArg (fun p : ℚ[X] => p.coeff 0) he
  have h₁ := congrArg (fun p : ℚ[X] => p.coeff 1) he
  have h₂ := congrArg (fun p : ℚ[X] => p.coeff 2) he
  have h₃ := congrArg (fun p : ℚ[X] => p.coeff 3) he
  have h₄ := congrArg (fun p : ℚ[X] => p.coeff 4) he
  have h₅ := congrArg (fun p : ℚ[X] => p.coeff 5) he
  have h₆ := congrArg (fun p : ℚ[X] => p.coeff 6) he
  norm_num only [veronesePolynomial,coeff_add,coeff_C_mul_X_pow,coeff_C_mul_X,
    coeff_C,coeff_zero,ite_true,ite_false,zero_add,add_zero] at h₀ h₁ h₂ h₃ h₄ h₅ h₆
  dsimp [cubicForm]
  linear_combination (x 0)^3*h₆+(x 0)^2*x 1*h₅+x 0*(x 1)^2*h₄+
    (x 1)^3*h₃+(x 1)^2*x 2*h₂+x 1*(x 2)^2*h₁+(x 2)^3*h₀

/-- The residual linear form, with the conic U*W-V^2 factored out. -/
noncomputable def residual (a b c d : Vec) : Vec →ₗ[ℚ] ℚ :=
  let z := cubicCoeffs a b c d
  linear ![z 2,z 4,z 5]

/-- Explicit polynomial division by the Veronese conic. -/
theorem conic_factorization {a b c d : Vec}
    (he : quad a^3+quad b^3+quad c^3+quad d^3=0) (x : Vec) :
    (linear a x)^3+(linear b x)^3+(linear c x)^3+(linear d x)^3=
      (x 0*x 2-(x 1)^2)*residual a b c d x := by
  have hp : veronesePolynomial (cubicCoeffs a b c d)=0 := by
    rw [veronese_expansion,he]
  rw [cube_expansion,residual_identity hp]
  rfl

/-- Injectivity of the three-dimensional linearization ensures that the
residual linear form is not zero. -/
theorem residual_ne_zero {a b c d : Vec}
    (hj : JointlyInjective (linear a) (linear b) (linear c) (linear d))
    (he : quad a^3+quad b^3+quad c^3+quad d^3=0) : residual a b c d ≠ 0 := by
  intro hz
  have hh : ∀ x, (linear a x)^3+(linear b x)^3+(linear c x)^3+(linear d x)^3=0 := by
    intro x
    rw [conic_factorization he x,hz]
    simp
  have hd := subspace_finrank_le_two hj hh
  norm_num [Vec,finrank_pi] at hd

/-- Linear dependence of a pair of polynomial coordinates over the constants. -/
def PolynomialPairDependent (p q : ℚ[X]) : Prop :=
  ∃ r s : ℚ, (r ≠ 0 ∨ s ≠ 0) ∧ C r*p+C s*q=0

private lemma polynomial_pair_of_linear {a b c d : Vec}
    (hp : PairDependent (linear a+linear b) (linear c+linear d)) :
    PolynomialPairDependent (quad a+quad b) (quad c+quad d) := by
  obtain ⟨r,s,hrs,he⟩ := hp
  refine ⟨r,s,hrs,?_⟩
  apply Polynomial.funext
  intro t
  have hh := congrArg (fun f : Vec →ₗ[ℚ] ℚ => f ![t^2,t,1]) he
  change r*(linear a ![t^2,t,1]+linear b ![t^2,t,1])+
    s*(linear c ![t^2,t,1]+linear d ![t^2,t,1])=0 at hh
  simpa [linear,quad] using hh

/-- Every nondegenerate rational quadratic family has one of the three
rational pair relations arising from the residual line. No orientation or
proportional-pair-sum case is omitted. -/
theorem quadratic_pair_relation {a b c d : Vec}
    (hj : JointlyInjective (linear a) (linear b) (linear c) (linear d))
    (he : quad a^3+quad b^3+quad c^3+quad d^3=0) :
    PolynomialPairDependent (quad a+quad b) (quad c+quad d) ∨
    PolynomialPairDependent (quad a+quad c) (quad b+quad d) ∨
    PolynomialPairDependent (quad a+quad d) (quad b+quad c) := by
  have hk : ∀ x, residual a b c d x=0 →
      (linear a x)^3+(linear b x)^3+(linear c x)^3+(linear d x)^3=0 := by
    intro x hx
    rw [conic_factorization he x,hx,mul_zero]
  rcases residual_pair_dependency hj (by simp [Vec]) hk with hp | hp | hp
  · exact Or.inl (polynomial_pair_of_linear hp)
  · exact Or.inr (Or.inl (polynomial_pair_of_linear hp))
  · exact Or.inr (Or.inr (polynomial_pair_of_linear hp))

#print axioms conic_factorization
#print axioms residual_ne_zero
#print axioms quadratic_pair_relation
end Erdos1206.FermatCubicConics
