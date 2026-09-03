import Submission.QuarticQuadraticMiddleZero

/-! Quadratic-form and linear-intersection versions of the F_5 incidence
lemma. These lemmas do not bound the full quartic representation count. -/
namespace Erdos322Research.QuadraticFormMiddleZero

open Finset MvPolynomial QuadraticMap
open QuarticQuadraticMiddleZero
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
noncomputable instance : Invertible (2 : K) := invertibleOfNonzero (by decide)

private lemma basis_expansion (x : V) : x = ∑ i, x i • axis i := by
  funext j
  simp [axis, Pi.single_apply]

noncomputable def formPolynomial (Q : QuadraticForm K V) : MvPolynomial (Fin 4) K :=
  ∑ i, ∑ j, C ((associated Q) (axis i) (axis j))*X i*X j

theorem formPolynomial_homogeneous (Q : QuadraticForm K V) :
    (formPolynomial Q).IsHomogeneous 2 := by
  apply IsHomogeneous.sum
  intro i _
  apply IsHomogeneous.sum
  intro j _
  exact ((isHomogeneous_C _ _).mul (isHomogeneous_X K i)).mul (isHomogeneous_X K j)

theorem formPolynomial_eval (Q : QuadraticForm K V) (x : V) :
    eval x (formPolynomial Q) = Q x := by
  have he : (associated Q) (∑ i, x i • axis i) (∑ j, x j • axis j) =
      ∑ i, ∑ j, (associated Q) (axis i) (axis j)*x i*x j := by
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul]
    apply sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply sum_congr rfl
    intro j _
    rw [associated_isSymm K Q (axis j) (axis i)]
    ring
  rw [← basis_expansion x] at he
  have hh : (associated Q) x x = Q x := associated_eq_self_apply K Q x
  rw [hh] at he
  simpa only [formPolynomial, map_sum, map_mul, eval_C, eval_X] using he.symm

/-- The incidence lemma for an abstract quadratic form. -/
theorem exists_middle_zero_form (Q : QuadraticForm K V) :
    ∃ x : V, (supportCount x = 2 ∨ supportCount x = 3) ∧ Q x = 0 := by
  obtain ⟨x,hx,hq⟩ := exists_middle_zero (formPolynomial Q) (formPolynomial_homogeneous Q)
  exact ⟨x,hx,by simpa only [formPolynomial_eval] using hq⟩

private lemma anisotropic_binary : ∀ a b : K, a*a-2*(b*b)=0 → a=0 ∧ b=0 := by
  decide +kernel

/-- Any two linear forms in four variables over F_5 vanish simultaneously
at some vector with exactly two or three nonzero coordinates. -/
theorem common_middle_zero (L M : V →ₗ[K] K) :
    ∃ x : V, (supportCount x = 2 ∨ supportCount x = 3) ∧ L x = 0 ∧ M x = 0 := by
  let Q : QuadraticForm K V := linMulLin L L - (2 : K) • linMulLin M M
  obtain ⟨x,hx,hq⟩ := exists_middle_zero_form Q
  have he : L x * L x - 2*(M x*M x) = 0 := by simpa [Q] using hq
  exact ⟨x,hx,anisotropic_binary _ _ he⟩

end Erdos322Research.QuadraticFormMiddleZero
