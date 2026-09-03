import Submission.JointQuadraticAffineRigidity

/-! Rational-input polynomial identities for the explicit generic pencil.
This is a construction obstruction, not a full representation-count bound. -/
namespace Erdos322Research.JointQuadraticRationalInterpolation

noncomputable section
open Finset MvPolynomial
open JointQuadraticGaussianInterpolation
set_option Elab.async false
set_option maxHeartbeats 0

abbrev Coefficients := Matrix (Fin 5) (Fin 5) ℚ

def quadraticEval (A : Coefficients) (x : Fin 5 → ℚ) : ℚ :=
  ∑ i, ∑ j, A i j * x i * x j

def rationalWeights : Fin 5 → ℚ := ![1,17,26,2,3]
def rationalLabel₁ (x : Fin 5 → ℚ) : ℚ := ∑ i, x i ^ 2
def rationalLabel₂ (x : Fin 5 → ℚ) : ℚ := ∑ i, rationalWeights i * x i ^ 2

private def quadraticPolynomial (A : Coefficients) : MvPolynomial (Fin 5) ℚ :=
  ∑ i, ∑ j, C (A i j) * X i * X j

private def labelPolynomials : Fin 2 → MvPolynomial (Fin 5) ℚ :=
  ![∑ i, X i ^ 2, ∑ i, C (rationalWeights i) * X i ^ 2]

private lemma quadraticPolynomial_eval (A : Coefficients) (x : Fin 5 → ℚ) :
    eval x (quadraticPolynomial A) = quadraticEval A x := by
  simp [quadraticPolynomial,quadraticEval]

private lemma labels_eval (x : Fin 5 → ℚ) :
    (fun j ↦ eval x (labelPolynomials j)) = ![rationalLabel₁ x,rationalLabel₂ x] := by
  funext j
  fin_cases j <;> simp [labelPolynomials,rationalLabel₁,rationalLabel₂]

private lemma eval_substitution {R : Type*} [CommRing R] (f : ℚ →+* R)
    (x : Fin 5 → R) (H : MvPolynomial (Fin 2) ℚ) :
    eval₂Hom f x (eval₂Hom C labelPolynomials H) =
      eval₂Hom f (fun j ↦ eval₂Hom f x (labelPolynomials j)) H := by
  rw [map_eval₂Hom]
  have hc : (eval₂Hom f x).comp C = f := by
    ext r
    simp
  rw [hc]

private def gaussianForm (A : Coefficients) : QuadraticForm K V :=
  Matrix.toQuadraticMap' (fun i j ↦ (A i j : K))

private lemma gaussianForm_eval (A : Coefficients) (x : V) :
    eval₂Hom (Rat.castHom K) x (quadraticPolynomial A) = gaussianForm A x := by
  simp only [quadraticPolynomial,map_sum,map_mul,eval₂Hom_C,eval₂Hom_X']
  simp only [gaussianForm,Matrix.toQuadraticMap',LinearMap.BilinMap.toQuadraticMap_apply,
    Matrix.toLinearMap₂'_apply]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  simp only [smul_eq_mul]
  change (A i j : K) * x i * x j = _
  ring

private lemma gaussian_labels_eval (x : V) :
    (fun j ↦ eval₂Hom (Rat.castHom K) x (labelPolynomials j)) = ![label₁ x,label₂ x] := by
  funext j
  fin_cases j
  · simp [labelPolynomials,label₁]
  · change eval₂Hom (Rat.castHom K) x (∑ i, C (rationalWeights i) * X i ^ 2) = label₂ x
    simp only [map_sum,map_mul,map_pow,eval₂Hom_C,eval₂Hom_X',label₂]
    apply sum_congr rfl
    intro i _
    congr 1
    fin_cases i <;> norm_num [rationalWeights,weights]

private lemma gaussianForm_rational (A : Coefficients) (x : Fin 5 → ℚ) :
    gaussianForm A (fun j ↦ (x j : K)) = (quadraticEval A x : K) := by
  rw [←gaussianForm_eval,←quadraticPolynomial_eval]
  simpa only [RingHom.comp_id] using
    (map_eval₂Hom (RingHom.id ℚ) x (Rat.castHom K) (quadraticPolynomial A)).symm

private lemma cast_labels (x : Fin 5 → ℚ) :
    label₁ (fun j ↦ (x j : K)) = (rationalLabel₁ x : K) ∧
    label₂ (fun j ↦ (x j : K)) = (rationalLabel₂ x : K) := by
  constructor
  · simp [label₁,rationalLabel₁]
  · simp only [label₂,rationalLabel₂,Rat.cast_sum,Rat.cast_mul,Rat.cast_pow]
    apply sum_congr rfl
    intro i _
    congr 1
    fin_cases i <;> norm_num [rationalWeights,weights]

/-- Mixed-parity homogeneous quadratic outputs are constant on the rational
joint fibers if their fourth-power sum is a polynomial in these two labels.
The hypothesis is only on rational inputs; polynomial identity extension is
proved explicitly before the Gaussian cone obstruction is used. -/
theorem rational_quadratic_outputs_constant (A : Fin 4 → Coefficients)
    (H : MvPolynomial (Fin 2) ℚ)
    (h : ∀ x : Fin 5 → ℚ, ∑ i, quadraticEval (A i) x ^ 4 =
      eval ![rationalLabel₁ x,rationalLabel₂ x] H)
    (x y : Fin 5 → ℚ) (hx : rationalLabel₁ x = rationalLabel₁ y)
    (hy : rationalLabel₂ x = rationalLabel₂ y) :
    ∀ i, quadraticEval (A i) x = quadraticEval (A i) y := by
  have hp : (∑ i, quadraticPolynomial (A i) ^ 4) = eval₂Hom C labelPolynomials H := by
    apply MvPolynomial.funext
    intro z
    rw [show eval z (eval₂Hom C labelPolynomials H) =
      eval₂Hom (RingHom.id ℚ) z (eval₂Hom C labelPolynomials H) from rfl,
      eval_substitution]
    change eval z (∑ i, quadraticPolynomial (A i) ^ 4) =
      eval (fun j ↦ eval z (labelPolynomials j)) H
    simp only [map_sum,map_pow,quadraticPolynomial_eval,labels_eval]
    exact h z
  let G : K → K → K := fun a b ↦ eval₂Hom (Rat.castHom K) ![a,b] H
  have hg : ∀ z : V, ∑ i, gaussianForm (A i) z ^ 4 = G (label₁ z) (label₂ z) := by
    intro z
    have hh := congrArg (eval₂Hom (Rat.castHom K) z) hp
    simpa only [map_sum,map_pow,gaussianForm_eval,eval_substitution,gaussian_labels_eval,G]
      using hh
  have hG : G 0 0 = 0 := by
    have hh := hg 0
    simpa [label₁,label₂] using hh.symm
  have hh := quartic_identity_constant_on_joint_fibers
    (fun i ↦ gaussianForm (A i)) G hG hg
    (fun j ↦ (x j : K)) (fun j ↦ (y j : K))
    (by rw [(cast_labels x).1,(cast_labels y).1,hx])
    (by rw [(cast_labels x).2,(cast_labels y).2,hy])
  intro i
  have hi := hh i
  rw [gaussianForm_rational,gaussianForm_rational] at hi
  exact_mod_cast hi

/-- In particular, these maps produce at most one output tuple on a fixed
joint fiber, whether or not their coordinates have fixed parity. -/
theorem rational_quadratic_fiber_image_card_le_one (A : Fin 4 → Coefficients)
    (H : MvPolynomial (Fin 2) ℚ)
    (h : ∀ x : Fin 5 → ℚ, ∑ i, quadraticEval (A i) x ^ 4 =
      eval ![rationalLabel₁ x,rationalLabel₂ x] H)
    (S : Finset (Fin 5 → ℚ)) (a b : ℚ)
    (hS : ∀ x ∈ S, rationalLabel₁ x = a ∧ rationalLabel₂ x = b) :
    (S.image (fun x i ↦ quadraticEval (A i) x)).card ≤ 1 := by
  classical
  apply card_le_one.mpr
  intro u hu v hv
  obtain ⟨x,hx,rfl⟩ := mem_image.mp hu
  obtain ⟨y,hy,rfl⟩ := mem_image.mp hv
  funext i
  exact rational_quadratic_outputs_constant A H h x y
    ((hS x hx).1.trans (hS y hy).1.symm)
    ((hS x hx).2.trans (hS y hy).2.symm) i

/-- The general rational polynomial of degree at most two, in matrix form. -/
def affineQuadraticEval (A : Coefficients) (b : Fin 5 → ℚ) (c : ℚ)
    (x : Fin 5 → ℚ) : ℚ := quadraticEval A x + (∑ j, b j * x j) + c

private def gaussianLinear (b : Fin 5 → ℚ) : V →ₗ[K] K where
  toFun x := ∑ j, (b j : K) * x j
  map_add' x y := by simp [mul_add,sum_add_distrib]
  map_smul' t x := by
    simp only [Pi.smul_apply,smul_eq_mul,mul_sum,RingHom.id_apply]
    apply sum_congr rfl
    intro j _
    ring

private def affinePolynomial (A : Coefficients) (b : Fin 5 → ℚ) (c : ℚ) :
    MvPolynomial (Fin 5) ℚ :=
  quadraticPolynomial A + (∑ j, C (b j) * X j) + C c

private lemma affinePolynomial_eval (A : Coefficients) (b : Fin 5 → ℚ) (c : ℚ)
    (x : Fin 5 → ℚ) : eval x (affinePolynomial A b c) = affineQuadraticEval A b c x := by
  simp [affinePolynomial,affineQuadraticEval,quadraticPolynomial_eval]

private lemma affinePolynomial_gaussian_eval (A : Coefficients) (b : Fin 5 → ℚ) (c : ℚ)
    (x : V) : eval₂Hom (Rat.castHom K) x (affinePolynomial A b c) =
      affineOutput (gaussianForm A) (gaussianLinear b) (c : K) x := by
  simp only [affinePolynomial,map_add,gaussianForm_eval]
  simp [affineOutput,gaussianLinear]

private lemma gaussianAffine_rational (A : Coefficients) (b : Fin 5 → ℚ) (c : ℚ)
    (x : Fin 5 → ℚ) :
    affineOutput (gaussianForm A) (gaussianLinear b) (c : K) (fun j ↦ (x j : K)) =
      (affineQuadraticEval A b c x : K) := by
  simp [affineOutput,gaussianLinear,affineQuadraticEval,gaussianForm_rational]

private lemma affine_identity_extension (A : Fin 4 → Coefficients)
    (b : Fin 4 → Fin 5 → ℚ) (c : Fin 4 → ℚ) (H : MvPolynomial (Fin 2) ℚ)
    (h : ∀ x : Fin 5 → ℚ, ∑ i, affineQuadraticEval (A i) (b i) (c i) x ^ 4 =
      eval ![rationalLabel₁ x,rationalLabel₂ x] H) :
    ∀ z : V, ∑ i, affineOutput (gaussianForm (A i)) (gaussianLinear (b i)) (c i : K) z ^ 4 =
      eval₂Hom (Rat.castHom K) ![label₁ z,label₂ z] H := by
  have hp : (∑ i, affinePolynomial (A i) (b i) (c i) ^ 4) =
      eval₂Hom C labelPolynomials H := by
    apply MvPolynomial.funext
    intro z
    rw [show eval z (eval₂Hom C labelPolynomials H) =
      eval₂Hom (RingHom.id ℚ) z (eval₂Hom C labelPolynomials H) from rfl,
      eval_substitution]
    change eval z (∑ i, affinePolynomial (A i) (b i) (c i) ^ 4) =
      eval (fun j ↦ eval z (labelPolynomials j)) H
    simp only [map_sum,map_pow,affinePolynomial_eval,labels_eval]
    exact h z
  intro z
  have hh := congrArg (eval₂Hom (Rat.castHom K) z) hp
  simpa only [map_sum,map_pow,affinePolynomial_gaussian_eval,
    eval_substitution,gaussian_labels_eval] using hh

/-- The homogeneous restriction is unnecessary: all rational outputs of
degree at most two are constant on the joint fibers of this pencil. -/
theorem rational_affine_quadratic_outputs_constant (A : Fin 4 → Coefficients)
    (b : Fin 4 → Fin 5 → ℚ) (c : Fin 4 → ℚ) (H : MvPolynomial (Fin 2) ℚ)
    (h : ∀ x : Fin 5 → ℚ, ∑ i, affineQuadraticEval (A i) (b i) (c i) x ^ 4 =
      eval ![rationalLabel₁ x,rationalLabel₂ x] H)
    (x y : Fin 5 → ℚ) (hx : rationalLabel₁ x = rationalLabel₁ y)
    (hy : rationalLabel₂ x = rationalLabel₂ y) :
    ∀ i, affineQuadraticEval (A i) (b i) (c i) x = affineQuadraticEval (A i) (b i) (c i) y := by
  have hh := affine_quartic_identity_constant_on_joint_fibers
    (fun i ↦ gaussianForm (A i)) (fun i ↦ gaussianLinear (b i)) (fun i ↦ (c i : K))
    (fun u v ↦ eval₂Hom (Rat.castHom K) ![u,v] H) (affine_identity_extension A b c H h)
    (fun j ↦ (x j : K)) (fun j ↦ (y j : K))
    (by rw [(cast_labels x).1,(cast_labels y).1,hx])
    (by rw [(cast_labels x).2,(cast_labels y).2,hy])
  intro i
  have hi := hh i
  rw [gaussianAffine_rational,gaussianAffine_rational] at hi
  exact_mod_cast hi

/-- Every linear coefficient is zero in such a rational identity. -/
theorem rational_affine_quadratic_linear_coefficients_zero (A : Fin 4 → Coefficients)
    (b : Fin 4 → Fin 5 → ℚ) (c : Fin 4 → ℚ) (H : MvPolynomial (Fin 2) ℚ)
    (h : ∀ x : Fin 5 → ℚ, ∑ i, affineQuadraticEval (A i) (b i) (c i) x ^ 4 =
      eval ![rationalLabel₁ x,rationalLabel₂ x] H) : ∀ i j, b i j = 0 := by
  have hh := (affine_quartic_identity_classification
    (fun i ↦ gaussianForm (A i)) (fun i ↦ gaussianLinear (b i)) (fun i ↦ (c i : K))
    (fun u v ↦ eval₂Hom (Rat.castHom K) ![u,v] H)
    (affine_identity_extension A b c H h)).1
  intro i j
  have he := hh i (Pi.single j 1)
  simpa [gaussianLinear,Pi.single_apply] using he

theorem rational_affine_quadratic_fiber_image_card_le_one (A : Fin 4 → Coefficients)
    (b : Fin 4 → Fin 5 → ℚ) (c : Fin 4 → ℚ) (H : MvPolynomial (Fin 2) ℚ)
    (h : ∀ x : Fin 5 → ℚ, ∑ i, affineQuadraticEval (A i) (b i) (c i) x ^ 4 =
      eval ![rationalLabel₁ x,rationalLabel₂ x] H)
    (S : Finset (Fin 5 → ℚ)) (u v : ℚ)
    (hS : ∀ x ∈ S, rationalLabel₁ x = u ∧ rationalLabel₂ x = v) :
    (S.image (fun x i ↦ affineQuadraticEval (A i) (b i) (c i) x)).card ≤ 1 := by
  classical
  apply card_le_one.mpr
  intro a ha d hd
  obtain ⟨x,hx,rfl⟩ := mem_image.mp ha
  obtain ⟨y,hy,rfl⟩ := mem_image.mp hd
  funext i
  exact rational_affine_quadratic_outputs_constant A b c H h x y
    ((hS x hx).1.trans (hS y hy).1.symm)
    ((hS x hx).2.trans (hS y hy).2.symm) i

end
end Erdos322Research.JointQuadraticRationalInterpolation
