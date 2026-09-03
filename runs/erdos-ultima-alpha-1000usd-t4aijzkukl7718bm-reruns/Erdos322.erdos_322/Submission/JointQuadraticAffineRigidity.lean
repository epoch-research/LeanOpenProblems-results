import Submission.JointQuadraticGaussianInterpolation
import Submission.QuarticFormalSpecialization

/-! For the explicit five-variable pencil, quartic norm identities force
all affine-quadratic outputs to be constants plus members of the pencil. -/
namespace Erdos322Research.JointQuadraticGaussianInterpolation

noncomputable section
open Finset Polynomial
set_option Elab.async false
set_option maxHeartbeats 0

lemma labels_smul (t : K) (x : V) :
    label₁ (t • x) = t ^ 2 * label₁ x ∧
    label₂ (t • x) = t ^ 2 * label₂ x := by
  constructor
  · simp [label₁,mul_pow,mul_sum]
  · simp only [label₂,Pi.smul_apply,smul_eq_mul,mul_pow,mul_sum]
    apply sum_congr rfl
    intro j _
    ring

def affineOutput (Q : QuadraticForm K V) (L : V →ₗ[K] K) (c : K) (x : V) : K :=
  Q x + L x + c

/-- On the common cone, the quadratic and linear parts both vanish. No
homogeneity assumption on the complete outputs or on the target is used. -/
theorem affine_identity_parts_vanish_on_cone
    (Q : Fin 4 → QuadraticForm K V) (L : Fin 4 → V →ₗ[K] K) (c : Fin 4 → K)
    (H : K → K → K)
    (h : ∀ x, ∑ i, affineOutput (Q i) (L i) (c i) x ^ 4 = H (label₁ x) (label₂ x))
    (x : V) (hx : label₁ x = 0) (hy : label₂ x = 0) :
    ∀ i, Q i x = 0 ∧ L i x = 0 := by
  let R (i : Fin 4) : Polynomial K := C (Q i x) * X ^ 2 + C (L i x) * X + C (c i)
  have hev (t : K) (i : Fin 4) :
      (R i).eval t = affineOutput (Q i) (L i) (c i) (t • x) := by
    simp only [R,eval_add,eval_mul,eval_C,eval_pow,eval_X,
      affineOutput,QuadraticMap.map_smul,map_smul,smul_eq_mul]
    ring
  have hn : (∑ i, R i ^ 4) = C (H 0 0) := by
    apply Polynomial.funext
    intro t
    simp only [eval_finset_sum,eval_pow,hev,eval_C]
    rw [h,(labels_smul t x).1,(labels_smul t x).2,hx,hy,mul_zero]
  have hc := QuarticFormalSpecialization.polynomial_constant_norm
    QuarticFormalSpecialization.gaussian_anisotropic R (H 0 0) hn
  intro i
  have h₂ := congrArg (fun P : Polynomial K ↦ P.coeff 2) (hc i)
  have h₁ := congrArg (fun P : Polynomial K ↦ P.coeff 1) (hc i)
  constructor
  · simpa [R] using h₂
  · simpa [R] using h₁

/-- Every polynomial output of degree at most two is a constant plus a
linear combination of the two labels. The identity is over Gaussian inputs. -/
theorem affine_quartic_identity_classification
    (Q : Fin 4 → QuadraticForm K V) (L : Fin 4 → V →ₗ[K] K) (c : Fin 4 → K)
    (H : K → K → K)
    (h : ∀ x, ∑ i, affineOutput (Q i) (L i) (c i) x ^ 4 = H (label₁ x) (label₂ x)) :
    (∀ i x, L i x = 0) ∧
    (∀ i, ∃ α β : K, ∀ x,
      affineOutput (Q i) (L i) (c i) x = c i + α * label₁ x + β * label₂ x) := by
  have hL : ∀ i x, L i x = 0 := by
    intro i
    apply cone_linear_zero
    intro x hx hy
    exact (affine_identity_parts_vanish_on_cone Q L c H h x hx hy i).2
  refine ⟨hL,?_⟩
  intro i
  obtain ⟨α,β,hQ⟩ := cone_quadratic_span (Q i)
    (fun x hx hy ↦ (affine_identity_parts_vanish_on_cone Q L c H h x hx hy i).1)
  refine ⟨α,β,?_⟩
  intro x
  rw [affineOutput,hL,hQ]
  ring

theorem affine_quartic_identity_constant_on_joint_fibers
    (Q : Fin 4 → QuadraticForm K V) (L : Fin 4 → V →ₗ[K] K) (c : Fin 4 → K)
    (H : K → K → K)
    (h : ∀ x, ∑ i, affineOutput (Q i) (L i) (c i) x ^ 4 = H (label₁ x) (label₂ x))
    (x y : V) (hx : label₁ x = label₁ y) (hy : label₂ x = label₂ y) :
    ∀ i, affineOutput (Q i) (L i) (c i) x = affineOutput (Q i) (L i) (c i) y := by
  intro i
  obtain ⟨α,β,hp⟩ := (affine_quartic_identity_classification Q L c H h).2 i
  rw [hp,hp,hx,hy]

end
end Erdos322Research.JointQuadraticGaussianInterpolation
