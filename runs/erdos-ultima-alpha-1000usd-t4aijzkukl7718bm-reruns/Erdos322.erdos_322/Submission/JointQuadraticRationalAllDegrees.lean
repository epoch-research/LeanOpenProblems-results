import Submission.JointQuadraticFiberRigidity
import Submission.JointQuadraticRationalInterpolation

/-! The all-degree mixed-parity obstruction with hypotheses only at
rational inputs. Arbitrary rational polynomial outputs are allowed. -/
namespace Erdos322Research.JointQuadraticRationalInterpolation
noncomputable section
open MvPolynomial Finset
open JointQuadraticCone (K)
set_option Elab.async false
set_option maxHeartbeats 0

private def allDegreeLabels : Fin 2 → MvPolynomial (Fin 5) ℚ :=
  ![∑ j, X j^2,∑ j, C (rationalWeights j)*X j^2]

private lemma allDegreeLabels_eval (x : Fin 5 → ℚ) :
    (fun j ↦ eval x (allDegreeLabels j)) = ![rationalLabel₁ x,rationalLabel₂ x] := by
  funext j
  fin_cases j <;> simp [allDegreeLabels,rationalLabel₁,rationalLabel₂]

private lemma allDegreeLabels_map :
    (MvPolynomial.map (Rat.castHom K) ∘ allDegreeLabels) =
      ![JointQuadraticCone.pencil₁,JointQuadraticCone.pencil₂] := by
  funext j
  fin_cases j
  · simp [allDegreeLabels,JointQuadraticCone.pencil₁]
  · change MvPolynomial.map (Rat.castHom K) (∑ j, C (rationalWeights j)*X j^2) =
      JointQuadraticCone.pencil₂
    simp only [map_sum,map_mul,map_pow,map_C,map_X,JointQuadraticCone.pencil₂]
    apply sum_congr rfl
    intro j _
    congr 2
    fin_cases j <;> norm_num [rationalWeights,JointQuadraticGaussianInterpolation.weights]

private lemma allDegree_cast_labels (x : Fin 5 → ℚ) :
    JointQuadraticGaussianInterpolation.label₁ (fun j ↦ (x j : K)) = (rationalLabel₁ x : K) ∧
    JointQuadraticGaussianInterpolation.label₂ (fun j ↦ (x j : K)) = (rationalLabel₂ x : K) := by
  constructor
  · simp [JointQuadraticGaussianInterpolation.label₁,rationalLabel₁]
  · simp only [JointQuadraticGaussianInterpolation.label₂,rationalLabel₂,Rat.cast_sum,Rat.cast_mul,Rat.cast_pow]
    apply sum_congr rfl
    intro j _
    congr 1
    fin_cases j <;> norm_num [rationalWeights,JointQuadraticGaussianInterpolation.weights]

private lemma allDegree_cast_eval (p : MvPolynomial (Fin 5) ℚ) (x : Fin 5 → ℚ) :
    eval (fun j ↦ (x j : K)) (MvPolynomial.map (Rat.castHom K) p) = (eval x p : K) := by
  rw [eval_map]
  exact (eval₂_comp (Rat.castHom K) x p).symm

/-- Arbitrary-degree rational polynomial identities extend to Gaussian
inputs before the all-degree fiber-algebra obstruction is applied. -/
theorem rational_polynomial_outputs_constant (P : Fin 4 → MvPolynomial (Fin 5) ℚ)
    (H : MvPolynomial (Fin 2) ℚ)
    (h : ∀ x : Fin 5 → ℚ, (∑ i, eval x (P i)^4) =
      eval ![rationalLabel₁ x,rationalLabel₂ x] H)
    (x y : Fin 5 → ℚ) (hx : rationalLabel₁ x = rationalLabel₁ y)
    (hy : rationalLabel₂ x = rationalLabel₂ y) :
    ∀ i, eval x (P i) = eval y (P i) := by
  have hp : (∑ i, P i^4) = eval₂ C allDegreeLabels H := by
    apply MvPolynomial.funext
    intro z
    rw [eval_eval₂]
    have hc : (eval z).comp C = RingHom.id ℚ := by ext c; simp
    rw [hc]
    change eval z (∑ i, P i^4) = eval (fun j ↦ eval z (allDegreeLabels j)) H
    rw [allDegreeLabels_eval]
    simpa only [map_sum,map_pow] using h z
  have hg := congrArg (MvPolynomial.map (Rat.castHom K)) hp
  simp only [map_sum,map_pow,map_eval₂,allDegreeLabels_map] at hg
  have hc := JointQuadraticCone.polynomial_quartic_identity_constant_on_joint_fibers
    (fun i ↦ MvPolynomial.map (Rat.castHom K) (P i)) (MvPolynomial.map (Rat.castHom K) H) hg
    (fun j ↦ (x j : K)) (fun j ↦ (y j : K))
    (by rw [(allDegree_cast_labels x).1,(allDegree_cast_labels y).1,hx])
    (by rw [(allDegree_cast_labels x).2,(allDegree_cast_labels y).2,hy])
  intro i
  have hi := hc i
  rw [allDegree_cast_eval,allDegree_cast_eval] at hi
  exact_mod_cast hi

/-- Such a polynomial construction has at most one image tuple on each
joint fiber, even at arbitrary degree and with unrestricted mixed parity. -/
theorem rational_polynomial_fiber_image_card_le_one (P : Fin 4 → MvPolynomial (Fin 5) ℚ)
    (H : MvPolynomial (Fin 2) ℚ)
    (h : ∀ x : Fin 5 → ℚ, (∑ i, eval x (P i)^4) =
      eval ![rationalLabel₁ x,rationalLabel₂ x] H)
    (S : Finset (Fin 5 → ℚ)) (a b : ℚ)
    (hS : ∀ x ∈ S, rationalLabel₁ x = a ∧ rationalLabel₂ x = b) :
    (S.image (fun x i ↦ eval x (P i))).card ≤ 1 := by
  classical
  apply card_le_one.mpr
  intro u hu v hv
  obtain ⟨x,hx,rfl⟩ := mem_image.mp hu
  obtain ⟨y,hy,rfl⟩ := mem_image.mp hv
  funext i
  exact rational_polynomial_outputs_constant P H h x y
    ((hS x hx).1.trans (hS y hy).1.symm)
    ((hS x hx).2.trans (hS y hy).2.symm) i

end
end Erdos322Research.JointQuadraticRationalInterpolation
