import FormalConjecturesUtil
import Submission.C8MixedSuzukiMatrices

/-! Diagonal normalization of an opposite Suzuki-type root element. -/
namespace Erdos713C8SuzukiNormalization
open Erdos713C8MixedSuzukiMatrices
variable {F : Type*} [Field F]
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

lemma diagonal_inverse (w : Fin 4 → F) (hw : ∀ i, w i ≠ 0) :
    Matrix.diagonal w * Matrix.diagonal (fun i => (w i)⁻¹) = 1 := by
  rw [Matrix.diagonal_mul_diagonal]
  convert (Matrix.diagonal_one : Matrix.diagonal (1 : Fin 4 → F) = 1) using 1
  congr 1
  funext i
  exact mul_inv_cancel₀ (hw i)

lemma inverse_diagonal (w : Fin 4 → F) (hw : ∀ i, w i ≠ 0) :
    Matrix.diagonal (fun i => (w i)⁻¹) * Matrix.diagonal w = 1 := by
  rw [Matrix.diagonal_mul_diagonal]
  convert (Matrix.diagonal_one : Matrix.diagonal (1 : Fin 4 → F) = 1) using 1
  congr 1
  funext i
  exact inv_mul_cancel₀ (hw i)

def conjugate (w : Fin 4 → F) (hw : ∀ i, w i ≠ 0) : Mat F →* Mat F where
  toFun A := Matrix.diagonal (fun i => (w i)⁻¹)*A*Matrix.diagonal w
  map_one' := by simp only [mul_one]; exact inverse_diagonal w hw
  map_mul' A B := by
    have h := diagonal_inverse w hw
    change _ = (Matrix.diagonal (fun i => (w i)⁻¹)*A*Matrix.diagonal w)*
      (Matrix.diagonal (fun i => (w i)⁻¹)*B*Matrix.diagonal w)
    calc
      _ = Matrix.diagonal (fun i => (w i)⁻¹)*A*
          (Matrix.diagonal w*Matrix.diagonal (fun i => (w i)⁻¹))*B*Matrix.diagonal w := by
        rw [h]; simp only [mul_one,mul_assoc]
      _ = _ := by simp only [mul_assoc]

lemma conjugate_apply (w : Fin 4 → F) (hw : ∀ i, w i ≠ 0)
    (A : Mat F) (i j : Fin 4) : conjugate w hw A i j=(w i)⁻¹*A i j*w j := by
  simp [conjugate,Matrix.diagonal_mul,Matrix.mul_diagonal]

lemma conjugate_injective (w : Fin 4 → F) (hw : ∀ i, w i ≠ 0) :
    Function.Injective (conjugate w hw) := by
  intro A B h
  ext i j
  have he := congrArg (fun C : Mat F => C i j) h
  simp only [conjugate_apply] at he
  exact mul_left_cancel₀ (inv_ne_zero (hw i)) (mul_right_cancel₀ (hw j) he)

def weights (σ : F →+* F) (c : F) : Fin 4 → F := ![c^2*σ c,c*σ c,c,1]

lemma weights_ne_zero (σ : F →+* F) (c : F) (hc : c ≠ 0) :
    ∀ i, weights σ c i ≠ 0 := by
  have hσc : σ c ≠ 0 := (map_ne_zero σ).mpr hc
  intro i
  fin_cases i <;> dsimp [weights]
  · exact mul_ne_zero (pow_ne_zero 2 hc) hσc
  · exact mul_ne_zero hc hσc
  · exact hc
  · exact one_ne_zero

def upper (σ : F →+* F) (c d : F) : Mat F :=
  !![1,c,d,c^2*σ c+c*d+σ d; 0,1,σ c,c*σ c+d; 0,0,1,c; 0,0,0,1]

lemma normalize_center (σ : F →+* F) (hσ : ∀ a, σ (σ a)=a^2)
    (c a : F) (hc : c ≠ 0) :
    conjugate (weights σ c) (weights_ne_zero σ c hc) (X a (σ a)) =
      X (a*c*σ c) (σ (a*c*σ c)) := by
  have hσc : σ c ≠ 0 := (map_ne_zero σ).mpr hc
  ext i j
  rw [conjugate_apply]
  fin_cases i <;> fin_cases j <;>
    simp [weights,X,map_mul,hσ] <;> field_simp

lemma normalize_upper (σ : F →+* F) (hσ : ∀ a, σ (σ a)=a^2)
    (c d : F) (hc : c ≠ 0) :
    conjugate (weights σ c) (weights_ne_zero σ c hc) (upper σ c d) =
      Y (d/(c*σ c)) (1+d/(c*σ c)+σ (d/(c*σ c))) := by
  have hσc : σ c ≠ 0 := (map_ne_zero σ).mpr hc
  ext i j
  rw [conjugate_apply]
  fin_cases i <;> fin_cases j <;>
    simp [weights,upper,Y,map_div₀,map_mul,hσ] <;> field_simp

end Erdos713C8SuzukiNormalization
