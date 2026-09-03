import Submission.DicksonPermutation
import Submission.MatrixCubicRecovery

/-!
A conditional matrix recovery bound from the Dickson quintic. The elliptic
pencil identity and the reconstruction hypotheses are explicit; this file
does not claim that arbitrary graph neighborhoods satisfy them.
-/

open Matrix
namespace Erdos714DicksonRecovery
open Erdos714MatrixCubicRecovery Erdos714Dickson

variable {F : Type*} [Field F]

lemma determinant_quintic (A B H : Mat2 F) (hD : H.det ≠ 0)
    (hH : H = H.det^3 • A + H.det • B) :
    A.det*H.det^5 + mixed A B*H.det^3 + B.det*H.det = 1 := by
  have hp : H = H.det • (H.det^2 • A + B) := by
    calc
      H = H.det^3 • A + H.det • B := hH
      _ = H.det • (H.det^2 • A + B) := by
        rw [smul_add, smul_smul, ← pow_succ']
  have hd := congrArg Matrix.det hp
  rw [Matrix.det_smul, Fintype.card_fin, pencil_det] at hd
  apply mul_left_cancel₀ hD
  linear_combination -hd

lemma normalize_quintic (a b c D : F) (ha : a ≠ 0)
    (hc : a*c = -b^2) (hD : a*D^5+b*D^3+c*D = 1) :
    D^5+(b/a)*D^3-(b/a)^2*D = a⁻¹ := by
  field_simp
  linear_combination a*hD-D*hc

/-- Under the displayed coefficient identity the determinant is uniquely
recoverable, and the reconstruction formula then determines the whole matrix. -/
theorem reconstruction_unique [Fintype F] [CharP F 3]
    (hm : Fintype.card F % 5 = 2 ∨ Fintype.card F % 5 = 3)
    (A B H K : Mat2 F) (ha : A.det ≠ 0)
    (hc : A.det*B.det = -(mixed A B)^2)
    (hH0 : H.det ≠ 0) (hK0 : K.det ≠ 0)
    (hH : H = H.det^3 • A + H.det • B)
    (hK : K = K.det^3 • A + K.det • B) : H = K := by
  have heH := normalize_quintic A.det (mixed A B) B.det H.det ha hc
    (determinant_quintic A B H hH0 hH)
  have heK := normalize_quintic A.det (mixed A B) B.det K.det ha hc
    (determinant_quintic A B K hK0 hK)
  have he : H.det = K.det :=
    (sparse_quintic_bijective (mixed A B / A.det) hm).injective (heH.trans heK.symm)
  calc
    H = H.det^3 • A + H.det • B := hH
    _ = K.det^3 • A + K.det • B := by rw [he]
    _ = K := hK.symm

end Erdos714DicksonRecovery

#print axioms Erdos714DicksonRecovery.determinant_quintic
#print axioms Erdos714DicksonRecovery.reconstruction_unique
