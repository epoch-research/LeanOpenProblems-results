import FormalConjecturesUtil
open Matrix
lemma dot_zero_of_cert (A : Matrix (Fin 9) (Fin 9) ℤ)
    (x v w : Fin 9 → ℤ) (a : ℤ) (ha : a ≠ 0)
    (hx : A *ᵥ x = 0) (hcert : a • v = w ᵥ* A) : v ⬝ᵥ x = 0 := by
  have he := congrArg (fun v : Fin 9 → ℤ => v ⬝ᵥ x) hcert
  change (a • v) ⬝ᵥ x = (w ᵥ* A) ⬝ᵥ x at he
  rw [smul_dotProduct, ← dotProduct_mulVec, hx, dotProduct_zero] at he
  exact (mul_eq_zero.mp he).resolve_left ha
#print axioms dot_zero_of_cert
