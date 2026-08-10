import FormalConjectures.Util.ProblemImports

open Matrix Nat Int Finset Equiv

namespace CBdev

/-- Cauchy–Binet "function form". -/
theorem cauchy_binet_f {m N : ℕ} {R : Type*} [CommRing R]
    (A : Matrix (Fin m) (Fin N) R) (B : Matrix (Fin N) (Fin m) R) :
    (A * B).det = ∑ f : Fin m → Fin N, (∏ i, A i (f i)) * (B.submatrix f id).det := by
  set D : (Fin m → R) [⋀^Fin m]→ₗ[R] R := Matrix.detRowAlternating with hD
  have hrows : (A * B) = (fun i => ∑ k : Fin N, A i k • B k) := by
    funext i j
    simp only [Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have key : (A * B).det = D.toMultilinearMap (fun i => ∑ k : Fin N, A i k • B k) := by
    rw [Matrix.det, ← hrows]; rfl
  rw [key, D.toMultilinearMap.map_sum]
  apply Finset.sum_congr rfl
  intro r _
  have hsmul : D.toMultilinearMap (fun i => A i (r i) • B (r i))
      = (∏ i, A i (r i)) • D.toMultilinearMap (fun i => B (r i)) :=
    D.toMultilinearMap.map_smul_univ (fun i => A i (r i)) (fun i => B (r i))
  have hdet : D.toMultilinearMap (fun i => B (r i)) = (B.submatrix r id).det := by
    rw [Matrix.det]; rfl
  rw [hsmul, hdet, smul_eq_mul]

end CBdev
