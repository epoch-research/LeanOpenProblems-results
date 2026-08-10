import FormalConjectures.Util.ProblemImports

open Nat Finset Matrix
open scoped BigOperators

lemma sign_revPerm (n : ℕ) : (Fin.revPerm (n:=n)).sign = (-1 : ℤˣ) ^ (n * (n-1) / 2) := by
  sorry

lemma det_antidiagonal_const {R : Type*} [CommRing R] (n : ℕ) [NeZero n] (M : Matrix (Fin n) (Fin n) R)
    (hzero : ∀ i j : Fin n, j < i → M i (Fin.rev j) = 0)
    (hdiag : ∀ i : Fin n, M i (Fin.rev i) = M 0 (Fin.rev 0)) :
    M.det = ((Fin.revPerm (n:=n)).sign : R) * (M 0 (Fin.rev 0)) ^ n := by
  let B : Matrix (Fin n) (Fin n) R := M.submatrix id (Fin.revPerm (n:=n))
  have htri : B.BlockTriangular id := by
    intro i j hij
    exact hzero i j hij
  have hdetB : B.det = (M 0 (Fin.rev 0)) ^ n := by
    rw [Matrix.det_of_upperTriangular htri]
    simp [B, hdiag, Finset.prod_const, Fintype.card_fin]
  have hperm : B.det = ((Fin.revPerm (n:=n)).sign : R) * M.det := by
    simpa [B] using (Matrix.det_permute' (Fin.revPerm (n:=n)) M)
  have hsignsq : (((Fin.revPerm (n:=n)).sign : R) * ((Fin.revPerm (n:=n)).sign : R)) = 1 := by
    rw [← Int.cast_mul]
    change (((((Fin.revPerm (n:=n)).sign * (Fin.revPerm (n:=n)).sign : ℤˣ) : ℤ) : R) = 1)
    simp
  calc
    M.det = (((Fin.revPerm (n:=n)).sign : R) * ((Fin.revPerm (n:=n)).sign : R)) * M.det := by rw [hsignsq, one_mul]
    _ = ((Fin.revPerm (n:=n)).sign : R) * B.det := by rw [hperm, mul_assoc]
    _ = ((Fin.revPerm (n:=n)).sign : R) * (M 0 (Fin.rev 0)) ^ n := by rw [hdetB]
