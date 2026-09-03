import Submission.PfaffianSix

/-! The normalized eight-dimensional determinant/Pfaffian identity, reduced
by a two-dimensional Schur complement. No geometric rank bound is asserted. -/
namespace Erdos213.NormalizedPfaffian
open Matrix
set_option maxHeartbeats 0
set_option maxRecDepth 200000
variable {R : Type*} [CommRing R]

private def blockEquiv : Fin 2 ⊕ Fin 6 ≃ Fin 8 where
  toFun := Sum.elim ![0,7] ![1,2,3,4,5,6]
  invFun := ![Sum.inl 0,Sum.inr 0,Sum.inr 1,Sum.inr 2,Sum.inr 3,
    Sum.inr 4,Sum.inr 5,Sum.inl 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def J : Matrix (Fin 2) (Fin 2) R := !![0,1;-1,0]
private def Jinv : Matrix (Fin 2) (Fin 2) R := !![0,-1;1,0]
private def top (a : Fin 21 → R) : Matrix (Fin 2) (Fin 6) R :=
  !![a 0,a 1,a 2,a 3,a 4,a 5;-1,-1,-1,-1,-1,-1]

private lemma block_identity (a : Fin 21 → R) :
    (normal8 a).submatrix blockEquiv blockEquiv=
      fromBlocks J (top a) (-(top a)ᵀ) (alt6 (inner a)) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  all_goals fin_cases i <;> fin_cases j <;>
    simp [normal8,blockEquiv,J,top,alt6,inner]

/-- Normalizing one row and column reduces the determinant by two dimensions. -/
theorem det_normal8 (a : Fin 21 → R) :
    (normal8 a).det=(alt6 (shifted a)).det := by
  letI : Invertible (J : Matrix (Fin 2) (Fin 2) R) := {
    invOf := Jinv
    invOf_mul_self := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [J,Jinv,Matrix.mul_apply,Fin.sum_univ_two]
    mul_invOf_self := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [J,Jinv,Matrix.mul_apply,Fin.sum_univ_two] }
  rw [← Matrix.det_submatrix_equiv_self blockEquiv (normal8 a),block_identity,
    Matrix.det_fromBlocks₁₁]
  have hJ : (J : Matrix (Fin 2) (Fin 2) R).det=1 := by
    simp [J,Matrix.det_fin_two]
  have hI : ⅟(J : Matrix (Fin 2) (Fin 2) R)=(Jinv : Matrix (Fin 2) (Fin 2) R) := rfl
  rw [hJ,one_mul,hI]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [Matrix.mul_apply,Fin.sum_univ_two,alt6,inner,shifted,top,Jinv]
  all_goals ring

lemma pfaffian_normal8 (a : Fin 21 → R) :
    SignedRankSix.pf8 (normal8 a)=pf6 (alt6 (shifted a)) := by
  simp only [SignedRankSix.pf8,SignedRankSix.pf6,pf6,normal8,alt6,shifted,
    Matrix.of_apply,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_one]
  ring

/-- The square of the eight-by-eight normalized Pfaffian is the determinant. -/
theorem det_eq_pfaffian_sq (a : Fin 21 → R) :
    (normal8 a).det=SignedRankSix.pf8 (normal8 a)^2 := by
  rw [det_normal8,det_alt6,pfaffian_normal8]

/-- The six-dimensional identity for an arbitrary rational alternating matrix. -/
theorem det_pf6_of_alternating (M : Matrix (Fin 6) (Fin 6) ℚ)
    (ha : ∀ i j, M i j= -M j i) : M.det=pf6 M^2 := by
  have hd : ∀ i, M i i=0 := by
    intro i
    linarith [ha i i]
  let a : Fin 15 → ℚ :=
    ![M 0 1,M 0 2,M 0 3,M 0 4,M 0 5,M 1 2,M 1 3,M 1 4,M 1 5,
      M 2 3,M 2 4,M 2 5,M 3 4,M 3 5,M 4 5]
  have he : M=alt6 a := by
    ext i j
    fin_cases i <;> fin_cases j
    all_goals dsimp only [alt6,a,Matrix.of_apply,Matrix.cons_val,
      Matrix.cons_val_zero,Matrix.cons_val_one]
    all_goals first | rfl | exact hd _ | exact ha _ _
  rw [he,det_alt6]

/-- An arbitrary normalized rational alternating eight-by-eight matrix
satisfies the determinant/Pfaffian identity. -/
theorem det_pf8_of_normalized (M : Matrix (Fin 8) (Fin 8) ℚ)
    (ha : ∀ i j, M i j= -M j i)
    (hn : ∀ i : Fin 7, M i.castSucc 7=1) :
    M.det=SignedRankSix.pf8 M^2 := by
  have hd : ∀ i, M i i=0 := by
    intro i
    linarith [ha i i]
  have hb : ∀ i : Fin 7, M 7 i.castSucc= -1 := by
    intro i
    rw [ha,hn]
  let a : Fin 21 → ℚ :=
    ![M 0 1,M 0 2,M 0 3,M 0 4,M 0 5,M 0 6,M 1 2,M 1 3,M 1 4,
      M 1 5,M 1 6,M 2 3,M 2 4,M 2 5,M 2 6,M 3 4,M 3 5,M 3 6,
      M 4 5,M 4 6,M 5 6]
  have he : M=normal8 a := by
    ext i j
    fin_cases i <;> fin_cases j
    all_goals dsimp only [normal8,a,Matrix.of_apply,Matrix.cons_val,
      Matrix.cons_val_zero,Matrix.cons_val_one]
    · exact hd 0
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact hn 0
    · exact ha 1 0
    · exact hd 1
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact hn 1
    · exact ha 2 0
    · exact ha 2 1
    · exact hd 2
    · rfl
    · rfl
    · rfl
    · rfl
    · exact hn 2
    · exact ha 3 0
    · exact ha 3 1
    · exact ha 3 2
    · exact hd 3
    · rfl
    · rfl
    · rfl
    · exact hn 3
    · exact ha 4 0
    · exact ha 4 1
    · exact ha 4 2
    · exact ha 4 3
    · exact hd 4
    · rfl
    · rfl
    · exact hn 4
    · exact ha 5 0
    · exact ha 5 1
    · exact ha 5 2
    · exact ha 5 3
    · exact ha 5 4
    · exact hd 5
    · rfl
    · exact hn 5
    · exact ha 6 0
    · exact ha 6 1
    · exact ha 6 2
    · exact ha 6 3
    · exact ha 6 4
    · exact ha 6 5
    · exact hd 6
    · exact hn 6
    · exact hb 0
    · exact hb 1
    · exact hb 2
    · exact hb 3
    · exact hb 4
    · exact hb 5
    · exact hb 6
    · exact hd 7
  rw [he,det_eq_pfaffian_sq]

#print axioms det_pf6_of_alternating
#print axioms det_pf8_of_normalized

#print axioms det_alt6
#print axioms det_normal8
#print axioms det_eq_pfaffian_sq
end Erdos213.NormalizedPfaffian
