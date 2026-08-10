import FormalConjectures.Util.ProblemImports
open BigOperators Matrix Nat
set_option maxHeartbeats 0

noncomputable def rowOp (N : ℕ) : Matrix (Fin (N+1)) (Fin (N+1)) ℤ :=
  Matrix.of fun i k => if k = i then (1:ℤ) else if (0 < i.val ∧ k.val + 1 = i.val) then 1 else 0

lemma rowOp_lower (N : ℕ) : (rowOp N).BlockTriangular OrderDual.toDual := by
  intro i j hij
  simp [rowOp]
  -- need show j=i false and condition false when ?
  sorry

lemma det_rowOp (N : ℕ) : (rowOp N).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · simp [rowOp]
  · exact rowOp_lower N

lemma rowOp_mul_apply {N : ℕ} (M : Matrix (Fin (N+1)) (Fin (N+1)) ℤ) (i j : Fin (N+1)) :
    (rowOp N * M) i j = if hi : i.val = 0 then M i j else M i j + M ⟨i.val-1, by omega⟩ j := by
  rw [Matrix.mul_apply]
  by_cases hi0 : i.val = 0
  · simp [rowOp, hi0]
    -- sum only k=i?
    sorry
  · sorry
