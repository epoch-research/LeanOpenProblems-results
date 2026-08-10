import FormalConjectures.Util.ProblemImports
open BigOperators Matrix Nat
set_option maxHeartbeats 0

lemma prod_fin_pos_const (N : ℕ) (d : ℤ) :
    (∏ i : Fin (N+1), (if 0 < i.val then d else 1)) = d ^ N := by
  induction N with
  | zero =>
    simp
  | succ N ih =>
    rw [Fin.prod_univ_castSucc]
    have hprod : (∏ i : Fin (N+1), (if 0 < i.castSucc.val then d else 1)) = d ^ N := by
      simpa using ih
    rw [hprod]
    simp [Fin.val_last, pow_succ]

lemma det_dvd_of_rows_dvd {N : ℕ} (M : Matrix (Fin (N+1)) (Fin (N+1)) ℤ) (d : ℤ) (hd : d ≠ 0)
    (h : ∀ i : Fin (N+1), 0 < i.val → ∀ j, d ∣ M i j) :
    d ^ N ∣ M.det := by
  let Q : Matrix (Fin (N+1)) (Fin (N+1)) ℤ :=
    Matrix.of fun i j => if hi : 0 < i.val then M i j / d else M i j
  let v : Fin (N+1) → ℤ := fun i => if 0 < i.val then d else 1
  have hM : M = Matrix.of fun i j => v i * Q i j := by
    ext i j
    dsimp [v, Q]
    by_cases hi : 0 < i.val
    · simp [hi]
      obtain ⟨z, hz⟩ := h i hi j
      rw [hz]
      rw [Int.mul_ediv_cancel_left _ hd]
    · simp [hi]
  rw [hM, Matrix.det_mul_column, prod_fin_pos_const]
  exact dvd_mul_right (d ^ N) Q.det
