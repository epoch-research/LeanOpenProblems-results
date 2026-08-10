import FormalConjectures.Util.ProblemImports
open BigOperators Matrix Nat
set_option maxHeartbeats 0

-- reuse definitions from scratch by copying minimal rowOp and determinant-divisibility lemmas
noncomputable def rowOp (N : ℕ) : Matrix (Fin (N+1)) (Fin (N+1)) ℤ :=
  Matrix.of fun i k => if k = i then (1:ℤ) else if (0 < i.val ∧ k.val + 1 = i.val) then 1 else 0

lemma rowOp_lower (N : ℕ) : (rowOp N).BlockTriangular OrderDual.toDual := by
  intro i j hij
  have hlt : i < j := by simpa using hij
  have hne : ¬ j = i := by exact ne_of_gt hlt
  simp only [rowOp, Matrix.of_apply, if_neg hne]
  by_cases hpos : 0 < i.val
  · rw [if_neg]
    intro hk
    have hv : i.val < j.val := by exact hlt
    omega
  · rw [if_neg]
    intro h
    exact hpos h.1

lemma det_rowOp (N : ℕ) : (rowOp N).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · simp [rowOp]
  · exact rowOp_lower N

lemma rowOp_mul_apply_pos {N : ℕ} (M : Matrix (Fin (N+1)) (Fin (N+1)) ℤ)
    {i : Fin (N+1)} (hi : 0 < i.val) (j : Fin (N+1)) :
    (rowOp N * M) i j = M i j + M ⟨i.val - 1, by omega⟩ j := by
  rw [Matrix.mul_apply]
  let p : Fin (N+1) := ⟨i.val - 1, by omega⟩
  have hp_ne : p ≠ i := by
    intro h
    have : p.val = i.val := congrArg Fin.val h
    dsimp [p] at this
    omega
  rw [Finset.sum_eq_add_sum_diff_singleton (Finset.mem_univ i)]
  rw [show rowOp N i i = 1 by simp [rowOp]]
  simp only [one_mul]
  rw [Finset.sum_eq_single p]
  · have hpval : rowOp N i p = 1 := by
      have hne : ¬ p = i := hp_ne
      have hp : 0 < i.val ∧ p.val + 1 = i.val := by
        constructor
        · exact hi
        · dsimp [p]; omega
      change (if p = i then (1 : ℤ) else if (0 < i.val ∧ p.val + 1 = i.val) then 1 else 0) = 1
      rw [if_neg hne, if_pos hp]
    rw [hpval]
    ring
  · intro k hk hkp
    have hki : k ≠ i := by simpa using hk
    have hpred : ¬ (0 < i.val ∧ k.val + 1 = i.val) := by
      intro h
      have kval : k.val = p.val := by dsimp [p]; omega
      apply hkp
      exact Fin.ext kval
    have hz : rowOp N i k = 0 := by
      simp only [rowOp, Matrix.of_apply]
      rw [if_neg hki]
      rw [if_neg hpred]
    rw [hz]
    simp
  · intro hpnot
    exfalso
    apply hpnot
    simp [p, hp_ne]

lemma prod_fin_pos_const (N : ℕ) (d : ℤ) :
    (∏ i : Fin (N+1), (if 0 < i.val then d else 1)) = d ^ N := by
  induction N with
  | zero => simp
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

lemma int_dvd_natAbs {c : ℕ} {z : ℤ} (h : (c : ℤ) ∣ z) : c ∣ z.natAbs := by
  obtain ⟨w, hw⟩ := h
  use w.natAbs
  rw [hw]
  simp [Int.natAbs_mul]

lemma dvd_det_natAbs_large (N : ℕ) (hN : 4 ≤ N) (B : ℕ → ℕ)
    (h6 : ∀ m, (6 : ℤ) ∣ (B (m+1) : ℤ) + (B m : ℤ)) :
    (16 * 3^N) ∣ (let M : Matrix (Fin (N+1)) (Fin (N+1)) ℤ := Matrix.of fun i j => (B (i.val+j.val) : ℤ); M.det.natAbs) := by
  let M : Matrix (Fin (N+1)) (Fin (N+1)) ℤ := Matrix.of fun i j => (B (i.val+j.val) : ℤ)
  let R := rowOp N * M
  have hrows : ∀ i : Fin (N+1), 0 < i.val → ∀ j, (6 : ℤ) ∣ R i j := by
    intro i hi j
    rw [show R i j = M i j + M ⟨i.val-1, by omega⟩ j by exact rowOp_mul_apply_pos M hi j]
    dsimp [M]
    change (6 : ℤ) ∣ (B (i.val + j.val) : ℤ) + (B (i.val - 1 + j.val) : ℤ)
    have hidx : i.val - 1 + j.val + 1 = i.val + j.val := by omega
    rw [← hidx]
    exact h6 (i.val - 1 + j.val)
  have hdetR : (6 : ℤ)^N ∣ R.det := det_dvd_of_rows_dvd R 6 (by norm_num) hrows
  have hdet_eq : R.det = M.det := by
    dsimp [R]
    rw [Matrix.det_mul, det_rowOp, one_mul]
  rw [hdet_eq] at hdetR
  have hmain_int : ((16 * 3^N : ℕ) : ℤ) ∣ M.det := by
    have hfactor : ((16 * 3^N : ℕ) : ℤ) ∣ (6 : ℤ)^N := by
      use (2:ℤ)^(N-4)
      norm_num [pow_succ]
      -- need arithmetic powers: 6^N = 16*3^N*2^(N-4) for N>=4
      have hpow : (6:ℤ)^N = (2:ℤ)^N * (3:ℤ)^N := by
        rw [show (6:ℤ) = 2*3 by norm_num, mul_pow]
      rw [hpow]
      norm_num
      have h2 : (2:ℤ)^N = 16 * (2:ℤ)^(N-4) := by
        rw [show N = 4 + (N-4) by omega]
        rw [pow_add]
        norm_num
      rw [h2]
      ring
    exact dvd_trans hfactor hdetR
  exact int_dvd_natAbs hmain_int
