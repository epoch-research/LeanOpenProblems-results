import FormalConjectures.Util.ProblemImports
open BigOperators Matrix Nat
set_option maxHeartbeats 0

noncomputable def rowOp (N : ℕ) : Matrix (Fin (N+1)) (Fin (N+1)) ℤ :=
  Matrix.of fun i k => if k = i then (1:ℤ) else if (0 < i.val ∧ k.val + 1 = i.val) then 1 else 0

lemma rowOp_lower (N : ℕ) : (rowOp N).BlockTriangular OrderDual.toDual := by
  intro i j hij
  have hlt : i < j := by simpa using hij
  have hne : ¬ j = i := by exact ne_of_gt hlt
  simp only [rowOp, Matrix.of_apply, if_neg hne]
  by_cases hpos : 0 < i.val
  · rw [if_neg]
    intro h
    have hv : i.val < j.val := by exact hlt
    omega
  · simp [hpos]

lemma det_rowOp (N : ℕ) : (rowOp N).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · simp [rowOp]
  · exact rowOp_lower N

lemma rowOp_apply_diag (N : ℕ) (i : Fin (N+1)) : rowOp N i i = 1 := by
  simp [rowOp]

lemma rowOp_apply_pred (N : ℕ) {i : Fin (N+1)} (hi : 0 < i.val) :
    rowOp N i ⟨i.val - 1, by omega⟩ = 1 := by
  let p : Fin (N+1) := ⟨i.val - 1, by omega⟩
  have hne : ¬ p = i := by
    intro h
    have hv : p.val = i.val := congrArg Fin.val h
    dsimp [p] at hv
    omega
  have hp : 0 < i.val ∧ p.val + 1 = i.val := by
    constructor
    · exact hi
    · dsimp [p]
      omega
  change (if p = i then (1 : ℤ) else if (0 < i.val ∧ p.val + 1 = i.val) then 1 else 0) = 1
  rw [if_neg hne, if_pos hp]

lemma rowOp_apply_other (N : ℕ) {i k : Fin (N+1)} (hne : k ≠ i)
    (hpred : ¬ (0 < i.val ∧ k.val + 1 = i.val)) : rowOp N i k = 0 := by
  simp only [rowOp, Matrix.of_apply, if_neg hne]
  rw [if_neg hpred]

lemma rowOp_mul_apply_zero {N : ℕ} (M : Matrix (Fin (N+1)) (Fin (N+1)) ℤ) (j : Fin (N+1)) :
    (rowOp N * M) 0 j = M 0 j := by
  rw [Matrix.mul_apply]
  calc
    ∑ x, rowOp N (0 : Fin (N+1)) x * M x j = rowOp N (0 : Fin (N+1)) 0 * M 0 j := by
      refine @Finset.sum_eq_single (Fin (N+1)) ℤ _ Finset.univ
        (fun k => rowOp N (0 : Fin (N+1)) k * M k j) (0 : Fin (N+1)) ?_ ?_
      · intro k _ hk
        have hne : k ≠ (0 : Fin (N+1)) := hk
        have hpred : ¬ (0 < (0 : Fin (N+1)).val ∧ k.val + 1 = (0 : Fin (N+1)).val) := by simp
        change rowOp N (0 : Fin (N+1)) k * M k j = 0
        rw [rowOp_apply_other N hne hpred]
        simp
      · intro h; simp at h
    _ = M 0 j := by simp [rowOp]

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
  rw [rowOp_apply_diag]
  simp only [one_mul]
  rw [Finset.sum_eq_single p]
  · rw [rowOp_apply_pred N hi]
    ring
  · intro k hk hkp
    have hki : k ≠ i := by
      simpa using hk
    have hpred : ¬ (0 < i.val ∧ k.val + 1 = i.val) := by
      intro h
      have kval : k.val = p.val := by dsimp [p]; omega
      apply hkp
      exact Fin.ext kval
    rw [rowOp_apply_other N hki hpred]
    simp
  · intro hpnot
    exfalso
    apply hpnot
    simp [p, hp_ne]
