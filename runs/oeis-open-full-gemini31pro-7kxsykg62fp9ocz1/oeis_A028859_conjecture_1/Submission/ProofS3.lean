import Submission.ProofS2
import Mathlib

theorem end_le_2 {L : ℕ} (hL : L > 0) (x : Fin L → ℕ) (hx : isValid2 x) : x ⟨L - 1, by omega⟩ ≤ 2 := by
  let last_idx : Fin L := ⟨L - 1, by omega⟩
  have h_last_val : last_idx.val = L - 1 := rfl
  by_cases hL2 : L < 2
  · have h1 : L = 1 := by omega
    have h_max : Finset.sup Finset.univ x = x ⟨0, by omega⟩ := by
      apply le_antisymm
      · apply Finset.sup_le
        intro i _
        have : i = ⟨0, by omega⟩ := Fin.ext (by omega)
        rw [this]
      · exact Finset.le_sup (Finset.mem_univ _)
    by_contra h_3
    push_neg at h_3
    have : x ⟨0, by omega⟩ ≥ 3 := by
      have h_eq : ⟨L - 1, by omega⟩ = (⟨0, by omega⟩ : Fin L) := Fin.ext (by omega)
      rw [h_eq] at h_3
      exact h_3
    have h_max_ge_2 : Finset.sup Finset.univ x ≥ 2 := by omega
    have ⟨i1, hi1⟩ := hx.2.2.1 1 (by omega)
    have ⟨i2, hi2⟩ := hx.2.2.1 2 (by omega)
    have : i1 = i2 := Fin.ext (by omega)
    rw [this] at hi1
    rw [hi1] at hi2
    omega
  · have hL_ge_2 : L ≥ 2 := by omega
    have h_3_cont : x last_idx ≥ 3 → False := by
      intro h_3
      have h_max : Finset.sup Finset.univ x ≥ 3 := by
        have : x last_idx ≤ Finset.sup Finset.univ x := Finset.le_sup (Finset.mem_univ _)
        omega
      have ⟨i1, hi1⟩ := hx.2.2.1 1 (by omega)
      have ⟨i2, hi2⟩ := hx.2.2.1 2 (by omega)
      have hi1_eq : i1.val = L - 2 := by
        by_contra h_i1
        have h_lt : i1.val < last_idx.val := by
          by_contra h_ge
          push_neg at h_ge
          have hi1_lt := i1.isLt
          have : i1 = last_idx := Fin.ext (by omega)
          rw [this] at hi1
          omega
        have hi1_lt := i1.isLt
        have h_neq : last_idx.val ≠ i1.val + 1 := by omega
        have h_ge := hx.2.2.2 i1 last_idx h_lt h_neq
        rw [hi1] at h_ge
        omega
      have hi2_eq : i2.val = L - 2 := by
        by_contra h_i2
        have h_lt : i2.val < last_idx.val := by
          by_contra h_ge
          push_neg at h_ge
          have hi2_lt := i2.isLt
          have : i2 = last_idx := Fin.ext (by omega)
          rw [this] at hi2
          omega
        have hi2_lt := i2.isLt
        have h_neq : last_idx.val ≠ i2.val + 1 := by omega
        have h_ge := hx.2.2.2 i2 last_idx h_lt h_neq
        rw [hi2] at h_ge
        omega
      have : i1 = i2 := Fin.ext (by omega)
      rw [this] at hi1
      rw [hi1] at hi2
      omega
    have h_eq : x ⟨L - 1, by omega⟩ = x last_idx := rfl
    rw [h_eq]
    by_contra h_2
    push_neg at h_2
    exact h_3_cont h_2
