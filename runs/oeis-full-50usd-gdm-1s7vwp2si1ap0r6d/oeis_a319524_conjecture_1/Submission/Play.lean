import FormalConjectures.Util.ProblemImports
open Nat

theorem no_sol_y_28 (m m' k' : ℕ)
  (h1 : 107 + m * 109 = 109 + m' * 113)
  (h2 : 109 + m' * 113 = 113 + k' * 127)
  (hm' : m' < 109) : False := by
  have h_m_gt : m > m' := by
    by_contra h_le
    push_neg at h_le
    have h_le_mul : m * 109 ≤ m' * 109 := Nat.mul_le_mul_right 109 h_le
    have h_le_mul2 : m' * 109 ≤ m' * 113 := Nat.mul_le_mul_left m' (by decide)
    have h_step1 : 107 + m * 109 ≤ 107 + m' * 109 := Nat.add_le_add_left h_le_mul 107
    have h_step2 : 107 + m' * 109 ≤ 107 + m' * 113 := Nat.add_le_add_left h_le_mul2 107
    have h_step3 : 107 + m' * 113 < 109 + m' * 113 := Nat.add_lt_add_right (by decide : 107 < 109) _
    have h_lt : 107 + m * 109 < 109 + m' * 113 := h_step1.trans_lt (h_step2.trans_lt h_step3)
    exact (h_lt.ne h1).elim
  generalize h_D : m - m' = D
  have h_alg : D * 109 = 4 * m' + 2 := by
    have h_eq : m * 109 = m' * 109 + D * 109 := by
      rw [← h_D]
      rw [← Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt h_m_gt)]
    have h1' := h1
    rw [h_eq] at h1'
    have h_dist : m' * 113 = m' * 109 + 4 * m' := by
      rw [show 113 = 109 + 4 by decide, Nat.mul_add, Nat.mul_comm m' 4]
    rw [h_dist] at h1'
    have h1_assoc : (107 + D * 109) + m' * 109 = (109 + 4 * m') + m' * 109 := by
      calc (107 + D * 109) + m' * 109 = 107 + (D * 109 + m' * 109) := by rw [Nat.add_assoc]
      _ = 107 + (m' * 109 + D * 109) := by rw [Nat.add_comm (D * 109)]
      _ = 109 + (m' * 109 + 4 * m') := h1'
      _ = 109 + (4 * m' + m' * 109) := by rw [Nat.add_comm (m' * 109)]
      _ = (109 + 4 * m') + m' * 109 := by rw [Nat.add_assoc]
    have h1_sub := Nat.add_right_cancel h1_assoc
    have h1_sub_eq : 107 + D * 109 = 107 + (4 * m' + 2) := by
      calc 107 + D * 109 = (107 + D * 109) := rfl
      _ = 109 + 4 * m' := h1_sub
      _ = 107 + 2 + 4 * m' := rfl
      _ = 107 + (2 + 4 * m') := by rw [Nat.add_assoc]
      _ = 107 + (4 * m' + 2) := by rw [Nat.add_comm 2]
    exact Nat.add_left_cancel h1_sub_eq
  have hD_le : D ≤ 4 := by
    by_contra h_gt
    push_neg at h_gt
    have h1 : D * 109 ≥ 5 * 109 := Nat.mul_le_mul_right 109 h_gt
    have h2 : 4 * m' + 2 < 5 * 109 := by
      have : 4 * m' < 4 * 109 := Nat.mul_lt_mul_of_pos_left hm' (by decide)
      have : 4 * m' + 2 < 4 * 109 + 2 := Nat.add_lt_add_right this 2
      calc 4 * m' + 2 < 4 * 109 + 2 := this
      _ ≤ 5 * 109 := by decide
    have h_lt : 5 * 109 < 5 * 109 := by
      calc 5 * 109 ≤ D * 109 := h1
      _ = 4 * m' + 2 := h_alg
      _ < 5 * 109 := h2
    exact h_lt.ne rfl
  have hD_pos : 1 ≤ D := by
    rw [← h_D]
    exact Nat.sub_pos_of_lt h_m_gt
  have h_cases : D = 1 ∨ D = 2 ∨ D = 3 ∨ D = 4 := by
    clear h1 h2 hm' h_m_gt h_D h_alg
    omega
  have h_D_eq : D = 2 := by
    clear h1 h2 hm' h_m_gt h_D
    rcases h_cases with rfl | rfl | rfl | rfl
    · revert h_alg; omega
    · rfl
    · revert h_alg; omega
    · revert h_alg; omega
  have hm'_eq : m' = 54 := by
    have h_alg_sol : 2 * 109 = 4 * m' + 2 := h_D_eq ▸ h_alg
    have h_eval : 2 * 109 = 218 := by decide
    rw [h_eval] at h_alg_sol
    have h_sub : 216 = 4 * m' := by
      calc 216 = 218 - 2 := rfl
      _ = 4 * m' + 2 - 2 := by rw [h_alg_sol]
      _ = 4 * m' := rfl
    have h_div : 216 / 4 = (4 * m') / 4 := by rw [h_sub]
    rw [Nat.mul_div_cancel_left m' (by decide : 0 < 4)] at h_div
    have h_div_eval : 216 / 4 = 54 := by decide
    exact h_div.symm.trans h_div_eval
  rw [hm'_eq] at h2
  revert h2
  intro h2'
  omega
