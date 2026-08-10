import FormalConjectures.Util.ProblemImports
open Nat

theorem no_sol_y_9 (m m' k' : ℕ)
  (h1 : 23 + m * 29 = 29 + m' * 31)
  (h2 : 29 + m' * 31 = 31 + k' * 37)
  (hm' : m' < 29) : False := by
  have h_m_gt : m > m' := by
    by_contra h_le
    push_neg at h_le
    have h_le_mul : m * 29 ≤ m' * 29 := Nat.mul_le_mul_right 29 h_le
    have h_le_mul2 : m' * 29 ≤ m' * 31 := Nat.mul_le_mul_left m' (by decide)
    have h_step1 : 23 + m * 29 ≤ 23 + m' * 29 := Nat.add_le_add_left h_le_mul 23
    have h_step2 : 23 + m' * 29 ≤ 23 + m' * 31 := Nat.add_le_add_left h_le_mul2 23
    have h_step3 : 23 + m' * 31 < 29 + m' * 31 := Nat.add_lt_add_right (by decide : 23 < 29) _
    have h_lt : 23 + m * 29 < 29 + m' * 31 := h_step1.trans_lt (h_step2.trans_lt h_step3)
    exact (h_lt.ne h1).elim
  generalize h_D : m - m' = D
  have h_alg : D * 29 = 2 * m' + 6 := by
    have h_eq : m * 29 = m' * 29 + D * 29 := by
      rw [← h_D]
      rw [← Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt h_m_gt)]
    have h1' := h1
    rw [h_eq] at h1'
    have h_dist : m' * 31 = m' * 29 + 2 * m' := by
      rw [show 31 = 29 + 2 by decide, Nat.mul_add, Nat.mul_comm m' 2]
    rw [h_dist] at h1'
    have h1_assoc : (23 + D * 29) + m' * 29 = (29 + 2 * m') + m' * 29 := by
      calc (23 + D * 29) + m' * 29 = 23 + (D * 29 + m' * 29) := by rw [Nat.add_assoc]
      _ = 23 + (m' * 29 + D * 29) := by rw [Nat.add_comm (D * 29)]
      _ = 29 + (m' * 29 + 2 * m') := h1'
      _ = 29 + (2 * m' + m' * 29) := by rw [Nat.add_comm (m' * 29)]
      _ = (29 + 2 * m') + m' * 29 := by rw [Nat.add_assoc]
    have h1_sub := Nat.add_right_cancel h1_assoc
    have h1_sub_eq : 23 + D * 29 = 23 + (2 * m' + 6) := by
      calc 23 + D * 29 = (23 + D * 29) := rfl
      _ = 29 + 2 * m' := h1_sub
      _ = 23 + 6 + 2 * m' := rfl
      _ = 23 + (6 + 2 * m') := by rw [Nat.add_assoc]
      _ = 23 + (2 * m' + 6) := by rw [Nat.add_comm 6]
    exact Nat.add_left_cancel h1_sub_eq
  have hD_le : D ≤ 2 := by
    by_contra h_gt
    push_neg at h_gt
    have h1 : D * 29 ≥ 3 * 29 := Nat.mul_le_mul_right 29 h_gt
    have h2 : 2 * m' + 6 < 3 * 29 := by
      have : 2 * m' < 2 * 29 := Nat.mul_lt_mul_of_pos_left hm' (by decide)
      have : 2 * m' + 6 < 2 * 29 + 6 := Nat.add_lt_add_right this 6
      calc 2 * m' + 6 < 2 * 29 + 6 := this
      _ ≤ 3 * 29 := by decide
    have h_lt : 3 * 29 < 3 * 29 := by
      calc 3 * 29 ≤ D * 29 := h1
      _ = 2 * m' + 6 := h_alg
      _ < 3 * 29 := h2
    exact h_lt.ne rfl
  have hD_pos : 1 ≤ D := by
    rw [← h_D]
    exact Nat.sub_pos_of_lt h_m_gt
  have h_cases : D = 1 ∨ D = 2 := by
    clear h1 h2 hm' h_m_gt h_D h_alg
    omega
  have h_D_eq : D = 2 := by
    clear h1 h2 hm' h_m_gt h_D
    rcases h_cases with rfl | rfl
    · revert h_alg; omega
    · rfl
  have hm'_eq : m' = 26 := by
    have h_alg_sol : 2 * 29 = 2 * m' + 6 := h_D_eq ▸ h_alg
    have h_eval : 2 * 29 = 58 := by decide
    rw [h_eval] at h_alg_sol
    have h_sub : 52 = 2 * m' := by
      calc 52 = 58 - 6 := rfl
      _ = 2 * m' + 6 - 6 := by rw [h_alg_sol]
      _ = 2 * m' := rfl
    have h_div : 52 / 2 = (2 * m') / 2 := by rw [h_sub]
    rw [Nat.mul_div_cancel_left m' (by decide : 0 < 2)] at h_div
    have h_div_eval : 52 / 2 = 26 := by decide
    exact h_div.symm.trans h_div_eval
  rw [hm'_eq] at h2
  revert h2
  intro h2'
  omega


theorem no_sol_y_13 (m m' k' : ℕ)
  (h1 : 41 + m * 43 = 43 + m' * 47)
  (h2 : 43 + m' * 47 = 47 + k' * 53)
  (hm' : m' < 43) : False := by
  have h_m_gt : m > m' := by
    by_contra h_le
    push_neg at h_le
    have h_le_mul : m * 43 ≤ m' * 43 := Nat.mul_le_mul_right 43 h_le
    have h_le_mul2 : m' * 43 ≤ m' * 47 := Nat.mul_le_mul_left m' (by decide)
    have h_step1 : 41 + m * 43 ≤ 41 + m' * 43 := Nat.add_le_add_left h_le_mul 41
    have h_step2 : 41 + m' * 43 ≤ 41 + m' * 47 := Nat.add_le_add_left h_le_mul2 41
    have h_step3 : 41 + m' * 47 < 43 + m' * 47 := Nat.add_lt_add_right (by decide : 41 < 43) _
    have h_lt : 41 + m * 43 < 43 + m' * 47 := h_step1.trans_lt (h_step2.trans_lt h_step3)
    exact (h_lt.ne h1).elim
  generalize h_D : m - m' = D
  have h_alg : D * 43 = 4 * m' + 2 := by
    have h_eq : m * 43 = m' * 43 + D * 43 := by
      rw [← h_D]
      rw [← Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt h_m_gt)]
    have h1' := h1
    rw [h_eq] at h1'
    have h_dist : m' * 47 = m' * 43 + 4 * m' := by
      rw [show 47 = 43 + 4 by decide, Nat.mul_add, Nat.mul_comm m' 4]
    rw [h_dist] at h1'
    have h1_assoc : (41 + D * 43) + m' * 43 = (43 + 4 * m') + m' * 43 := by
      calc (41 + D * 43) + m' * 43 = 41 + (D * 43 + m' * 43) := by rw [Nat.add_assoc]
      _ = 41 + (m' * 43 + D * 43) := by rw [Nat.add_comm (D * 43)]
      _ = 43 + (m' * 43 + 4 * m') := h1'
      _ = 43 + (4 * m' + m' * 43) := by rw [Nat.add_comm (m' * 43)]
      _ = (43 + 4 * m') + m' * 43 := by rw [Nat.add_assoc]
    have h1_sub := Nat.add_right_cancel h1_assoc
    have h1_sub_eq : 41 + D * 43 = 41 + (4 * m' + 2) := by
      calc 41 + D * 43 = (41 + D * 43) := rfl
      _ = 43 + 4 * m' := h1_sub
      _ = 41 + 2 + 4 * m' := rfl
      _ = 41 + (2 + 4 * m') := by rw [Nat.add_assoc]
      _ = 41 + (4 * m' + 2) := by rw [Nat.add_comm 2]
    exact Nat.add_left_cancel h1_sub_eq
  have hD_le : D ≤ 4 := by
    by_contra h_gt
    push_neg at h_gt
    have h1 : D * 43 ≥ 5 * 43 := Nat.mul_le_mul_right 43 h_gt
    have h2 : 4 * m' + 2 < 5 * 43 := by
      have : 4 * m' < 4 * 43 := Nat.mul_lt_mul_of_pos_left hm' (by decide)
      have : 4 * m' + 2 < 4 * 43 + 2 := Nat.add_lt_add_right this 2
      calc 4 * m' + 2 < 4 * 43 + 2 := this
      _ ≤ 5 * 43 := by decide
    have h_lt : 5 * 43 < 5 * 43 := by
      calc 5 * 43 ≤ D * 43 := h1
      _ = 4 * m' + 2 := h_alg
      _ < 5 * 43 := h2
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
  have hm'_eq : m' = 21 := by
    have h_alg_sol : 2 * 43 = 4 * m' + 2 := h_D_eq ▸ h_alg
    have h_eval : 2 * 43 = 86 := by decide
    rw [h_eval] at h_alg_sol
    have h_sub : 84 = 4 * m' := by
      calc 84 = 86 - 2 := rfl
      _ = 4 * m' + 2 - 2 := by rw [h_alg_sol]
      _ = 4 * m' := rfl
    have h_div : 84 / 4 = (4 * m') / 4 := by rw [h_sub]
    rw [Nat.mul_div_cancel_left m' (by decide : 0 < 4)] at h_div
    have h_div_eval : 84 / 4 = 21 := by decide
    exact h_div.symm.trans h_div_eval
  rw [hm'_eq] at h2
  revert h2
  intro h2'
  omega


theorem no_sol_y_14 (m m' k' : ℕ)
  (h1 : 43 + m * 47 = 47 + m' * 53)
  (h2 : 47 + m' * 53 = 53 + k' * 59)
  (hm' : m' < 47) : False := by
  have h_m_gt : m > m' := by
    by_contra h_le
    push_neg at h_le
    have h_le_mul : m * 47 ≤ m' * 47 := Nat.mul_le_mul_right 47 h_le
    have h_le_mul2 : m' * 47 ≤ m' * 53 := Nat.mul_le_mul_left m' (by decide)
    have h_step1 : 43 + m * 47 ≤ 43 + m' * 47 := Nat.add_le_add_left h_le_mul 43
    have h_step2 : 43 + m' * 47 ≤ 43 + m' * 53 := Nat.add_le_add_left h_le_mul2 43
    have h_step3 : 43 + m' * 53 < 47 + m' * 53 := Nat.add_lt_add_right (by decide : 43 < 47) _
    have h_lt : 43 + m * 47 < 47 + m' * 53 := h_step1.trans_lt (h_step2.trans_lt h_step3)
    exact (h_lt.ne h1).elim
  generalize h_D : m - m' = D
  have h_alg : D * 47 = 6 * m' + 4 := by
    have h_eq : m * 47 = m' * 47 + D * 47 := by
      rw [← h_D]
      rw [← Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt h_m_gt)]
    have h1' := h1
    rw [h_eq] at h1'
    have h_dist : m' * 53 = m' * 47 + 6 * m' := by
      rw [show 53 = 47 + 6 by decide, Nat.mul_add, Nat.mul_comm m' 6]
    rw [h_dist] at h1'
    have h1_assoc : (43 + D * 47) + m' * 47 = (47 + 6 * m') + m' * 47 := by
      calc (43 + D * 47) + m' * 47 = 43 + (D * 47 + m' * 47) := by rw [Nat.add_assoc]
      _ = 43 + (m' * 47 + D * 47) := by rw [Nat.add_comm (D * 47)]
      _ = 47 + (m' * 47 + 6 * m') := h1'
      _ = 47 + (6 * m' + m' * 47) := by rw [Nat.add_comm (m' * 47)]
      _ = (47 + 6 * m') + m' * 47 := by rw [Nat.add_assoc]
    have h1_sub := Nat.add_right_cancel h1_assoc
    have h1_sub_eq : 43 + D * 47 = 43 + (6 * m' + 4) := by
      calc 43 + D * 47 = (43 + D * 47) := rfl
      _ = 47 + 6 * m' := h1_sub
      _ = 43 + 4 + 6 * m' := rfl
      _ = 43 + (4 + 6 * m') := by rw [Nat.add_assoc]
      _ = 43 + (6 * m' + 4) := by rw [Nat.add_comm 4]
    exact Nat.add_left_cancel h1_sub_eq
  have hD_le : D ≤ 6 := by
    by_contra h_gt
    push_neg at h_gt
    have h1 : D * 47 ≥ 7 * 47 := Nat.mul_le_mul_right 47 h_gt
    have h2 : 6 * m' + 4 < 7 * 47 := by
      have : 6 * m' < 6 * 47 := Nat.mul_lt_mul_of_pos_left hm' (by decide)
      have : 6 * m' + 4 < 6 * 47 + 4 := Nat.add_lt_add_right this 4
      calc 6 * m' + 4 < 6 * 47 + 4 := this
      _ ≤ 7 * 47 := by decide
    have h_lt : 7 * 47 < 7 * 47 := by
      calc 7 * 47 ≤ D * 47 := h1
      _ = 6 * m' + 4 := h_alg
      _ < 7 * 47 := h2
    exact h_lt.ne rfl
  have hD_pos : 1 ≤ D := by
    rw [← h_D]
    exact Nat.sub_pos_of_lt h_m_gt
  have h_cases : D = 1 ∨ D = 2 ∨ D = 3 ∨ D = 4 ∨ D = 5 ∨ D = 6 := by
    clear h1 h2 hm' h_m_gt h_D h_alg
    omega
  have h_D_eq : D = 2 := by
    clear h1 h2 hm' h_m_gt h_D
    rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl
    · revert h_alg; omega
    · rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
  have hm'_eq : m' = 15 := by
    have h_alg_sol : 2 * 47 = 6 * m' + 4 := h_D_eq ▸ h_alg
    have h_eval : 2 * 47 = 94 := by decide
    rw [h_eval] at h_alg_sol
    have h_sub : 90 = 6 * m' := by
      calc 90 = 94 - 4 := rfl
      _ = 6 * m' + 4 - 4 := by rw [h_alg_sol]
      _ = 6 * m' := rfl
    have h_div : 90 / 6 = (6 * m') / 6 := by rw [h_sub]
    rw [Nat.mul_div_cancel_left m' (by decide : 0 < 6)] at h_div
    have h_div_eval : 90 / 6 = 15 := by decide
    exact h_div.symm.trans h_div_eval
  rw [hm'_eq] at h2
  revert h2
  intro h2'
  omega


theorem no_sol_y_22 (m m' k' : ℕ)
  (h1 : 79 + m * 83 = 83 + m' * 89)
  (h2 : 83 + m' * 89 = 89 + k' * 97)
  (hm' : m' < 83) : False := by
  have h_m_gt : m > m' := by
    by_contra h_le
    push_neg at h_le
    have h_le_mul : m * 83 ≤ m' * 83 := Nat.mul_le_mul_right 83 h_le
    have h_le_mul2 : m' * 83 ≤ m' * 89 := Nat.mul_le_mul_left m' (by decide)
    have h_step1 : 79 + m * 83 ≤ 79 + m' * 83 := Nat.add_le_add_left h_le_mul 79
    have h_step2 : 79 + m' * 83 ≤ 79 + m' * 89 := Nat.add_le_add_left h_le_mul2 79
    have h_step3 : 79 + m' * 89 < 83 + m' * 89 := Nat.add_lt_add_right (by decide : 79 < 83) _
    have h_lt : 79 + m * 83 < 83 + m' * 89 := h_step1.trans_lt (h_step2.trans_lt h_step3)
    exact (h_lt.ne h1).elim
  generalize h_D : m - m' = D
  have h_alg : D * 83 = 6 * m' + 4 := by
    have h_eq : m * 83 = m' * 83 + D * 83 := by
      rw [← h_D]
      rw [← Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt h_m_gt)]
    have h1' := h1
    rw [h_eq] at h1'
    have h_dist : m' * 89 = m' * 83 + 6 * m' := by
      rw [show 89 = 83 + 6 by decide, Nat.mul_add, Nat.mul_comm m' 6]
    rw [h_dist] at h1'
    have h1_assoc : (79 + D * 83) + m' * 83 = (83 + 6 * m') + m' * 83 := by
      calc (79 + D * 83) + m' * 83 = 79 + (D * 83 + m' * 83) := by rw [Nat.add_assoc]
      _ = 79 + (m' * 83 + D * 83) := by rw [Nat.add_comm (D * 83)]
      _ = 83 + (m' * 83 + 6 * m') := h1'
      _ = 83 + (6 * m' + m' * 83) := by rw [Nat.add_comm (m' * 83)]
      _ = (83 + 6 * m') + m' * 83 := by rw [Nat.add_assoc]
    have h1_sub := Nat.add_right_cancel h1_assoc
    have h1_sub_eq : 79 + D * 83 = 79 + (6 * m' + 4) := by
      calc 79 + D * 83 = (79 + D * 83) := rfl
      _ = 83 + 6 * m' := h1_sub
      _ = 79 + 4 + 6 * m' := rfl
      _ = 79 + (4 + 6 * m') := by rw [Nat.add_assoc]
      _ = 79 + (6 * m' + 4) := by rw [Nat.add_comm 4]
    exact Nat.add_left_cancel h1_sub_eq
  have hD_le : D ≤ 6 := by
    by_contra h_gt
    push_neg at h_gt
    have h1 : D * 83 ≥ 7 * 83 := Nat.mul_le_mul_right 83 h_gt
    have h2 : 6 * m' + 4 < 7 * 83 := by
      have : 6 * m' < 6 * 83 := Nat.mul_lt_mul_of_pos_left hm' (by decide)
      have : 6 * m' + 4 < 6 * 83 + 4 := Nat.add_lt_add_right this 4
      calc 6 * m' + 4 < 6 * 83 + 4 := this
      _ ≤ 7 * 83 := by decide
    have h_lt : 7 * 83 < 7 * 83 := by
      calc 7 * 83 ≤ D * 83 := h1
      _ = 6 * m' + 4 := h_alg
      _ < 7 * 83 := h2
    exact h_lt.ne rfl
  have hD_pos : 1 ≤ D := by
    rw [← h_D]
    exact Nat.sub_pos_of_lt h_m_gt
  have h_cases : D = 1 ∨ D = 2 ∨ D = 3 ∨ D = 4 ∨ D = 5 ∨ D = 6 := by
    clear h1 h2 hm' h_m_gt h_D h_alg
    omega
  have h_D_eq : D = 2 := by
    clear h1 h2 hm' h_m_gt h_D
    rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl
    · revert h_alg; omega
    · rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
  have hm'_eq : m' = 27 := by
    have h_alg_sol : 2 * 83 = 6 * m' + 4 := h_D_eq ▸ h_alg
    have h_eval : 2 * 83 = 166 := by decide
    rw [h_eval] at h_alg_sol
    have h_sub : 162 = 6 * m' := by
      calc 162 = 166 - 4 := rfl
      _ = 6 * m' + 4 - 4 := by rw [h_alg_sol]
      _ = 6 * m' := rfl
    have h_div : 162 / 6 = (6 * m') / 6 := by rw [h_sub]
    rw [Nat.mul_div_cancel_left m' (by decide : 0 < 6)] at h_div
    have h_div_eval : 162 / 6 = 27 := by decide
    exact h_div.symm.trans h_div_eval
  rw [hm'_eq] at h2
  revert h2
  intro h2'
  omega


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


theorem no_sol_y_45 (m m' k' : ℕ)
  (h1 : 197 + m * 199 = 199 + m' * 211)
  (h2 : 199 + m' * 211 = 211 + k' * 223)
  (hm' : m' < 199) : False := by
  have h_m_gt : m > m' := by
    by_contra h_le
    push_neg at h_le
    have h_le_mul : m * 199 ≤ m' * 199 := Nat.mul_le_mul_right 199 h_le
    have h_le_mul2 : m' * 199 ≤ m' * 211 := Nat.mul_le_mul_left m' (by decide)
    have h_step1 : 197 + m * 199 ≤ 197 + m' * 199 := Nat.add_le_add_left h_le_mul 197
    have h_step2 : 197 + m' * 199 ≤ 197 + m' * 211 := Nat.add_le_add_left h_le_mul2 197
    have h_step3 : 197 + m' * 211 < 199 + m' * 211 := Nat.add_lt_add_right (by decide : 197 < 199) _
    have h_lt : 197 + m * 199 < 199 + m' * 211 := h_step1.trans_lt (h_step2.trans_lt h_step3)
    exact (h_lt.ne h1).elim
  generalize h_D : m - m' = D
  have h_alg : D * 199 = 12 * m' + 2 := by
    have h_eq : m * 199 = m' * 199 + D * 199 := by
      rw [← h_D]
      rw [← Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt h_m_gt)]
    have h1' := h1
    rw [h_eq] at h1'
    have h_dist : m' * 211 = m' * 199 + 12 * m' := by
      rw [show 211 = 199 + 12 by decide, Nat.mul_add, Nat.mul_comm m' 12]
    rw [h_dist] at h1'
    have h1_assoc : (197 + D * 199) + m' * 199 = (199 + 12 * m') + m' * 199 := by
      calc (197 + D * 199) + m' * 199 = 197 + (D * 199 + m' * 199) := by rw [Nat.add_assoc]
      _ = 197 + (m' * 199 + D * 199) := by rw [Nat.add_comm (D * 199)]
      _ = 199 + (m' * 199 + 12 * m') := h1'
      _ = 199 + (12 * m' + m' * 199) := by rw [Nat.add_comm (m' * 199)]
      _ = (199 + 12 * m') + m' * 199 := by rw [Nat.add_assoc]
    have h1_sub := Nat.add_right_cancel h1_assoc
    have h1_sub_eq : 197 + D * 199 = 197 + (12 * m' + 2) := by
      calc 197 + D * 199 = (197 + D * 199) := rfl
      _ = 199 + 12 * m' := h1_sub
      _ = 197 + 2 + 12 * m' := rfl
      _ = 197 + (2 + 12 * m') := by rw [Nat.add_assoc]
      _ = 197 + (12 * m' + 2) := by rw [Nat.add_comm 2]
    exact Nat.add_left_cancel h1_sub_eq
  have hD_le : D ≤ 12 := by
    by_contra h_gt
    push_neg at h_gt
    have h1 : D * 199 ≥ 13 * 199 := Nat.mul_le_mul_right 199 h_gt
    have h2 : 12 * m' + 2 < 13 * 199 := by
      have : 12 * m' < 12 * 199 := Nat.mul_lt_mul_of_pos_left hm' (by decide)
      have : 12 * m' + 2 < 12 * 199 + 2 := Nat.add_lt_add_right this 2
      calc 12 * m' + 2 < 12 * 199 + 2 := this
      _ ≤ 13 * 199 := by decide
    have h_lt : 13 * 199 < 13 * 199 := by
      calc 13 * 199 ≤ D * 199 := h1
      _ = 12 * m' + 2 := h_alg
      _ < 13 * 199 := h2
    exact h_lt.ne rfl
  have hD_pos : 1 ≤ D := by
    rw [← h_D]
    exact Nat.sub_pos_of_lt h_m_gt
  have h_cases : D = 1 ∨ D = 2 ∨ D = 3 ∨ D = 4 ∨ D = 5 ∨ D = 6 ∨ D = 7 ∨ D = 8 ∨ D = 9 ∨ D = 10 ∨ D = 11 ∨ D = 12 := by
    clear h1 h2 hm' h_m_gt h_D h_alg
    omega
  have h_D_eq : D = 2 := by
    clear h1 h2 hm' h_m_gt h_D
    rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · revert h_alg; omega
    · rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
  have hm'_eq : m' = 33 := by
    have h_alg_sol : 2 * 199 = 12 * m' + 2 := h_D_eq ▸ h_alg
    have h_eval : 2 * 199 = 398 := by decide
    rw [h_eval] at h_alg_sol
    have h_sub : 396 = 12 * m' := by
      calc 396 = 398 - 2 := rfl
      _ = 12 * m' + 2 - 2 := by rw [h_alg_sol]
      _ = 12 * m' := rfl
    have h_div : 396 / 12 = (12 * m') / 12 := by rw [h_sub]
    rw [Nat.mul_div_cancel_left m' (by decide : 0 < 12)] at h_div
    have h_div_eval : 396 / 12 = 33 := by decide
    exact h_div.symm.trans h_div_eval
  rw [hm'_eq] at h2
  revert h2
  intro h2'
  omega


theorem no_sol_y_60 (m m' k' : ℕ)
  (h1 : 281 + m * 283 = 283 + m' * 293)
  (h2 : 283 + m' * 293 = 293 + k' * 307)
  (hm' : m' < 283) : False := by
  have h_m_gt : m > m' := by
    by_contra h_le
    push_neg at h_le
    have h_le_mul : m * 283 ≤ m' * 283 := Nat.mul_le_mul_right 283 h_le
    have h_le_mul2 : m' * 283 ≤ m' * 293 := Nat.mul_le_mul_left m' (by decide)
    have h_step1 : 281 + m * 283 ≤ 281 + m' * 283 := Nat.add_le_add_left h_le_mul 281
    have h_step2 : 281 + m' * 283 ≤ 281 + m' * 293 := Nat.add_le_add_left h_le_mul2 281
    have h_step3 : 281 + m' * 293 < 283 + m' * 293 := Nat.add_lt_add_right (by decide : 281 < 283) _
    have h_lt : 281 + m * 283 < 283 + m' * 293 := h_step1.trans_lt (h_step2.trans_lt h_step3)
    exact (h_lt.ne h1).elim
  generalize h_D : m - m' = D
  have h_alg : D * 283 = 10 * m' + 2 := by
    have h_eq : m * 283 = m' * 283 + D * 283 := by
      rw [← h_D]
      rw [← Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt h_m_gt)]
    have h1' := h1
    rw [h_eq] at h1'
    have h_dist : m' * 293 = m' * 283 + 10 * m' := by
      rw [show 293 = 283 + 10 by decide, Nat.mul_add, Nat.mul_comm m' 10]
    rw [h_dist] at h1'
    have h1_assoc : (281 + D * 283) + m' * 283 = (283 + 10 * m') + m' * 283 := by
      calc (281 + D * 283) + m' * 283 = 281 + (D * 283 + m' * 283) := by rw [Nat.add_assoc]
      _ = 281 + (m' * 283 + D * 283) := by rw [Nat.add_comm (D * 283)]
      _ = 283 + (m' * 283 + 10 * m') := h1'
      _ = 283 + (10 * m' + m' * 283) := by rw [Nat.add_comm (m' * 283)]
      _ = (283 + 10 * m') + m' * 283 := by rw [Nat.add_assoc]
    have h1_sub := Nat.add_right_cancel h1_assoc
    have h1_sub_eq : 281 + D * 283 = 281 + (10 * m' + 2) := by
      calc 281 + D * 283 = (281 + D * 283) := rfl
      _ = 283 + 10 * m' := h1_sub
      _ = 281 + 2 + 10 * m' := rfl
      _ = 281 + (2 + 10 * m') := by rw [Nat.add_assoc]
      _ = 281 + (10 * m' + 2) := by rw [Nat.add_comm 2]
    exact Nat.add_left_cancel h1_sub_eq
  have hD_le : D ≤ 10 := by
    by_contra h_gt
    push_neg at h_gt
    have h1 : D * 283 ≥ 11 * 283 := Nat.mul_le_mul_right 283 h_gt
    have h2 : 10 * m' + 2 < 11 * 283 := by
      have : 10 * m' < 10 * 283 := Nat.mul_lt_mul_of_pos_left hm' (by decide)
      have : 10 * m' + 2 < 10 * 283 + 2 := Nat.add_lt_add_right this 2
      calc 10 * m' + 2 < 10 * 283 + 2 := this
      _ ≤ 11 * 283 := by decide
    have h_lt : 11 * 283 < 11 * 283 := by
      calc 11 * 283 ≤ D * 283 := h1
      _ = 10 * m' + 2 := h_alg
      _ < 11 * 283 := h2
    exact h_lt.ne rfl
  have hD_pos : 1 ≤ D := by
    rw [← h_D]
    exact Nat.sub_pos_of_lt h_m_gt
  have h_cases : D = 1 ∨ D = 2 ∨ D = 3 ∨ D = 4 ∨ D = 5 ∨ D = 6 ∨ D = 7 ∨ D = 8 ∨ D = 9 ∨ D = 10 := by
    clear h1 h2 hm' h_m_gt h_D h_alg
    omega
  have h_D_eq : D = 4 := by
    clear h1 h2 hm' h_m_gt h_D
    rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
  have hm'_eq : m' = 113 := by
    have h_alg_sol : 4 * 283 = 10 * m' + 2 := h_D_eq ▸ h_alg
    have h_eval : 4 * 283 = 1132 := by decide
    rw [h_eval] at h_alg_sol
    have h_sub : 1130 = 10 * m' := by
      calc 1130 = 1132 - 2 := rfl
      _ = 10 * m' + 2 - 2 := by rw [h_alg_sol]
      _ = 10 * m' := rfl
    have h_div : 1130 / 10 = (10 * m') / 10 := by rw [h_sub]
    rw [Nat.mul_div_cancel_left m' (by decide : 0 < 10)] at h_div
    have h_div_eval : 1130 / 10 = 113 := by decide
    exact h_div.symm.trans h_div_eval
  rw [hm'_eq] at h2
  revert h2
  intro h2'
  omega


theorem no_sol_y_64 (m m' k' : ℕ)
  (h1 : 311 + m * 313 = 313 + m' * 317)
  (h2 : 313 + m' * 317 = 317 + k' * 331)
  (hm' : m' < 313) : False := by
  have h_m_gt : m > m' := by
    by_contra h_le
    push_neg at h_le
    have h_le_mul : m * 313 ≤ m' * 313 := Nat.mul_le_mul_right 313 h_le
    have h_le_mul2 : m' * 313 ≤ m' * 317 := Nat.mul_le_mul_left m' (by decide)
    have h_step1 : 311 + m * 313 ≤ 311 + m' * 313 := Nat.add_le_add_left h_le_mul 311
    have h_step2 : 311 + m' * 313 ≤ 311 + m' * 317 := Nat.add_le_add_left h_le_mul2 311
    have h_step3 : 311 + m' * 317 < 313 + m' * 317 := Nat.add_lt_add_right (by decide : 311 < 313) _
    have h_lt : 311 + m * 313 < 313 + m' * 317 := h_step1.trans_lt (h_step2.trans_lt h_step3)
    exact (h_lt.ne h1).elim
  generalize h_D : m - m' = D
  have h_alg : D * 313 = 4 * m' + 2 := by
    have h_eq : m * 313 = m' * 313 + D * 313 := by
      rw [← h_D]
      rw [← Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt h_m_gt)]
    have h1' := h1
    rw [h_eq] at h1'
    have h_dist : m' * 317 = m' * 313 + 4 * m' := by
      rw [show 317 = 313 + 4 by decide, Nat.mul_add, Nat.mul_comm m' 4]
    rw [h_dist] at h1'
    have h1_assoc : (311 + D * 313) + m' * 313 = (313 + 4 * m') + m' * 313 := by
      calc (311 + D * 313) + m' * 313 = 311 + (D * 313 + m' * 313) := by rw [Nat.add_assoc]
      _ = 311 + (m' * 313 + D * 313) := by rw [Nat.add_comm (D * 313)]
      _ = 313 + (m' * 313 + 4 * m') := h1'
      _ = 313 + (4 * m' + m' * 313) := by rw [Nat.add_comm (m' * 313)]
      _ = (313 + 4 * m') + m' * 313 := by rw [Nat.add_assoc]
    have h1_sub := Nat.add_right_cancel h1_assoc
    have h1_sub_eq : 311 + D * 313 = 311 + (4 * m' + 2) := by
      calc 311 + D * 313 = (311 + D * 313) := rfl
      _ = 313 + 4 * m' := h1_sub
      _ = 311 + 2 + 4 * m' := rfl
      _ = 311 + (2 + 4 * m') := by rw [Nat.add_assoc]
      _ = 311 + (4 * m' + 2) := by rw [Nat.add_comm 2]
    exact Nat.add_left_cancel h1_sub_eq
  have hD_le : D ≤ 4 := by
    by_contra h_gt
    push_neg at h_gt
    have h1 : D * 313 ≥ 5 * 313 := Nat.mul_le_mul_right 313 h_gt
    have h2 : 4 * m' + 2 < 5 * 313 := by
      have : 4 * m' < 4 * 313 := Nat.mul_lt_mul_of_pos_left hm' (by decide)
      have : 4 * m' + 2 < 4 * 313 + 2 := Nat.add_lt_add_right this 2
      calc 4 * m' + 2 < 4 * 313 + 2 := this
      _ ≤ 5 * 313 := by decide
    have h_lt : 5 * 313 < 5 * 313 := by
      calc 5 * 313 ≤ D * 313 := h1
      _ = 4 * m' + 2 := h_alg
      _ < 5 * 313 := h2
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
  have hm'_eq : m' = 156 := by
    have h_alg_sol : 2 * 313 = 4 * m' + 2 := h_D_eq ▸ h_alg
    have h_eval : 2 * 313 = 626 := by decide
    rw [h_eval] at h_alg_sol
    have h_sub : 624 = 4 * m' := by
      calc 624 = 626 - 2 := rfl
      _ = 4 * m' + 2 - 2 := by rw [h_alg_sol]
      _ = 4 * m' := rfl
    have h_div : 624 / 4 = (4 * m') / 4 := by rw [h_sub]
    rw [Nat.mul_div_cancel_left m' (by decide : 0 < 4)] at h_div
    have h_div_eval : 624 / 4 = 156 := by decide
    exact h_div.symm.trans h_div_eval
  rw [hm'_eq] at h2
  revert h2
  intro h2'
  omega


theorem no_sol_y_144 (m m' k' : ℕ)
  (h1 : 827 + m * 829 = 829 + m' * 839)
  (h2 : 829 + m' * 839 = 839 + k' * 853)
  (hm' : m' < 829) : False := by
  have h_m_gt : m > m' := by
    by_contra h_le
    push_neg at h_le
    have h_le_mul : m * 829 ≤ m' * 829 := Nat.mul_le_mul_right 829 h_le
    have h_le_mul2 : m' * 829 ≤ m' * 839 := Nat.mul_le_mul_left m' (by decide)
    have h_step1 : 827 + m * 829 ≤ 827 + m' * 829 := Nat.add_le_add_left h_le_mul 827
    have h_step2 : 827 + m' * 829 ≤ 827 + m' * 839 := Nat.add_le_add_left h_le_mul2 827
    have h_step3 : 827 + m' * 839 < 829 + m' * 839 := Nat.add_lt_add_right (by decide : 827 < 829) _
    have h_lt : 827 + m * 829 < 829 + m' * 839 := h_step1.trans_lt (h_step2.trans_lt h_step3)
    exact (h_lt.ne h1).elim
  generalize h_D : m - m' = D
  have h_alg : D * 829 = 10 * m' + 2 := by
    have h_eq : m * 829 = m' * 829 + D * 829 := by
      rw [← h_D]
      rw [← Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt h_m_gt)]
    have h1' := h1
    rw [h_eq] at h1'
    have h_dist : m' * 839 = m' * 829 + 10 * m' := by
      rw [show 839 = 829 + 10 by decide, Nat.mul_add, Nat.mul_comm m' 10]
    rw [h_dist] at h1'
    have h1_assoc : (827 + D * 829) + m' * 829 = (829 + 10 * m') + m' * 829 := by
      calc (827 + D * 829) + m' * 829 = 827 + (D * 829 + m' * 829) := by rw [Nat.add_assoc]
      _ = 827 + (m' * 829 + D * 829) := by rw [Nat.add_comm (D * 829)]
      _ = 829 + (m' * 829 + 10 * m') := h1'
      _ = 829 + (10 * m' + m' * 829) := by rw [Nat.add_comm (m' * 829)]
      _ = (829 + 10 * m') + m' * 829 := by rw [Nat.add_assoc]
    have h1_sub := Nat.add_right_cancel h1_assoc
    have h1_sub_eq : 827 + D * 829 = 827 + (10 * m' + 2) := by
      calc 827 + D * 829 = (827 + D * 829) := rfl
      _ = 829 + 10 * m' := h1_sub
      _ = 827 + 2 + 10 * m' := rfl
      _ = 827 + (2 + 10 * m') := by rw [Nat.add_assoc]
      _ = 827 + (10 * m' + 2) := by rw [Nat.add_comm 2]
    exact Nat.add_left_cancel h1_sub_eq
  have hD_le : D ≤ 10 := by
    by_contra h_gt
    push_neg at h_gt
    have h1 : D * 829 ≥ 11 * 829 := Nat.mul_le_mul_right 829 h_gt
    have h2 : 10 * m' + 2 < 11 * 829 := by
      have : 10 * m' < 10 * 829 := Nat.mul_lt_mul_of_pos_left hm' (by decide)
      have : 10 * m' + 2 < 10 * 829 + 2 := Nat.add_lt_add_right this 2
      calc 10 * m' + 2 < 10 * 829 + 2 := this
      _ ≤ 11 * 829 := by decide
    have h_lt : 11 * 829 < 11 * 829 := by
      calc 11 * 829 ≤ D * 829 := h1
      _ = 10 * m' + 2 := h_alg
      _ < 11 * 829 := h2
    exact h_lt.ne rfl
  have hD_pos : 1 ≤ D := by
    rw [← h_D]
    exact Nat.sub_pos_of_lt h_m_gt
  have h_cases : D = 1 ∨ D = 2 ∨ D = 3 ∨ D = 4 ∨ D = 5 ∨ D = 6 ∨ D = 7 ∨ D = 8 ∨ D = 9 ∨ D = 10 := by
    clear h1 h2 hm' h_m_gt h_D h_alg
    omega
  have h_D_eq : D = 8 := by
    clear h1 h2 hm' h_m_gt h_D
    rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · rfl
    · revert h_alg; omega
    · revert h_alg; omega
  have hm'_eq : m' = 663 := by
    have h_alg_sol : 8 * 829 = 10 * m' + 2 := h_D_eq ▸ h_alg
    have h_eval : 8 * 829 = 6632 := by decide
    rw [h_eval] at h_alg_sol
    have h_sub : 6630 = 10 * m' := by
      calc 6630 = 6632 - 2 := rfl
      _ = 10 * m' + 2 - 2 := by rw [h_alg_sol]
      _ = 10 * m' := rfl
    have h_div : 6630 / 10 = (10 * m') / 10 := by rw [h_sub]
    rw [Nat.mul_div_cancel_left m' (by decide : 0 < 10)] at h_div
    have h_div_eval : 6630 / 10 = 663 := by decide
    exact h_div.symm.trans h_div_eval
  rw [hm'_eq] at h2
  revert h2
  intro h2'
  omega


theorem no_sol_y_187 (m m' k' : ℕ)
  (h1 : 1117 + m * 1123 = 1123 + m' * 1129)
  (h2 : 1123 + m' * 1129 = 1129 + k' * 1151)
  (hm' : m' < 1123) : False := by
  have h_m_gt : m > m' := by
    by_contra h_le
    push_neg at h_le
    have h_le_mul : m * 1123 ≤ m' * 1123 := Nat.mul_le_mul_right 1123 h_le
    have h_le_mul2 : m' * 1123 ≤ m' * 1129 := Nat.mul_le_mul_left m' (by decide)
    have h_step1 : 1117 + m * 1123 ≤ 1117 + m' * 1123 := Nat.add_le_add_left h_le_mul 1117
    have h_step2 : 1117 + m' * 1123 ≤ 1117 + m' * 1129 := Nat.add_le_add_left h_le_mul2 1117
    have h_step3 : 1117 + m' * 1129 < 1123 + m' * 1129 := Nat.add_lt_add_right (by decide : 1117 < 1123) _
    have h_lt : 1117 + m * 1123 < 1123 + m' * 1129 := h_step1.trans_lt (h_step2.trans_lt h_step3)
    exact (h_lt.ne h1).elim
  generalize h_D : m - m' = D
  have h_alg : D * 1123 = 6 * m' + 6 := by
    have h_eq : m * 1123 = m' * 1123 + D * 1123 := by
      rw [← h_D]
      rw [← Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt h_m_gt)]
    have h1' := h1
    rw [h_eq] at h1'
    have h_dist : m' * 1129 = m' * 1123 + 6 * m' := by
      rw [show 1129 = 1123 + 6 by decide, Nat.mul_add, Nat.mul_comm m' 6]
    rw [h_dist] at h1'
    have h1_assoc : (1117 + D * 1123) + m' * 1123 = (1123 + 6 * m') + m' * 1123 := by
      calc (1117 + D * 1123) + m' * 1123 = 1117 + (D * 1123 + m' * 1123) := by rw [Nat.add_assoc]
      _ = 1117 + (m' * 1123 + D * 1123) := by rw [Nat.add_comm (D * 1123)]
      _ = 1123 + (m' * 1123 + 6 * m') := h1'
      _ = 1123 + (6 * m' + m' * 1123) := by rw [Nat.add_comm (m' * 1123)]
      _ = (1123 + 6 * m') + m' * 1123 := by rw [Nat.add_assoc]
    have h1_sub := Nat.add_right_cancel h1_assoc
    have h1_sub_eq : 1117 + D * 1123 = 1117 + (6 * m' + 6) := by
      calc 1117 + D * 1123 = (1117 + D * 1123) := rfl
      _ = 1123 + 6 * m' := h1_sub
      _ = 1117 + 6 + 6 * m' := rfl
      _ = 1117 + (6 + 6 * m') := by rw [Nat.add_assoc]
      _ = 1117 + (6 * m' + 6) := by rw [Nat.add_comm 6]
    exact Nat.add_left_cancel h1_sub_eq
  have hD_le : D ≤ 6 := by
    by_contra h_gt
    push_neg at h_gt
    have h1 : D * 1123 ≥ 7 * 1123 := Nat.mul_le_mul_right 1123 h_gt
    have h2 : 6 * m' + 6 < 7 * 1123 := by
      have : 6 * m' < 6 * 1123 := Nat.mul_lt_mul_of_pos_left hm' (by decide)
      have : 6 * m' + 6 < 6 * 1123 + 6 := Nat.add_lt_add_right this 6
      calc 6 * m' + 6 < 6 * 1123 + 6 := this
      _ ≤ 7 * 1123 := by decide
    have h_lt : 7 * 1123 < 7 * 1123 := by
      calc 7 * 1123 ≤ D * 1123 := h1
      _ = 6 * m' + 6 := h_alg
      _ < 7 * 1123 := h2
    exact h_lt.ne rfl
  have hD_pos : 1 ≤ D := by
    rw [← h_D]
    exact Nat.sub_pos_of_lt h_m_gt
  have h_cases : D = 1 ∨ D = 2 ∨ D = 3 ∨ D = 4 ∨ D = 5 ∨ D = 6 := by
    clear h1 h2 hm' h_m_gt h_D h_alg
    omega
  have h_D_eq : D = 6 := by
    clear h1 h2 hm' h_m_gt h_D
    rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · rfl
  have hm'_eq : m' = 1122 := by
    have h_alg_sol : 6 * 1123 = 6 * m' + 6 := h_D_eq ▸ h_alg
    have h_eval : 6 * 1123 = 6738 := by decide
    rw [h_eval] at h_alg_sol
    have h_sub : 6732 = 6 * m' := by
      calc 6732 = 6738 - 6 := rfl
      _ = 6 * m' + 6 - 6 := by rw [h_alg_sol]
      _ = 6 * m' := rfl
    have h_div : 6732 / 6 = (6 * m') / 6 := by rw [h_sub]
    rw [Nat.mul_div_cancel_left m' (by decide : 0 < 6)] at h_div
    have h_div_eval : 6732 / 6 = 1122 := by decide
    exact h_div.symm.trans h_div_eval
  rw [hm'_eq] at h2
  revert h2
  intro h2'
  omega


theorem no_sol_y_203 (m m' k' : ℕ)
  (h1 : 1237 + m * 1249 = 1249 + m' * 1259)
  (h2 : 1249 + m' * 1259 = 1259 + k' * 1277)
  (hm' : m' < 1249) : False := by
  have h_m_gt : m > m' := by
    by_contra h_le
    push_neg at h_le
    have h_le_mul : m * 1249 ≤ m' * 1249 := Nat.mul_le_mul_right 1249 h_le
    have h_le_mul2 : m' * 1249 ≤ m' * 1259 := Nat.mul_le_mul_left m' (by decide)
    have h_step1 : 1237 + m * 1249 ≤ 1237 + m' * 1249 := Nat.add_le_add_left h_le_mul 1237
    have h_step2 : 1237 + m' * 1249 ≤ 1237 + m' * 1259 := Nat.add_le_add_left h_le_mul2 1237
    have h_step3 : 1237 + m' * 1259 < 1249 + m' * 1259 := Nat.add_lt_add_right (by decide : 1237 < 1249) _
    have h_lt : 1237 + m * 1249 < 1249 + m' * 1259 := h_step1.trans_lt (h_step2.trans_lt h_step3)
    exact (h_lt.ne h1).elim
  generalize h_D : m - m' = D
  have h_alg : D * 1249 = 10 * m' + 12 := by
    have h_eq : m * 1249 = m' * 1249 + D * 1249 := by
      rw [← h_D]
      rw [← Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt h_m_gt)]
    have h1' := h1
    rw [h_eq] at h1'
    have h_dist : m' * 1259 = m' * 1249 + 10 * m' := by
      rw [show 1259 = 1249 + 10 by decide, Nat.mul_add, Nat.mul_comm m' 10]
    rw [h_dist] at h1'
    have h1_assoc : (1237 + D * 1249) + m' * 1249 = (1249 + 10 * m') + m' * 1249 := by
      calc (1237 + D * 1249) + m' * 1249 = 1237 + (D * 1249 + m' * 1249) := by rw [Nat.add_assoc]
      _ = 1237 + (m' * 1249 + D * 1249) := by rw [Nat.add_comm (D * 1249)]
      _ = 1249 + (m' * 1249 + 10 * m') := h1'
      _ = 1249 + (10 * m' + m' * 1249) := by rw [Nat.add_comm (m' * 1249)]
      _ = (1249 + 10 * m') + m' * 1249 := by rw [Nat.add_assoc]
    have h1_sub := Nat.add_right_cancel h1_assoc
    have h1_sub_eq : 1237 + D * 1249 = 1237 + (10 * m' + 12) := by
      calc 1237 + D * 1249 = (1237 + D * 1249) := rfl
      _ = 1249 + 10 * m' := h1_sub
      _ = 1237 + 12 + 10 * m' := rfl
      _ = 1237 + (12 + 10 * m') := by rw [Nat.add_assoc]
      _ = 1237 + (10 * m' + 12) := by rw [Nat.add_comm 12]
    exact Nat.add_left_cancel h1_sub_eq
  have hD_le : D ≤ 10 := by
    by_contra h_gt
    push_neg at h_gt
    have h1 : D * 1249 ≥ 11 * 1249 := Nat.mul_le_mul_right 1249 h_gt
    have h2 : 10 * m' + 12 < 11 * 1249 := by
      have : 10 * m' < 10 * 1249 := Nat.mul_lt_mul_of_pos_left hm' (by decide)
      have : 10 * m' + 12 < 10 * 1249 + 12 := Nat.add_lt_add_right this 12
      calc 10 * m' + 12 < 10 * 1249 + 12 := this
      _ ≤ 11 * 1249 := by decide
    have h_lt : 11 * 1249 < 11 * 1249 := by
      calc 11 * 1249 ≤ D * 1249 := h1
      _ = 10 * m' + 12 := h_alg
      _ < 11 * 1249 := h2
    exact h_lt.ne rfl
  have hD_pos : 1 ≤ D := by
    rw [← h_D]
    exact Nat.sub_pos_of_lt h_m_gt
  have h_cases : D = 1 ∨ D = 2 ∨ D = 3 ∨ D = 4 ∨ D = 5 ∨ D = 6 ∨ D = 7 ∨ D = 8 ∨ D = 9 ∨ D = 10 := by
    clear h1 h2 hm' h_m_gt h_D h_alg
    omega
  have h_D_eq : D = 8 := by
    clear h1 h2 hm' h_m_gt h_D
    rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · rfl
    · revert h_alg; omega
    · revert h_alg; omega
  have hm'_eq : m' = 998 := by
    have h_alg_sol : 8 * 1249 = 10 * m' + 12 := h_D_eq ▸ h_alg
    have h_eval : 8 * 1249 = 9992 := by decide
    rw [h_eval] at h_alg_sol
    have h_sub : 9980 = 10 * m' := by
      calc 9980 = 9992 - 12 := rfl
      _ = 10 * m' + 12 - 12 := by rw [h_alg_sol]
      _ = 10 * m' := rfl
    have h_div : 9980 / 10 = (10 * m') / 10 := by rw [h_sub]
    rw [Nat.mul_div_cancel_left m' (by decide : 0 < 10)] at h_div
    have h_div_eval : 9980 / 10 = 998 := by decide
    exact h_div.symm.trans h_div_eval
  rw [hm'_eq] at h2
  revert h2
  intro h2'
  omega


theorem no_sol_y_215 (m m' k' : ℕ)
  (h1 : 1319 + m * 1321 = 1321 + m' * 1327)
  (h2 : 1321 + m' * 1327 = 1327 + k' * 1361)
  (hm' : m' < 1321) : False := by
  have h_m_gt : m > m' := by
    by_contra h_le
    push_neg at h_le
    have h_le_mul : m * 1321 ≤ m' * 1321 := Nat.mul_le_mul_right 1321 h_le
    have h_le_mul2 : m' * 1321 ≤ m' * 1327 := Nat.mul_le_mul_left m' (by decide)
    have h_step1 : 1319 + m * 1321 ≤ 1319 + m' * 1321 := Nat.add_le_add_left h_le_mul 1319
    have h_step2 : 1319 + m' * 1321 ≤ 1319 + m' * 1327 := Nat.add_le_add_left h_le_mul2 1319
    have h_step3 : 1319 + m' * 1327 < 1321 + m' * 1327 := Nat.add_lt_add_right (by decide : 1319 < 1321) _
    have h_lt : 1319 + m * 1321 < 1321 + m' * 1327 := h_step1.trans_lt (h_step2.trans_lt h_step3)
    exact (h_lt.ne h1).elim
  generalize h_D : m - m' = D
  have h_alg : D * 1321 = 6 * m' + 2 := by
    have h_eq : m * 1321 = m' * 1321 + D * 1321 := by
      rw [← h_D]
      rw [← Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt h_m_gt)]
    have h1' := h1
    rw [h_eq] at h1'
    have h_dist : m' * 1327 = m' * 1321 + 6 * m' := by
      rw [show 1327 = 1321 + 6 by decide, Nat.mul_add, Nat.mul_comm m' 6]
    rw [h_dist] at h1'
    have h1_assoc : (1319 + D * 1321) + m' * 1321 = (1321 + 6 * m') + m' * 1321 := by
      calc (1319 + D * 1321) + m' * 1321 = 1319 + (D * 1321 + m' * 1321) := by rw [Nat.add_assoc]
      _ = 1319 + (m' * 1321 + D * 1321) := by rw [Nat.add_comm (D * 1321)]
      _ = 1321 + (m' * 1321 + 6 * m') := h1'
      _ = 1321 + (6 * m' + m' * 1321) := by rw [Nat.add_comm (m' * 1321)]
      _ = (1321 + 6 * m') + m' * 1321 := by rw [Nat.add_assoc]
    have h1_sub := Nat.add_right_cancel h1_assoc
    have h1_sub_eq : 1319 + D * 1321 = 1319 + (6 * m' + 2) := by
      calc 1319 + D * 1321 = (1319 + D * 1321) := rfl
      _ = 1321 + 6 * m' := h1_sub
      _ = 1319 + 2 + 6 * m' := rfl
      _ = 1319 + (2 + 6 * m') := by rw [Nat.add_assoc]
      _ = 1319 + (6 * m' + 2) := by rw [Nat.add_comm 2]
    exact Nat.add_left_cancel h1_sub_eq
  have hD_le : D ≤ 6 := by
    by_contra h_gt
    push_neg at h_gt
    have h1 : D * 1321 ≥ 7 * 1321 := Nat.mul_le_mul_right 1321 h_gt
    have h2 : 6 * m' + 2 < 7 * 1321 := by
      have : 6 * m' < 6 * 1321 := Nat.mul_lt_mul_of_pos_left hm' (by decide)
      have : 6 * m' + 2 < 6 * 1321 + 2 := Nat.add_lt_add_right this 2
      calc 6 * m' + 2 < 6 * 1321 + 2 := this
      _ ≤ 7 * 1321 := by decide
    have h_lt : 7 * 1321 < 7 * 1321 := by
      calc 7 * 1321 ≤ D * 1321 := h1
      _ = 6 * m' + 2 := h_alg
      _ < 7 * 1321 := h2
    exact h_lt.ne rfl
  have hD_pos : 1 ≤ D := by
    rw [← h_D]
    exact Nat.sub_pos_of_lt h_m_gt
  have h_cases : D = 1 ∨ D = 2 ∨ D = 3 ∨ D = 4 ∨ D = 5 ∨ D = 6 := by
    clear h1 h2 hm' h_m_gt h_D h_alg
    omega
  have h_D_eq : D = 2 := by
    clear h1 h2 hm' h_m_gt h_D
    rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl
    · revert h_alg; omega
    · rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
  have hm'_eq : m' = 440 := by
    have h_alg_sol : 2 * 1321 = 6 * m' + 2 := h_D_eq ▸ h_alg
    have h_eval : 2 * 1321 = 2642 := by decide
    rw [h_eval] at h_alg_sol
    have h_sub : 2640 = 6 * m' := by
      calc 2640 = 2642 - 2 := rfl
      _ = 6 * m' + 2 - 2 := by rw [h_alg_sol]
      _ = 6 * m' := rfl
    have h_div : 2640 / 6 = (6 * m') / 6 := by rw [h_sub]
    rw [Nat.mul_div_cancel_left m' (by decide : 0 < 6)] at h_div
    have h_div_eval : 2640 / 6 = 440 := by decide
    exact h_div.symm.trans h_div_eval
  rw [hm'_eq] at h2
  revert h2
  intro h2'
  omega


theorem no_sol_y_257 (m m' k' : ℕ)
  (h1 : 1621 + m * 1627 = 1627 + m' * 1637)
  (h2 : 1627 + m' * 1637 = 1637 + k' * 1657)
  (hm' : m' < 1627) : False := by
  have h_m_gt : m > m' := by
    by_contra h_le
    push_neg at h_le
    have h_le_mul : m * 1627 ≤ m' * 1627 := Nat.mul_le_mul_right 1627 h_le
    have h_le_mul2 : m' * 1627 ≤ m' * 1637 := Nat.mul_le_mul_left m' (by decide)
    have h_step1 : 1621 + m * 1627 ≤ 1621 + m' * 1627 := Nat.add_le_add_left h_le_mul 1621
    have h_step2 : 1621 + m' * 1627 ≤ 1621 + m' * 1637 := Nat.add_le_add_left h_le_mul2 1621
    have h_step3 : 1621 + m' * 1637 < 1627 + m' * 1637 := Nat.add_lt_add_right (by decide : 1621 < 1627) _
    have h_lt : 1621 + m * 1627 < 1627 + m' * 1637 := h_step1.trans_lt (h_step2.trans_lt h_step3)
    exact (h_lt.ne h1).elim
  generalize h_D : m - m' = D
  have h_alg : D * 1627 = 10 * m' + 6 := by
    have h_eq : m * 1627 = m' * 1627 + D * 1627 := by
      rw [← h_D]
      rw [← Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt h_m_gt)]
    have h1' := h1
    rw [h_eq] at h1'
    have h_dist : m' * 1637 = m' * 1627 + 10 * m' := by
      rw [show 1637 = 1627 + 10 by decide, Nat.mul_add, Nat.mul_comm m' 10]
    rw [h_dist] at h1'
    have h1_assoc : (1621 + D * 1627) + m' * 1627 = (1627 + 10 * m') + m' * 1627 := by
      calc (1621 + D * 1627) + m' * 1627 = 1621 + (D * 1627 + m' * 1627) := by rw [Nat.add_assoc]
      _ = 1621 + (m' * 1627 + D * 1627) := by rw [Nat.add_comm (D * 1627)]
      _ = 1627 + (m' * 1627 + 10 * m') := h1'
      _ = 1627 + (10 * m' + m' * 1627) := by rw [Nat.add_comm (m' * 1627)]
      _ = (1627 + 10 * m') + m' * 1627 := by rw [Nat.add_assoc]
    have h1_sub := Nat.add_right_cancel h1_assoc
    have h1_sub_eq : 1621 + D * 1627 = 1621 + (10 * m' + 6) := by
      calc 1621 + D * 1627 = (1621 + D * 1627) := rfl
      _ = 1627 + 10 * m' := h1_sub
      _ = 1621 + 6 + 10 * m' := rfl
      _ = 1621 + (6 + 10 * m') := by rw [Nat.add_assoc]
      _ = 1621 + (10 * m' + 6) := by rw [Nat.add_comm 6]
    exact Nat.add_left_cancel h1_sub_eq
  have hD_le : D ≤ 10 := by
    by_contra h_gt
    push_neg at h_gt
    have h1 : D * 1627 ≥ 11 * 1627 := Nat.mul_le_mul_right 1627 h_gt
    have h2 : 10 * m' + 6 < 11 * 1627 := by
      have : 10 * m' < 10 * 1627 := Nat.mul_lt_mul_of_pos_left hm' (by decide)
      have : 10 * m' + 6 < 10 * 1627 + 6 := Nat.add_lt_add_right this 6
      calc 10 * m' + 6 < 10 * 1627 + 6 := this
      _ ≤ 11 * 1627 := by decide
    have h_lt : 11 * 1627 < 11 * 1627 := by
      calc 11 * 1627 ≤ D * 1627 := h1
      _ = 10 * m' + 6 := h_alg
      _ < 11 * 1627 := h2
    exact h_lt.ne rfl
  have hD_pos : 1 ≤ D := by
    rw [← h_D]
    exact Nat.sub_pos_of_lt h_m_gt
  have h_cases : D = 1 ∨ D = 2 ∨ D = 3 ∨ D = 4 ∨ D = 5 ∨ D = 6 ∨ D = 7 ∨ D = 8 ∨ D = 9 ∨ D = 10 := by
    clear h1 h2 hm' h_m_gt h_D h_alg
    omega
  have h_D_eq : D = 8 := by
    clear h1 h2 hm' h_m_gt h_D
    rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · rfl
    · revert h_alg; omega
    · revert h_alg; omega
  have hm'_eq : m' = 1301 := by
    have h_alg_sol : 8 * 1627 = 10 * m' + 6 := h_D_eq ▸ h_alg
    have h_eval : 8 * 1627 = 13016 := by decide
    rw [h_eval] at h_alg_sol
    have h_sub : 13010 = 10 * m' := by
      calc 13010 = 13016 - 6 := rfl
      _ = 10 * m' + 6 - 6 := by rw [h_alg_sol]
      _ = 10 * m' := rfl
    have h_div : 13010 / 10 = (10 * m') / 10 := by rw [h_sub]
    rw [Nat.mul_div_cancel_left m' (by decide : 0 < 10)] at h_div
    have h_div_eval : 13010 / 10 = 1301 := by decide
    exact h_div.symm.trans h_div_eval
  rw [hm'_eq] at h2
  revert h2
  intro h2'
  omega


theorem no_sol_y_325 (m m' k' : ℕ)
  (h1 : 2153 + m * 2161 = 2161 + m' * 2179)
  (h2 : 2161 + m' * 2179 = 2179 + k' * 2203)
  (hm' : m' < 2161) : False := by
  have h_m_gt : m > m' := by
    by_contra h_le
    push_neg at h_le
    have h_le_mul : m * 2161 ≤ m' * 2161 := Nat.mul_le_mul_right 2161 h_le
    have h_le_mul2 : m' * 2161 ≤ m' * 2179 := Nat.mul_le_mul_left m' (by decide)
    have h_step1 : 2153 + m * 2161 ≤ 2153 + m' * 2161 := Nat.add_le_add_left h_le_mul 2153
    have h_step2 : 2153 + m' * 2161 ≤ 2153 + m' * 2179 := Nat.add_le_add_left h_le_mul2 2153
    have h_step3 : 2153 + m' * 2179 < 2161 + m' * 2179 := Nat.add_lt_add_right (by decide : 2153 < 2161) _
    have h_lt : 2153 + m * 2161 < 2161 + m' * 2179 := h_step1.trans_lt (h_step2.trans_lt h_step3)
    exact (h_lt.ne h1).elim
  generalize h_D : m - m' = D
  have h_alg : D * 2161 = 18 * m' + 8 := by
    have h_eq : m * 2161 = m' * 2161 + D * 2161 := by
      rw [← h_D]
      rw [← Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt h_m_gt)]
    have h1' := h1
    rw [h_eq] at h1'
    have h_dist : m' * 2179 = m' * 2161 + 18 * m' := by
      rw [show 2179 = 2161 + 18 by decide, Nat.mul_add, Nat.mul_comm m' 18]
    rw [h_dist] at h1'
    have h1_assoc : (2153 + D * 2161) + m' * 2161 = (2161 + 18 * m') + m' * 2161 := by
      calc (2153 + D * 2161) + m' * 2161 = 2153 + (D * 2161 + m' * 2161) := by rw [Nat.add_assoc]
      _ = 2153 + (m' * 2161 + D * 2161) := by rw [Nat.add_comm (D * 2161)]
      _ = 2161 + (m' * 2161 + 18 * m') := h1'
      _ = 2161 + (18 * m' + m' * 2161) := by rw [Nat.add_comm (m' * 2161)]
      _ = (2161 + 18 * m') + m' * 2161 := by rw [Nat.add_assoc]
    have h1_sub := Nat.add_right_cancel h1_assoc
    have h1_sub_eq : 2153 + D * 2161 = 2153 + (18 * m' + 8) := by
      calc 2153 + D * 2161 = (2153 + D * 2161) := rfl
      _ = 2161 + 18 * m' := h1_sub
      _ = 2153 + 8 + 18 * m' := rfl
      _ = 2153 + (8 + 18 * m') := by rw [Nat.add_assoc]
      _ = 2153 + (18 * m' + 8) := by rw [Nat.add_comm 8]
    exact Nat.add_left_cancel h1_sub_eq
  have hD_le : D ≤ 18 := by
    by_contra h_gt
    push_neg at h_gt
    have h1 : D * 2161 ≥ 19 * 2161 := Nat.mul_le_mul_right 2161 h_gt
    have h2 : 18 * m' + 8 < 19 * 2161 := by
      have : 18 * m' < 18 * 2161 := Nat.mul_lt_mul_of_pos_left hm' (by decide)
      have : 18 * m' + 8 < 18 * 2161 + 8 := Nat.add_lt_add_right this 8
      calc 18 * m' + 8 < 18 * 2161 + 8 := this
      _ ≤ 19 * 2161 := by decide
    have h_lt : 19 * 2161 < 19 * 2161 := by
      calc 19 * 2161 ≤ D * 2161 := h1
      _ = 18 * m' + 8 := h_alg
      _ < 19 * 2161 := h2
    exact h_lt.ne rfl
  have hD_pos : 1 ≤ D := by
    rw [← h_D]
    exact Nat.sub_pos_of_lt h_m_gt
  have h_cases : D = 1 ∨ D = 2 ∨ D = 3 ∨ D = 4 ∨ D = 5 ∨ D = 6 ∨ D = 7 ∨ D = 8 ∨ D = 9 ∨ D = 10 ∨ D = 11 ∨ D = 12 ∨ D = 13 ∨ D = 14 ∨ D = 15 ∨ D = 16 ∨ D = 17 ∨ D = 18 := by
    clear h1 h2 hm' h_m_gt h_D h_alg
    omega
  have h_D_eq : D = 8 := by
    clear h1 h2 hm' h_m_gt h_D
    rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
  have hm'_eq : m' = 960 := by
    have h_alg_sol : 8 * 2161 = 18 * m' + 8 := h_D_eq ▸ h_alg
    have h_eval : 8 * 2161 = 17288 := by decide
    rw [h_eval] at h_alg_sol
    have h_sub : 17280 = 18 * m' := by
      calc 17280 = 17288 - 8 := rfl
      _ = 18 * m' + 8 - 8 := by rw [h_alg_sol]
      _ = 18 * m' := rfl
    have h_div : 17280 / 18 = (18 * m') / 18 := by rw [h_sub]
    rw [Nat.mul_div_cancel_left m' (by decide : 0 < 18)] at h_div
    have h_div_eval : 17280 / 18 = 960 := by decide
    exact h_div.symm.trans h_div_eval
  rw [hm'_eq] at h2
  revert h2
  intro h2'
  omega


theorem no_sol_y_366 (m m' k' : ℕ)
  (h1 : 2473 + m * 2477 = 2477 + m' * 2503)
  (h2 : 2477 + m' * 2503 = 2503 + k' * 2521)
  (hm' : m' < 2477) : False := by
  have h_m_gt : m > m' := by
    by_contra h_le
    push_neg at h_le
    have h_le_mul : m * 2477 ≤ m' * 2477 := Nat.mul_le_mul_right 2477 h_le
    have h_le_mul2 : m' * 2477 ≤ m' * 2503 := Nat.mul_le_mul_left m' (by decide)
    have h_step1 : 2473 + m * 2477 ≤ 2473 + m' * 2477 := Nat.add_le_add_left h_le_mul 2473
    have h_step2 : 2473 + m' * 2477 ≤ 2473 + m' * 2503 := Nat.add_le_add_left h_le_mul2 2473
    have h_step3 : 2473 + m' * 2503 < 2477 + m' * 2503 := Nat.add_lt_add_right (by decide : 2473 < 2477) _
    have h_lt : 2473 + m * 2477 < 2477 + m' * 2503 := h_step1.trans_lt (h_step2.trans_lt h_step3)
    exact (h_lt.ne h1).elim
  generalize h_D : m - m' = D
  have h_alg : D * 2477 = 26 * m' + 4 := by
    have h_eq : m * 2477 = m' * 2477 + D * 2477 := by
      rw [← h_D]
      rw [← Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt h_m_gt)]
    have h1' := h1
    rw [h_eq] at h1'
    have h_dist : m' * 2503 = m' * 2477 + 26 * m' := by
      rw [show 2503 = 2477 + 26 by decide, Nat.mul_add, Nat.mul_comm m' 26]
    rw [h_dist] at h1'
    have h1_assoc : (2473 + D * 2477) + m' * 2477 = (2477 + 26 * m') + m' * 2477 := by
      calc (2473 + D * 2477) + m' * 2477 = 2473 + (D * 2477 + m' * 2477) := by rw [Nat.add_assoc]
      _ = 2473 + (m' * 2477 + D * 2477) := by rw [Nat.add_comm (D * 2477)]
      _ = 2477 + (m' * 2477 + 26 * m') := h1'
      _ = 2477 + (26 * m' + m' * 2477) := by rw [Nat.add_comm (m' * 2477)]
      _ = (2477 + 26 * m') + m' * 2477 := by rw [Nat.add_assoc]
    have h1_sub := Nat.add_right_cancel h1_assoc
    have h1_sub_eq : 2473 + D * 2477 = 2473 + (26 * m' + 4) := by
      calc 2473 + D * 2477 = (2473 + D * 2477) := rfl
      _ = 2477 + 26 * m' := h1_sub
      _ = 2473 + 4 + 26 * m' := rfl
      _ = 2473 + (4 + 26 * m') := by rw [Nat.add_assoc]
      _ = 2473 + (26 * m' + 4) := by rw [Nat.add_comm 4]
    exact Nat.add_left_cancel h1_sub_eq
  have hD_le : D ≤ 26 := by
    by_contra h_gt
    push_neg at h_gt
    have h1 : D * 2477 ≥ 27 * 2477 := Nat.mul_le_mul_right 2477 h_gt
    have h2 : 26 * m' + 4 < 27 * 2477 := by
      have : 26 * m' < 26 * 2477 := Nat.mul_lt_mul_of_pos_left hm' (by decide)
      have : 26 * m' + 4 < 26 * 2477 + 4 := Nat.add_lt_add_right this 4
      calc 26 * m' + 4 < 26 * 2477 + 4 := this
      _ ≤ 27 * 2477 := by decide
    have h_lt : 27 * 2477 < 27 * 2477 := by
      calc 27 * 2477 ≤ D * 2477 := h1
      _ = 26 * m' + 4 := h_alg
      _ < 27 * 2477 := h2
    exact h_lt.ne rfl
  have hD_pos : 1 ≤ D := by
    rw [← h_D]
    exact Nat.sub_pos_of_lt h_m_gt
  have h_cases : D = 1 ∨ D = 2 ∨ D = 3 ∨ D = 4 ∨ D = 5 ∨ D = 6 ∨ D = 7 ∨ D = 8 ∨ D = 9 ∨ D = 10 ∨ D = 11 ∨ D = 12 ∨ D = 13 ∨ D = 14 ∨ D = 15 ∨ D = 16 ∨ D = 17 ∨ D = 18 ∨ D = 19 ∨ D = 20 ∨ D = 21 ∨ D = 22 ∨ D = 23 ∨ D = 24 ∨ D = 25 ∨ D = 26 := by
    clear h1 h2 hm' h_m_gt h_D h_alg
    omega
  have h_D_eq : D = 8 := by
    clear h1 h2 hm' h_m_gt h_D
    rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
  have hm'_eq : m' = 762 := by
    have h_alg_sol : 8 * 2477 = 26 * m' + 4 := h_D_eq ▸ h_alg
    have h_eval : 8 * 2477 = 19816 := by decide
    rw [h_eval] at h_alg_sol
    have h_sub : 19812 = 26 * m' := by
      calc 19812 = 19816 - 4 := rfl
      _ = 26 * m' + 4 - 4 := by rw [h_alg_sol]
      _ = 26 * m' := rfl
    have h_div : 19812 / 26 = (26 * m') / 26 := by rw [h_sub]
    rw [Nat.mul_div_cancel_left m' (by decide : 0 < 26)] at h_div
    have h_div_eval : 19812 / 26 = 762 := by decide
    exact h_div.symm.trans h_div_eval
  rw [hm'_eq] at h2
  revert h2
  intro h2'
  omega


theorem no_sol_y_444 (m m' k' : ℕ)
  (h1 : 3119 + m * 3121 = 3121 + m' * 3137)
  (h2 : 3121 + m' * 3137 = 3137 + k' * 3163)
  (hm' : m' < 3121) : False := by
  have h_m_gt : m > m' := by
    by_contra h_le
    push_neg at h_le
    have h_le_mul : m * 3121 ≤ m' * 3121 := Nat.mul_le_mul_right 3121 h_le
    have h_le_mul2 : m' * 3121 ≤ m' * 3137 := Nat.mul_le_mul_left m' (by decide)
    have h_step1 : 3119 + m * 3121 ≤ 3119 + m' * 3121 := Nat.add_le_add_left h_le_mul 3119
    have h_step2 : 3119 + m' * 3121 ≤ 3119 + m' * 3137 := Nat.add_le_add_left h_le_mul2 3119
    have h_step3 : 3119 + m' * 3137 < 3121 + m' * 3137 := Nat.add_lt_add_right (by decide : 3119 < 3121) _
    have h_lt : 3119 + m * 3121 < 3121 + m' * 3137 := h_step1.trans_lt (h_step2.trans_lt h_step3)
    exact (h_lt.ne h1).elim
  generalize h_D : m - m' = D
  have h_alg : D * 3121 = 16 * m' + 2 := by
    have h_eq : m * 3121 = m' * 3121 + D * 3121 := by
      rw [← h_D]
      rw [← Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt h_m_gt)]
    have h1' := h1
    rw [h_eq] at h1'
    have h_dist : m' * 3137 = m' * 3121 + 16 * m' := by
      rw [show 3137 = 3121 + 16 by decide, Nat.mul_add, Nat.mul_comm m' 16]
    rw [h_dist] at h1'
    have h1_assoc : (3119 + D * 3121) + m' * 3121 = (3121 + 16 * m') + m' * 3121 := by
      calc (3119 + D * 3121) + m' * 3121 = 3119 + (D * 3121 + m' * 3121) := by rw [Nat.add_assoc]
      _ = 3119 + (m' * 3121 + D * 3121) := by rw [Nat.add_comm (D * 3121)]
      _ = 3121 + (m' * 3121 + 16 * m') := h1'
      _ = 3121 + (16 * m' + m' * 3121) := by rw [Nat.add_comm (m' * 3121)]
      _ = (3121 + 16 * m') + m' * 3121 := by rw [Nat.add_assoc]
    have h1_sub := Nat.add_right_cancel h1_assoc
    have h1_sub_eq : 3119 + D * 3121 = 3119 + (16 * m' + 2) := by
      calc 3119 + D * 3121 = (3119 + D * 3121) := rfl
      _ = 3121 + 16 * m' := h1_sub
      _ = 3119 + 2 + 16 * m' := rfl
      _ = 3119 + (2 + 16 * m') := by rw [Nat.add_assoc]
      _ = 3119 + (16 * m' + 2) := by rw [Nat.add_comm 2]
    exact Nat.add_left_cancel h1_sub_eq
  have hD_le : D ≤ 16 := by
    by_contra h_gt
    push_neg at h_gt
    have h1 : D * 3121 ≥ 17 * 3121 := Nat.mul_le_mul_right 3121 h_gt
    have h2 : 16 * m' + 2 < 17 * 3121 := by
      have : 16 * m' < 16 * 3121 := Nat.mul_lt_mul_of_pos_left hm' (by decide)
      have : 16 * m' + 2 < 16 * 3121 + 2 := Nat.add_lt_add_right this 2
      calc 16 * m' + 2 < 16 * 3121 + 2 := this
      _ ≤ 17 * 3121 := by decide
    have h_lt : 17 * 3121 < 17 * 3121 := by
      calc 17 * 3121 ≤ D * 3121 := h1
      _ = 16 * m' + 2 := h_alg
      _ < 17 * 3121 := h2
    exact h_lt.ne rfl
  have hD_pos : 1 ≤ D := by
    rw [← h_D]
    exact Nat.sub_pos_of_lt h_m_gt
  have h_cases : D = 1 ∨ D = 2 ∨ D = 3 ∨ D = 4 ∨ D = 5 ∨ D = 6 ∨ D = 7 ∨ D = 8 ∨ D = 9 ∨ D = 10 ∨ D = 11 ∨ D = 12 ∨ D = 13 ∨ D = 14 ∨ D = 15 ∨ D = 16 := by
    clear h1 h2 hm' h_m_gt h_D h_alg
    omega
  have h_D_eq : D = 2 := by
    clear h1 h2 hm' h_m_gt h_D
    rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · revert h_alg; omega
    · rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
  have hm'_eq : m' = 390 := by
    have h_alg_sol : 2 * 3121 = 16 * m' + 2 := h_D_eq ▸ h_alg
    have h_eval : 2 * 3121 = 6242 := by decide
    rw [h_eval] at h_alg_sol
    have h_sub : 6240 = 16 * m' := by
      calc 6240 = 6242 - 2 := rfl
      _ = 16 * m' + 2 - 2 := by rw [h_alg_sol]
      _ = 16 * m' := rfl
    have h_div : 6240 / 16 = (16 * m') / 16 := by rw [h_sub]
    rw [Nat.mul_div_cancel_left m' (by decide : 0 < 16)] at h_div
    have h_div_eval : 6240 / 16 = 390 := by decide
    exact h_div.symm.trans h_div_eval
  rw [hm'_eq] at h2
  revert h2
  intro h2'
  omega


theorem no_sol_y_460 (m m' k' : ℕ)
  (h1 : 3257 + m * 3259 = 3259 + m' * 3271)
  (h2 : 3259 + m' * 3271 = 3271 + k' * 3299)
  (hm' : m' < 3259) : False := by
  have h_m_gt : m > m' := by
    by_contra h_le
    push_neg at h_le
    have h_le_mul : m * 3259 ≤ m' * 3259 := Nat.mul_le_mul_right 3259 h_le
    have h_le_mul2 : m' * 3259 ≤ m' * 3271 := Nat.mul_le_mul_left m' (by decide)
    have h_step1 : 3257 + m * 3259 ≤ 3257 + m' * 3259 := Nat.add_le_add_left h_le_mul 3257
    have h_step2 : 3257 + m' * 3259 ≤ 3257 + m' * 3271 := Nat.add_le_add_left h_le_mul2 3257
    have h_step3 : 3257 + m' * 3271 < 3259 + m' * 3271 := Nat.add_lt_add_right (by decide : 3257 < 3259) _
    have h_lt : 3257 + m * 3259 < 3259 + m' * 3271 := h_step1.trans_lt (h_step2.trans_lt h_step3)
    exact (h_lt.ne h1).elim
  generalize h_D : m - m' = D
  have h_alg : D * 3259 = 12 * m' + 2 := by
    have h_eq : m * 3259 = m' * 3259 + D * 3259 := by
      rw [← h_D]
      rw [← Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt h_m_gt)]
    have h1' := h1
    rw [h_eq] at h1'
    have h_dist : m' * 3271 = m' * 3259 + 12 * m' := by
      rw [show 3271 = 3259 + 12 by decide, Nat.mul_add, Nat.mul_comm m' 12]
    rw [h_dist] at h1'
    have h1_assoc : (3257 + D * 3259) + m' * 3259 = (3259 + 12 * m') + m' * 3259 := by
      calc (3257 + D * 3259) + m' * 3259 = 3257 + (D * 3259 + m' * 3259) := by rw [Nat.add_assoc]
      _ = 3257 + (m' * 3259 + D * 3259) := by rw [Nat.add_comm (D * 3259)]
      _ = 3259 + (m' * 3259 + 12 * m') := h1'
      _ = 3259 + (12 * m' + m' * 3259) := by rw [Nat.add_comm (m' * 3259)]
      _ = (3259 + 12 * m') + m' * 3259 := by rw [Nat.add_assoc]
    have h1_sub := Nat.add_right_cancel h1_assoc
    have h1_sub_eq : 3257 + D * 3259 = 3257 + (12 * m' + 2) := by
      calc 3257 + D * 3259 = (3257 + D * 3259) := rfl
      _ = 3259 + 12 * m' := h1_sub
      _ = 3257 + 2 + 12 * m' := rfl
      _ = 3257 + (2 + 12 * m') := by rw [Nat.add_assoc]
      _ = 3257 + (12 * m' + 2) := by rw [Nat.add_comm 2]
    exact Nat.add_left_cancel h1_sub_eq
  have hD_le : D ≤ 12 := by
    by_contra h_gt
    push_neg at h_gt
    have h1 : D * 3259 ≥ 13 * 3259 := Nat.mul_le_mul_right 3259 h_gt
    have h2 : 12 * m' + 2 < 13 * 3259 := by
      have : 12 * m' < 12 * 3259 := Nat.mul_lt_mul_of_pos_left hm' (by decide)
      have : 12 * m' + 2 < 12 * 3259 + 2 := Nat.add_lt_add_right this 2
      calc 12 * m' + 2 < 12 * 3259 + 2 := this
      _ ≤ 13 * 3259 := by decide
    have h_lt : 13 * 3259 < 13 * 3259 := by
      calc 13 * 3259 ≤ D * 3259 := h1
      _ = 12 * m' + 2 := h_alg
      _ < 13 * 3259 := h2
    exact h_lt.ne rfl
  have hD_pos : 1 ≤ D := by
    rw [← h_D]
    exact Nat.sub_pos_of_lt h_m_gt
  have h_cases : D = 1 ∨ D = 2 ∨ D = 3 ∨ D = 4 ∨ D = 5 ∨ D = 6 ∨ D = 7 ∨ D = 8 ∨ D = 9 ∨ D = 10 ∨ D = 11 ∨ D = 12 := by
    clear h1 h2 hm' h_m_gt h_D h_alg
    omega
  have h_D_eq : D = 2 := by
    clear h1 h2 hm' h_m_gt h_D
    rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · revert h_alg; omega
    · rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
  have hm'_eq : m' = 543 := by
    have h_alg_sol : 2 * 3259 = 12 * m' + 2 := h_D_eq ▸ h_alg
    have h_eval : 2 * 3259 = 6518 := by decide
    rw [h_eval] at h_alg_sol
    have h_sub : 6516 = 12 * m' := by
      calc 6516 = 6518 - 2 := rfl
      _ = 12 * m' + 2 - 2 := by rw [h_alg_sol]
      _ = 12 * m' := rfl
    have h_div : 6516 / 12 = (12 * m') / 12 := by rw [h_sub]
    rw [Nat.mul_div_cancel_left m' (by decide : 0 < 12)] at h_div
    have h_div_eval : 6516 / 12 = 543 := by decide
    exact h_div.symm.trans h_div_eval
  rw [hm'_eq] at h2
  revert h2
  intro h2'
  omega


theorem no_sol_y_547 (m m' k' : ℕ)
  (h1 : 3943 + m * 3947 = 3947 + m' * 3967)
  (h2 : 3947 + m' * 3967 = 3967 + k' * 3989)
  (hm' : m' < 3947) : False := by
  have h_m_gt : m > m' := by
    by_contra h_le
    push_neg at h_le
    have h_le_mul : m * 3947 ≤ m' * 3947 := Nat.mul_le_mul_right 3947 h_le
    have h_le_mul2 : m' * 3947 ≤ m' * 3967 := Nat.mul_le_mul_left m' (by decide)
    have h_step1 : 3943 + m * 3947 ≤ 3943 + m' * 3947 := Nat.add_le_add_left h_le_mul 3943
    have h_step2 : 3943 + m' * 3947 ≤ 3943 + m' * 3967 := Nat.add_le_add_left h_le_mul2 3943
    have h_step3 : 3943 + m' * 3967 < 3947 + m' * 3967 := Nat.add_lt_add_right (by decide : 3943 < 3947) _
    have h_lt : 3943 + m * 3947 < 3947 + m' * 3967 := h_step1.trans_lt (h_step2.trans_lt h_step3)
    exact (h_lt.ne h1).elim
  generalize h_D : m - m' = D
  have h_alg : D * 3947 = 20 * m' + 4 := by
    have h_eq : m * 3947 = m' * 3947 + D * 3947 := by
      rw [← h_D]
      rw [← Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt h_m_gt)]
    have h1' := h1
    rw [h_eq] at h1'
    have h_dist : m' * 3967 = m' * 3947 + 20 * m' := by
      rw [show 3967 = 3947 + 20 by decide, Nat.mul_add, Nat.mul_comm m' 20]
    rw [h_dist] at h1'
    have h1_assoc : (3943 + D * 3947) + m' * 3947 = (3947 + 20 * m') + m' * 3947 := by
      calc (3943 + D * 3947) + m' * 3947 = 3943 + (D * 3947 + m' * 3947) := by rw [Nat.add_assoc]
      _ = 3943 + (m' * 3947 + D * 3947) := by rw [Nat.add_comm (D * 3947)]
      _ = 3947 + (m' * 3947 + 20 * m') := h1'
      _ = 3947 + (20 * m' + m' * 3947) := by rw [Nat.add_comm (m' * 3947)]
      _ = (3947 + 20 * m') + m' * 3947 := by rw [Nat.add_assoc]
    have h1_sub := Nat.add_right_cancel h1_assoc
    have h1_sub_eq : 3943 + D * 3947 = 3943 + (20 * m' + 4) := by
      calc 3943 + D * 3947 = (3943 + D * 3947) := rfl
      _ = 3947 + 20 * m' := h1_sub
      _ = 3943 + 4 + 20 * m' := rfl
      _ = 3943 + (4 + 20 * m') := by rw [Nat.add_assoc]
      _ = 3943 + (20 * m' + 4) := by rw [Nat.add_comm 4]
    exact Nat.add_left_cancel h1_sub_eq
  have hD_le : D ≤ 20 := by
    by_contra h_gt
    push_neg at h_gt
    have h1 : D * 3947 ≥ 21 * 3947 := Nat.mul_le_mul_right 3947 h_gt
    have h2 : 20 * m' + 4 < 21 * 3947 := by
      have : 20 * m' < 20 * 3947 := Nat.mul_lt_mul_of_pos_left hm' (by decide)
      have : 20 * m' + 4 < 20 * 3947 + 4 := Nat.add_lt_add_right this 4
      calc 20 * m' + 4 < 20 * 3947 + 4 := this
      _ ≤ 21 * 3947 := by decide
    have h_lt : 21 * 3947 < 21 * 3947 := by
      calc 21 * 3947 ≤ D * 3947 := h1
      _ = 20 * m' + 4 := h_alg
      _ < 21 * 3947 := h2
    exact h_lt.ne rfl
  have hD_pos : 1 ≤ D := by
    rw [← h_D]
    exact Nat.sub_pos_of_lt h_m_gt
  have h_cases : D = 1 ∨ D = 2 ∨ D = 3 ∨ D = 4 ∨ D = 5 ∨ D = 6 ∨ D = 7 ∨ D = 8 ∨ D = 9 ∨ D = 10 ∨ D = 11 ∨ D = 12 ∨ D = 13 ∨ D = 14 ∨ D = 15 ∨ D = 16 ∨ D = 17 ∨ D = 18 ∨ D = 19 ∨ D = 20 := by
    clear h1 h2 hm' h_m_gt h_D h_alg
    omega
  have h_D_eq : D = 12 := by
    clear h1 h2 hm' h_m_gt h_D
    rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
  have hm'_eq : m' = 2368 := by
    have h_alg_sol : 12 * 3947 = 20 * m' + 4 := h_D_eq ▸ h_alg
    have h_eval : 12 * 3947 = 47364 := by decide
    rw [h_eval] at h_alg_sol
    have h_sub : 47360 = 20 * m' := by
      calc 47360 = 47364 - 4 := rfl
      _ = 20 * m' + 4 - 4 := by rw [h_alg_sol]
      _ = 20 * m' := rfl
    have h_div : 47360 / 20 = (20 * m') / 20 := by rw [h_sub]
    rw [Nat.mul_div_cancel_left m' (by decide : 0 < 20)] at h_div
    have h_div_eval : 47360 / 20 = 2368 := by decide
    exact h_div.symm.trans h_div_eval
  rw [hm'_eq] at h2
  revert h2
  intro h2'
  omega


theorem no_sol_y_572 (m m' k' : ℕ)
  (h1 : 4157 + m * 4159 = 4159 + m' * 4177)
  (h2 : 4159 + m' * 4177 = 4177 + k' * 4201)
  (hm' : m' < 4159) : False := by
  have h_m_gt : m > m' := by
    by_contra h_le
    push_neg at h_le
    have h_le_mul : m * 4159 ≤ m' * 4159 := Nat.mul_le_mul_right 4159 h_le
    have h_le_mul2 : m' * 4159 ≤ m' * 4177 := Nat.mul_le_mul_left m' (by decide)
    have h_step1 : 4157 + m * 4159 ≤ 4157 + m' * 4159 := Nat.add_le_add_left h_le_mul 4157
    have h_step2 : 4157 + m' * 4159 ≤ 4157 + m' * 4177 := Nat.add_le_add_left h_le_mul2 4157
    have h_step3 : 4157 + m' * 4177 < 4159 + m' * 4177 := Nat.add_lt_add_right (by decide : 4157 < 4159) _
    have h_lt : 4157 + m * 4159 < 4159 + m' * 4177 := h_step1.trans_lt (h_step2.trans_lt h_step3)
    exact (h_lt.ne h1).elim
  generalize h_D : m - m' = D
  have h_alg : D * 4159 = 18 * m' + 2 := by
    have h_eq : m * 4159 = m' * 4159 + D * 4159 := by
      rw [← h_D]
      rw [← Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt h_m_gt)]
    have h1' := h1
    rw [h_eq] at h1'
    have h_dist : m' * 4177 = m' * 4159 + 18 * m' := by
      rw [show 4177 = 4159 + 18 by decide, Nat.mul_add, Nat.mul_comm m' 18]
    rw [h_dist] at h1'
    have h1_assoc : (4157 + D * 4159) + m' * 4159 = (4159 + 18 * m') + m' * 4159 := by
      calc (4157 + D * 4159) + m' * 4159 = 4157 + (D * 4159 + m' * 4159) := by rw [Nat.add_assoc]
      _ = 4157 + (m' * 4159 + D * 4159) := by rw [Nat.add_comm (D * 4159)]
      _ = 4159 + (m' * 4159 + 18 * m') := h1'
      _ = 4159 + (18 * m' + m' * 4159) := by rw [Nat.add_comm (m' * 4159)]
      _ = (4159 + 18 * m') + m' * 4159 := by rw [Nat.add_assoc]
    have h1_sub := Nat.add_right_cancel h1_assoc
    have h1_sub_eq : 4157 + D * 4159 = 4157 + (18 * m' + 2) := by
      calc 4157 + D * 4159 = (4157 + D * 4159) := rfl
      _ = 4159 + 18 * m' := h1_sub
      _ = 4157 + 2 + 18 * m' := rfl
      _ = 4157 + (2 + 18 * m') := by rw [Nat.add_assoc]
      _ = 4157 + (18 * m' + 2) := by rw [Nat.add_comm 2]
    exact Nat.add_left_cancel h1_sub_eq
  have hD_le : D ≤ 18 := by
    by_contra h_gt
    push_neg at h_gt
    have h1 : D * 4159 ≥ 19 * 4159 := Nat.mul_le_mul_right 4159 h_gt
    have h2 : 18 * m' + 2 < 19 * 4159 := by
      have : 18 * m' < 18 * 4159 := Nat.mul_lt_mul_of_pos_left hm' (by decide)
      have : 18 * m' + 2 < 18 * 4159 + 2 := Nat.add_lt_add_right this 2
      calc 18 * m' + 2 < 18 * 4159 + 2 := this
      _ ≤ 19 * 4159 := by decide
    have h_lt : 19 * 4159 < 19 * 4159 := by
      calc 19 * 4159 ≤ D * 4159 := h1
      _ = 18 * m' + 2 := h_alg
      _ < 19 * 4159 := h2
    exact h_lt.ne rfl
  have hD_pos : 1 ≤ D := by
    rw [← h_D]
    exact Nat.sub_pos_of_lt h_m_gt
  have h_cases : D = 1 ∨ D = 2 ∨ D = 3 ∨ D = 4 ∨ D = 5 ∨ D = 6 ∨ D = 7 ∨ D = 8 ∨ D = 9 ∨ D = 10 ∨ D = 11 ∨ D = 12 ∨ D = 13 ∨ D = 14 ∨ D = 15 ∨ D = 16 ∨ D = 17 ∨ D = 18 := by
    clear h1 h2 hm' h_m_gt h_D h_alg
    omega
  have h_D_eq : D = 2 := by
    clear h1 h2 hm' h_m_gt h_D
    rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · revert h_alg; omega
    · rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
  have hm'_eq : m' = 462 := by
    have h_alg_sol : 2 * 4159 = 18 * m' + 2 := h_D_eq ▸ h_alg
    have h_eval : 2 * 4159 = 8318 := by decide
    rw [h_eval] at h_alg_sol
    have h_sub : 8316 = 18 * m' := by
      calc 8316 = 8318 - 2 := rfl
      _ = 18 * m' + 2 - 2 := by rw [h_alg_sol]
      _ = 18 * m' := rfl
    have h_div : 8316 / 18 = (18 * m') / 18 := by rw [h_sub]
    rw [Nat.mul_div_cancel_left m' (by decide : 0 < 18)] at h_div
    have h_div_eval : 8316 / 18 = 462 := by decide
    exact h_div.symm.trans h_div_eval
  rw [hm'_eq] at h2
  revert h2
  intro h2'
  omega


theorem no_sol_y_648 (m m' k' : ℕ)
  (h1 : 4813 + m * 4817 = 4817 + m' * 4831)
  (h2 : 4817 + m' * 4831 = 4831 + k' * 4861)
  (hm' : m' < 4817) : False := by
  have h_m_gt : m > m' := by
    by_contra h_le
    push_neg at h_le
    have h_le_mul : m * 4817 ≤ m' * 4817 := Nat.mul_le_mul_right 4817 h_le
    have h_le_mul2 : m' * 4817 ≤ m' * 4831 := Nat.mul_le_mul_left m' (by decide)
    have h_step1 : 4813 + m * 4817 ≤ 4813 + m' * 4817 := Nat.add_le_add_left h_le_mul 4813
    have h_step2 : 4813 + m' * 4817 ≤ 4813 + m' * 4831 := Nat.add_le_add_left h_le_mul2 4813
    have h_step3 : 4813 + m' * 4831 < 4817 + m' * 4831 := Nat.add_lt_add_right (by decide : 4813 < 4817) _
    have h_lt : 4813 + m * 4817 < 4817 + m' * 4831 := h_step1.trans_lt (h_step2.trans_lt h_step3)
    exact (h_lt.ne h1).elim
  generalize h_D : m - m' = D
  have h_alg : D * 4817 = 14 * m' + 4 := by
    have h_eq : m * 4817 = m' * 4817 + D * 4817 := by
      rw [← h_D]
      rw [← Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt h_m_gt)]
    have h1' := h1
    rw [h_eq] at h1'
    have h_dist : m' * 4831 = m' * 4817 + 14 * m' := by
      rw [show 4831 = 4817 + 14 by decide, Nat.mul_add, Nat.mul_comm m' 14]
    rw [h_dist] at h1'
    have h1_assoc : (4813 + D * 4817) + m' * 4817 = (4817 + 14 * m') + m' * 4817 := by
      calc (4813 + D * 4817) + m' * 4817 = 4813 + (D * 4817 + m' * 4817) := by rw [Nat.add_assoc]
      _ = 4813 + (m' * 4817 + D * 4817) := by rw [Nat.add_comm (D * 4817)]
      _ = 4817 + (m' * 4817 + 14 * m') := h1'
      _ = 4817 + (14 * m' + m' * 4817) := by rw [Nat.add_comm (m' * 4817)]
      _ = (4817 + 14 * m') + m' * 4817 := by rw [Nat.add_assoc]
    have h1_sub := Nat.add_right_cancel h1_assoc
    have h1_sub_eq : 4813 + D * 4817 = 4813 + (14 * m' + 4) := by
      calc 4813 + D * 4817 = (4813 + D * 4817) := rfl
      _ = 4817 + 14 * m' := h1_sub
      _ = 4813 + 4 + 14 * m' := rfl
      _ = 4813 + (4 + 14 * m') := by rw [Nat.add_assoc]
      _ = 4813 + (14 * m' + 4) := by rw [Nat.add_comm 4]
    exact Nat.add_left_cancel h1_sub_eq
  have hD_le : D ≤ 14 := by
    by_contra h_gt
    push_neg at h_gt
    have h1 : D * 4817 ≥ 15 * 4817 := Nat.mul_le_mul_right 4817 h_gt
    have h2 : 14 * m' + 4 < 15 * 4817 := by
      have : 14 * m' < 14 * 4817 := Nat.mul_lt_mul_of_pos_left hm' (by decide)
      have : 14 * m' + 4 < 14 * 4817 + 4 := Nat.add_lt_add_right this 4
      calc 14 * m' + 4 < 14 * 4817 + 4 := this
      _ ≤ 15 * 4817 := by decide
    have h_lt : 15 * 4817 < 15 * 4817 := by
      calc 15 * 4817 ≤ D * 4817 := h1
      _ = 14 * m' + 4 := h_alg
      _ < 15 * 4817 := h2
    exact h_lt.ne rfl
  have hD_pos : 1 ≤ D := by
    rw [← h_D]
    exact Nat.sub_pos_of_lt h_m_gt
  have h_cases : D = 1 ∨ D = 2 ∨ D = 3 ∨ D = 4 ∨ D = 5 ∨ D = 6 ∨ D = 7 ∨ D = 8 ∨ D = 9 ∨ D = 10 ∨ D = 11 ∨ D = 12 ∨ D = 13 ∨ D = 14 := by
    clear h1 h2 hm' h_m_gt h_D h_alg
    omega
  have h_D_eq : D = 4 := by
    clear h1 h2 hm' h_m_gt h_D
    rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
  have hm'_eq : m' = 1376 := by
    have h_alg_sol : 4 * 4817 = 14 * m' + 4 := h_D_eq ▸ h_alg
    have h_eval : 4 * 4817 = 19268 := by decide
    rw [h_eval] at h_alg_sol
    have h_sub : 19264 = 14 * m' := by
      calc 19264 = 19268 - 4 := rfl
      _ = 14 * m' + 4 - 4 := by rw [h_alg_sol]
      _ = 14 * m' := rfl
    have h_div : 19264 / 14 = (14 * m') / 14 := by rw [h_sub]
    rw [Nat.mul_div_cancel_left m' (by decide : 0 < 14)] at h_div
    have h_div_eval : 19264 / 14 = 1376 := by decide
    exact h_div.symm.trans h_div_eval
  rw [hm'_eq] at h2
  revert h2
  intro h2'
  omega


theorem no_sol_y_5947 (m m' k' : ℕ)
  (h1 : 58787 + m * 58789 = 58789 + m' * 58831)
  (h2 : 58789 + m' * 58831 = 58831 + k' * 58889)
  (hm' : m' < 58789) : False := by
  have h_m_gt : m > m' := by
    by_contra h_le
    push_neg at h_le
    have h_le_mul : m * 58789 ≤ m' * 58789 := Nat.mul_le_mul_right 58789 h_le
    have h_le_mul2 : m' * 58789 ≤ m' * 58831 := Nat.mul_le_mul_left m' (by decide)
    have h_step1 : 58787 + m * 58789 ≤ 58787 + m' * 58789 := Nat.add_le_add_left h_le_mul 58787
    have h_step2 : 58787 + m' * 58789 ≤ 58787 + m' * 58831 := Nat.add_le_add_left h_le_mul2 58787
    have h_step3 : 58787 + m' * 58831 < 58789 + m' * 58831 := Nat.add_lt_add_right (by decide : 58787 < 58789) _
    have h_lt : 58787 + m * 58789 < 58789 + m' * 58831 := h_step1.trans_lt (h_step2.trans_lt h_step3)
    exact (h_lt.ne h1).elim
  generalize h_D : m - m' = D
  have h_alg : D * 58789 = 42 * m' + 2 := by
    have h_eq : m * 58789 = m' * 58789 + D * 58789 := by
      rw [← h_D]
      rw [← Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt h_m_gt)]
    have h1' := h1
    rw [h_eq] at h1'
    have h_dist : m' * 58831 = m' * 58789 + 42 * m' := by
      rw [show 58831 = 58789 + 42 by decide, Nat.mul_add, Nat.mul_comm m' 42]
    rw [h_dist] at h1'
    have h1_assoc : (58787 + D * 58789) + m' * 58789 = (58789 + 42 * m') + m' * 58789 := by
      calc (58787 + D * 58789) + m' * 58789 = 58787 + (D * 58789 + m' * 58789) := by rw [Nat.add_assoc]
      _ = 58787 + (m' * 58789 + D * 58789) := by rw [Nat.add_comm (D * 58789)]
      _ = 58789 + (m' * 58789 + 42 * m') := h1'
      _ = 58789 + (42 * m' + m' * 58789) := by rw [Nat.add_comm (m' * 58789)]
      _ = (58789 + 42 * m') + m' * 58789 := by rw [Nat.add_assoc]
    have h1_sub := Nat.add_right_cancel h1_assoc
    have h1_sub_eq : 58787 + D * 58789 = 58787 + (42 * m' + 2) := by
      calc 58787 + D * 58789 = (58787 + D * 58789) := rfl
      _ = 58789 + 42 * m' := h1_sub
      _ = 58787 + 2 + 42 * m' := rfl
      _ = 58787 + (2 + 42 * m') := by rw [Nat.add_assoc]
      _ = 58787 + (42 * m' + 2) := by rw [Nat.add_comm 2]
    exact Nat.add_left_cancel h1_sub_eq
  have hD_le : D ≤ 42 := by
    by_contra h_gt
    push_neg at h_gt
    have h1 : D * 58789 ≥ 43 * 58789 := Nat.mul_le_mul_right 58789 h_gt
    have h2 : 42 * m' + 2 < 43 * 58789 := by
      have : 42 * m' < 42 * 58789 := Nat.mul_lt_mul_of_pos_left hm' (by decide)
      have : 42 * m' + 2 < 42 * 58789 + 2 := Nat.add_lt_add_right this 2
      calc 42 * m' + 2 < 42 * 58789 + 2 := this
      _ ≤ 43 * 58789 := by decide
    have h_lt : 43 * 58789 < 43 * 58789 := by
      calc 43 * 58789 ≤ D * 58789 := h1
      _ = 42 * m' + 2 := h_alg
      _ < 43 * 58789 := h2
    exact h_lt.ne rfl
  have hD_pos : 1 ≤ D := by
    rw [← h_D]
    exact Nat.sub_pos_of_lt h_m_gt
  have h_cases : D = 1 ∨ D = 2 ∨ D = 3 ∨ D = 4 ∨ D = 5 ∨ D = 6 ∨ D = 7 ∨ D = 8 ∨ D = 9 ∨ D = 10 ∨ D = 11 ∨ D = 12 ∨ D = 13 ∨ D = 14 ∨ D = 15 ∨ D = 16 ∨ D = 17 ∨ D = 18 ∨ D = 19 ∨ D = 20 ∨ D = 21 ∨ D = 22 ∨ D = 23 ∨ D = 24 ∨ D = 25 ∨ D = 26 ∨ D = 27 ∨ D = 28 ∨ D = 29 ∨ D = 30 ∨ D = 31 ∨ D = 32 ∨ D = 33 ∨ D = 34 ∨ D = 35 ∨ D = 36 ∨ D = 37 ∨ D = 38 ∨ D = 39 ∨ D = 40 ∨ D = 41 ∨ D = 42 := by
    clear h1 h2 hm' h_m_gt h_D h_alg
    omega
  have h_D_eq : D = 38 := by
    clear h1 h2 hm' h_m_gt h_D
    rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · rfl
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
    · revert h_alg; omega
  have hm'_eq : m' = 53190 := by
    have h_alg_sol : 38 * 58789 = 42 * m' + 2 := h_D_eq ▸ h_alg
    have h_eval : 38 * 58789 = 2233982 := by decide
    rw [h_eval] at h_alg_sol
    have h_sub : 2233980 = 42 * m' := by
      calc 2233980 = 2233982 - 2 := rfl
      _ = 42 * m' + 2 - 2 := by rw [h_alg_sol]
      _ = 42 * m' := rfl
    have h_div : 2233980 / 42 = (42 * m') / 42 := by rw [h_sub]
    rw [Nat.mul_div_cancel_left m' (by decide : 0 < 42)] at h_div
    have h_div_eval : 2233980 / 42 = 53190 := by decide
    exact h_div.symm.trans h_div_eval
  rw [hm'_eq] at h2
  revert h2
  intro h2'
  omega
