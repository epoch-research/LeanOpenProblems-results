import FormalConjectures.Util.ProblemImports
open Finset

lemma div_mul_le_comm (A B C : ℕ) : A / B * C ≤ A * C / B := by
  by_cases hB : B = 0
  · subst hB; simp
  · have hB_pos : 0 < B := Nat.pos_of_ne_zero hB
    rw [Nat.le_div_iff_mul_le hB_pos]
    calc
      A / B * C * B = (A / B * B) * C := by ring
      _ ≤ A * C := Nat.mul_le_mul_right C (Nat.div_mul_le_self A B)

lemma odd_div_relation (H k : ℕ) (hk : k ≤ H) (hH : 3 ≤ H) :
    k ^ 2 / (2 * H + 1) + 1 ≥ k ^ 2 / (2 * H - 1) := by
  have h_sq : k ^ 2 ≤ H ^ 2 := Nat.pow_le_pow_left hk 2
  have hH_pos : 0 < 2 * H + 1 := by omega
  have h_div_le : k ^ 2 / (2 * H + 1) ≤ H ^ 2 / (2 * H + 1) := Nat.div_le_div_right h_sq
  have h_div_H : H ^ 2 / (2 * H + 1) * 2 ≤ H := by
    have h_mul : 2 * H ^ 2 ≤ H * (2 * H + 1) := by
      calc
        2 * H ^ 2 = 2 * H * H := by ring
        _ ≤ (2 * H + 1) * H := Nat.mul_le_mul_right H (by omega)
        _ = H * (2 * H + 1) := by ring
    have h_mul2 : 2 * H ^ 2 ≤ (2 * H + 1) * H := by
      rw [mul_comm (2 * H + 1) H]
      exact h_mul
    have h_div_le2 : 2 * H ^ 2 / (2 * H + 1) ≤ H := Nat.div_le_of_le_mul h_mul2
    have h_le_comm : H ^ 2 / (2 * H + 1) * 2 ≤ 2 * H ^ 2 / (2 * H + 1) := by
      have : H ^ 2 / (2 * H + 1) * 2 ≤ H ^ 2 * 2 / (2 * H + 1) := div_mul_le_comm (H ^ 2) (2 * H + 1) 2
      rw [mul_comm (H ^ 2) 2] at this
      exact this
    omega
  have h_X_bound : 2 * (k ^ 2 / (2 * H + 1)) ≤ H := by
    calc
      2 * (k ^ 2 / (2 * H + 1)) = k ^ 2 / (2 * H + 1) * 2 := by ring
      _ ≤ H ^ 2 / (2 * H + 1) * 2 := Nat.mul_le_mul_right 2 h_div_le
      _ ≤ H := h_div_H
  by_contra h_contra
  push_neg at h_contra
  have h_contra2 : k ^ 2 / (2 * H - 1) ≥ k ^ 2 / (2 * H + 1) + 2 := h_contra
  set B := 2 * H - 1
  set C := 2 * H + 1
  set X := k ^ 2 / C
  set Y := k ^ 2 / B
  have h_B_pos : 0 < B := by omega
  have h_C_pos : 0 < C := by omega
  have h_Y_eq : B * Y ≤ k ^ 2 := by
    have : Y * B ≤ k ^ 2 := Nat.div_mul_le_self (k ^ 2) B
    rw [mul_comm] at this
    exact this
  have h_X_eq : k ^ 2 < C * (X + 1) := by
    have : k ^ 2 % C < C := Nat.mod_lt _ (by omega)
    have h_div_add : k ^ 2 = X * C + k ^ 2 % C := by
      have h1 := (Nat.div_add_mod (k ^ 2) C).symm
      rw [mul_comm] at h1
      exact h1
    rw [h_div_add]
    have : X * C + k ^ 2 % C < C * (X + 1) := by
      have : C * (X + 1) = X * C + C := by ring
      rw [this]
      omega
    exact this
  have h_le_trans : B * Y < C * (X + 1) := by omega
  have h_mono : B * (X + 2) ≤ B * Y := Nat.mul_le_mul_left B h_contra2
  have h_lt : B * (X + 2) < C * (X + 1) := by omega
  have h_B_expand : B * (X + 2) = 2 * H * X + 4 * H - X - 2 := by
    have h_B : B = 2 * H - 1 := rfl
    rw [h_B]
    have h_sub : (2 * H - 1) * (X + 2) = 2 * H * (X + 2) - (X + 2) := by
      rw [Nat.sub_mul, one_mul]
    rw [h_sub]
    have h_sub2 : 2 * H * (X + 2) = 2 * H * X + 4 * H := by ring
    rw [h_sub2]
    omega
  have h_C_expand : C * (X + 1) = 2 * H * X + 2 * H + X + 1 := by
    have h_C : C = 2 * H + 1 := rfl
    rw [h_C]
    ring
  rw [h_B_expand, h_C_expand] at h_lt
  omega

lemma even_div_relation (H k : ℕ) (hk : k ≤ 2 * H) (hH : 4 ≤ H) :
    k ^ 2 / (4 * H) + 2 ≥ k ^ 2 / (4 * H - 4) := by
  have h_sq : k ^ 2 ≤ (2 * H) ^ 2 := Nat.pow_le_pow_left hk 2
  have h_sq_id : (2 * H) ^ 2 = 4 * H ^ 2 := by ring
  rw [h_sq_id] at h_sq
  have h_div_le : k ^ 2 / (4 * H) ≤ 4 * H ^ 2 / (4 * H) := Nat.div_le_div_right h_sq
  have h_div_H : 4 * H ^ 2 / (4 * H) ≤ H := by
    have h_mul : 4 * H ^ 2 = H * (4 * H) := by ring
    rw [h_mul]
    rw [Nat.mul_div_cancel _ (by omega)]
  have h_X_bound : k ^ 2 / (4 * H) ≤ H := by omega
  by_contra h_contra
  push_neg at h_contra
  have h_contra2 : k ^ 2 / (4 * H - 4) ≥ k ^ 2 / (4 * H) + 3 := h_contra
  set B := 4 * H - 4
  set C := 4 * H
  set X := k ^ 2 / C
  set Y := k ^ 2 / B
  have h_B_pos : 0 < B := by omega
  have h_C_pos : 0 < C := by omega
  have h_Y_eq : B * Y ≤ k ^ 2 := by
    have : Y * B ≤ k ^ 2 := Nat.div_mul_le_self (k ^ 2) B
    rw [mul_comm] at this
    exact this
  have h_X_eq : k ^ 2 < C * (X + 1) := by
    have : k ^ 2 % C < C := Nat.mod_lt _ (by omega)
    have h_div_add : k ^ 2 = X * C + k ^ 2 % C := by
      have h1 := (Nat.div_add_mod (k ^ 2) C).symm
      rw [mul_comm] at h1
      exact h1
    rw [h_div_add]
    have : X * C + k ^ 2 % C < C * (X + 1) := by
      have : C * (X + 1) = X * C + C := by ring
      rw [this]
      omega
    exact this
  have h_le_trans : B * Y < C * (X + 1) := by omega
  have h_mono : B * (X + 3) ≤ B * Y := Nat.mul_le_mul_left B h_contra2
  have h_lt : B * (X + 3) < C * (X + 1) := by omega
  have h_B_expand : B * (X + 3) = 4 * H * X + 12 * H - 4 * X - 12 := by
    have h_B : B = 4 * H - 4 := rfl
    rw [h_B]
    have h_sub : (4 * H - 4) * (X + 3) = 4 * H * (X + 3) - 4 * (X + 3) := by
      rw [Nat.sub_mul]
    rw [h_sub]
    have h_sub2 : 4 * H * (X + 3) = 4 * H * X + 12 * H := by ring
    rw [h_sub2]
    omega
  have h_C_expand : C * (X + 1) = 4 * H * X + 4 * H := by
    have h_C : C = 4 * H := rfl
    rw [h_C]
    ring
  rw [h_B_expand, h_C_expand] at h_lt
  omega

lemma div_add_one_ge (n k : ℕ) (hk : k ≤ n) (hn : 0 < n) :
    k ^ 2 / n ≤ k ^ 2 / (n + 1) + 1 := by
  have h_sq : k ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left hk 2
  have h_lt : k ^ 2 < n * (k ^ 2 / (n + 1) + 2) := by
    set X := k ^ 2 / (n + 1)
    have h_div_add : k ^ 2 = X * (n + 1) + k ^ 2 % (n + 1) := Nat.div_add_mod (k ^ 2) (n + 1)
    have h_mod_lt : k ^ 2 % (n + 1) < n + 1 := Nat.mod_lt _ (by omega)
    have h_X_lt : X < n := by
      have h_sq_lt : k ^ 2 < n * (n + 1) := by
        calc
          k ^ 2 ≤ n ^ 2 := h_sq
          _ < n * (n + 1) := by
            rw [sq]
            exact Nat.mul_lt_mul_of_pos_left (by omega) hn
      rw [Nat.div_lt_iff_lt_mul (by omega)] at h_sq_lt
      exact h_sq_lt
    rw [h_div_add]
    calc
      X * (n + 1) + k ^ 2 % (n + 1) < X * (n + 1) + (n + 1) := by omega
      _ = (X + 1) * (n + 1) := by ring
      _ = (X + 1) * n + (X + 1) := by ring
      _ < (X + 2) * n := by
        have : X + 1 ≤ n := by omega
        rw [add_mul, one_mul]
        omega
      _ = n * (X + 2) := by ring
  have h_div_lt : k ^ 2 / n < k ^ 2 / (n + 1) + 2 := by
    rw [Nat.div_lt_iff_lt_mul hn]
    exact h_lt
  omega
