import FormalConjectures.Util.ProblemImports

open Nat

lemma chinese_remainder_helper (r : ℕ) (h3 : r % 3 = 2) (h5 : r % 5 = 4) (h16 : r % 16 = 1) (h_lt : r < 480) : r % 32 = 17 ∨ r = 449 := by
  obtain ⟨k, hk⟩ : ∃ k, r = 16 * k + 1 := ⟨r / 16, by omega⟩
  have h_k_lt : k < 30 := by omega
  revert h_k_lt h3 h5 h16
  rcases k with _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|k
  all_goals (try rw [hk])
  all_goals (try decide)
  all_goals (try intro h_k_lt h3 h5 h16)
  all_goals (try exfalso)
  all_goals (try omega)

lemma chinese_remainder_X (X : ℕ) (h3 : X % 3 = 2) (h5 : X % 5 = 4) (h16 : X % 16 = 1) : X % 32 = 17 ∨ X % 480 = 449 := by
  have h_eq : X = 480 * (X / 480) + X % 480 := (Nat.div_add_mod X 480).symm
  have h3_r : X % 480 % 3 = 2 := by
    have : (480 * (X / 480) + X % 480) % 3 = X % 480 % 3 := by
      rw [Nat.add_mod]
      have h_mul : (480 * (X / 480)) % 3 = 0 := by
        rw [Nat.mul_mod]
        have : 480 % 3 = 0 := rfl
        rw [this, zero_mul]
        rfl
      rw [h_mul, zero_add, Nat.mod_mod]
    rw [← this]
    rw [← h_eq]
    exact h3
  have h5_r : X % 480 % 5 = 4 := by
    have : (480 * (X / 480) + X % 480) % 5 = X % 480 % 5 := by
      rw [Nat.add_mod]
      have h_mul : (480 * (X / 480)) % 5 = 0 := by
        rw [Nat.mul_mod]
        have : 480 % 5 = 0 := rfl
        rw [this, zero_mul]
        rfl
      rw [h_mul, zero_add, Nat.mod_mod]
    rw [← this]
    rw [← h_eq]
    exact h5
  have h16_r : X % 480 % 16 = 1 := by
    have : (480 * (X / 480) + X % 480) % 16 = X % 480 % 16 := by
      rw [Nat.add_mod]
      have h_mul : (480 * (X / 480)) % 16 = 0 := by
        rw [Nat.mul_mod]
        have : 480 % 16 = 0 := rfl
        rw [this, zero_mul]
        rfl
      rw [h_mul, zero_add, Nat.mod_mod]
    rw [← this]
    rw [← h_eq]
    exact h16
  have h_lt : X % 480 < 480 := Nat.mod_lt _ (by decide)
  have h_cases : X % 480 % 32 = 17 ∨ X % 480 = 449 := chinese_remainder_helper (X % 480) h3_r h5_r h16_r h_lt
  rcases h_cases with h17 | h449
  · left
    have : X % 32 = X % 480 % 32 := by
      conv_lhs => rw [h_eq]
      rw [Nat.add_mod]
      have h_mul : (480 * (X / 480)) % 32 = 0 := by
        rw [Nat.mul_mod]
        have : 480 % 32 = 0 := rfl
        rw [this, zero_mul]
        rfl
      rw [h_mul, zero_add, Nat.mod_mod]
    rw [this, h17]
  · right
    exact h449
