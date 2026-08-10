import Mathlib

lemma div_mod_two_eq_mod_div (H X : ℕ) (hH : 0 < H) :
    (X / (2 * H)) % 2 = (X % (4 * H)) / (2 * H) := by
  have hH2 : 0 < 2 * H := by omega
  have h_eq : X / (2 * H) = X % (4 * H) / (2 * H) + (X / (4 * H)) * 2 := by
    have h3 : X = X % (4 * H) + (X / (4 * H) * 2) * (2 * H) := by
      have h1 : X = X % (4 * H) + (4 * H) * (X / (4 * H)) := (Nat.mod_add_div X (4 * H)).symm
      have h_mul : (4 * H) * (X / (4 * H)) = (X / (4 * H) * 2) * (2 * H) := by ring
      omega
    nth_rw 1 [h3]
    rw [Nat.add_mul_div_right _ _ hH2]
  have h_lt : (X % (4 * H)) / (2 * H) < 2 := by
    apply Nat.div_lt_of_lt_mul
    have h_lt_mul : X % (4 * H) < 4 * H := Nat.mod_lt X (by omega)
    have : 2 * H * 2 = 4 * H := by ring
    omega
  rw [h_eq]
  rw [Nat.add_mul_mod_self_right]
  rw [Nat.mod_eq_of_lt h_lt]

def A048153 (n : ℕ) : ℕ := sorry

lemma Q_bound_implies_A048153_bound (n : ℕ) (h_n : 2 ≤ n)
    (h_Q : (n - 1) * (n - 2) ≤ 3 * (∑ k ∈ range n, k ^ 2 / n)) :
    A048153 n ≤ n * (n - 1) / 2 := sorry

lemma S_bound_inductive (n : ℕ) :
    3 * (∑ k ∈ range n, k ^ 2 / n) ≥ (n - 1) * (n - 2) := sorry

lemma a048153_odd_le (H : ℕ) : A048153 (2 * H + 1) ≤ H * (2 * H + 1) := by
  by_cases hH : H = 0
  · subst hH; simp
  · have h_n : 2 ≤ 2 * H + 1 := by omega
    have h_Q := S_bound_inductive (2 * H + 1)
    have h_le := Q_bound_implies_A048153_bound (2 * H + 1) h_n (by
      have h_eq : (2 * H + 1 - 1) * (2 * H + 1 - 2) = (2 * H) * (2 * H - 1) := by
        rcases H with _ | H
        · omega
        · rfl
      rw [h_eq]
      exact h_Q)
    have h_bound : (2 * H + 1) * (2 * H + 1 - 1) / 2 = H * (2 * H + 1) := by
      have : 2 * H + 1 - 1 = 2 * H := by omega
      rw [this]
      have : (2 * H + 1) * (2 * H) = 2 * (H * (2 * H + 1)) := by ring
      rw [this]
      exact Nat.mul_div_cancel_left _ (by omega)
    rw [h_bound] at h_le
    exact h_le
