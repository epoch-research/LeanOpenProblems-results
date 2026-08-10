import FormalConjectures.Util.ProblemImports
open Finset

lemma div_sq_sub_self (n k : ℕ) (hn : 0 < n) (hk : 2 * k ≤ n) : (n - k) ^ 2 / n = n - 2 * k + k ^ 2 / n := sorry

lemma div_sq_sub_self_mod_two (H k : ℕ) (hk : k ≤ H) (hH : 0 < H) :
    ((2 * H - k) ^ 2 / (2 * H)) % 2 = (k ^ 2 / (2 * H)) % 2 := by
  by_cases hk0 : k = 0
  · subst hk0
    have : (2 * H - 0) = 2 * H := by omega
    rw [this]
    have h_div : (2 * H) ^ 2 / (2 * H) = 2 * H := by
      have : (2 * H) ^ 2 = (2 * H) * (2 * H) := by ring
      rw [this]
      exact Nat.mul_div_cancel_left _ (by omega)
    rw [h_div]
    have : (0 : ℕ) ^ 2 / (2 * H) % 2 = 0 := by simp
    rw [this]
    exact Nat.mul_mod_right 2 H
  · have hj_le : 2 * k ≤ 2 * H := by omega
    have h_sub := div_sq_sub_self (2 * H) k (by omega) hj_le
    rw [h_sub]
    omega
