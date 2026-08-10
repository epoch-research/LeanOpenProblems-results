import FormalConjectures.Util.ProblemImports

open Nat

lemma squares_mod_four (a : ℕ) : a * a % 4 = 0 ∨ a * a % 4 = 1 := by
  rcases Nat.mod_two_eq_zero_or_one a with h | h
  · have : a = 2 * (a / 2) := by omega
    rw [this]
    left
    have h1 : (2 * (a / 2)) * (2 * (a / 2)) = 4 * ((a / 2) * (a / 2)) := by ring
    rw [h1]
    rw [Nat.mul_mod_right]
  · have : a = 2 * (a / 2) + 1 := by omega
    rw [this]
    right
    have h1 : (2 * (a / 2) + 1) * (2 * (a / 2) + 1) = 4 * ((a / 2) * (a / 2) + (a / 2)) + 1 := by ring
    rw [h1]
    rw [Nat.add_mod]
    rw [Nat.mul_mod_right]



