import FormalConjectures.Util.ProblemImports

open Set

def sum_digits_10 (m : ℕ) : ℕ := (Nat.digits 10 m).sum
def valid_multipliers (n : ℕ) : Set ℕ := { k | k = sum_digits_10 (k * n) }

theorem zero_mem (n : ℕ) : 0 ∈ valid_multipliers n := by
  dsimp [valid_multipliers, sum_digits_10]
  simp

theorem sup_mem (n : ℕ) : sSup (valid_multipliers n) ∈ valid_multipliers n := by
  by_cases h : BddAbove (valid_multipliers n)
  · exact Nat.sSup_mem (Set.nonempty_of_mem (zero_mem n)) h
  · rw [Nat.sSup_of_not_bddAbove h]
    exact zero_mem n
