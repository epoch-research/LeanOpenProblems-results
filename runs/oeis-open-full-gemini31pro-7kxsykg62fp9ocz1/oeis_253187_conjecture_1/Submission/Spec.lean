import FormalConjectures.Util.ProblemImports

open Nat Finset

def pentagonal_first (x : ℕ) : ℕ := (x * (3 * x - 1)) / 2
def pentagonal_second (y : ℕ) : ℕ := (y * (3 * y + 1)) / 2
def count_generalized_decagonal_index (r : ℕ) : ℕ :=
  if Nat.sqrt (16 * r + 9) * Nat.sqrt (16 * r + 9) = 16 * r + 9 then 1 else 0

def A253187 (n : ℕ) : ℕ :=
  (range (n + 1)).sum fun x =>
    (range (n + 1)).sum fun y =>
      let sum_pent := pentagonal_first x + pentagonal_second y
      if sum_pent <= n then
        count_generalized_decagonal_index (n - sum_pent)
      else
        0

theorem oeis_253187_conjecture_1 : ∀ (n : ℕ), A253187 n > 0 := by
  sorry

theorem oeis_253187_conjecture_1.disproof : ¬ (type_of% @oeis_253187_conjecture_1) := by
  sorry
