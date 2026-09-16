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

#eval A253187 0
#eval A253187 1
#eval A253187 2
#eval A253187 3
