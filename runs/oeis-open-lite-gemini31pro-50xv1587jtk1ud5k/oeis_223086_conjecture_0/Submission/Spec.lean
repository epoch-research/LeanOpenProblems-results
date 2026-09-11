import FormalConjectures.Util.ProblemImports

open Nat

def A006368_map (k : ℕ) : ℕ :=
  if k % 2 = 0 then (3 * k) / 2
  else if k % 4 = 1 then (3 * k + 1) / 4
  else (3 * k - 1) / 4

def a (n : ℕ) : ℕ :=
  Nat.iterate A006368_map (n - 1) 64

theorem oeis_223086_conjecture_0 :
  ∀ (i j : ℕ), 0 < i → 0 < j → a i = a j → i = j := by sorry

theorem oeis_223086_conjecture_0.disproof : ¬ (∀ (i j : ℕ), 0 < i → 0 < j → a i = a j → i = j) := by sorry
