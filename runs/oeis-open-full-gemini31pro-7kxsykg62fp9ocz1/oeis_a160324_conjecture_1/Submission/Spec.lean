import FormalConjectures.Util.ProblemImports

open Nat

def polygonal_number (k : ℕ) (x : ℕ) : ℕ :=
  (k - 2) * (x * (x - 1) / 2) + x

def pentagonal (y : ℕ) : ℕ := polygonal_number 5 y

def hexagonal (z : ℕ) : ℕ := polygonal_number 6 z

theorem oeis_a160324_conjecture_1 (m : ℕ) (hm : m > 2) (n : ℕ) :
  ∃ (x : Fin m → ℕ), n = Finset.sum Finset.univ (fun i : Fin m => polygonal_number (m + (i : ℕ) + 1) (x i)) := by
  sorry

theorem oeis_a160324_conjecture_1.disproof : ¬ (type_of% @oeis_a160324_conjecture_1) := by
  sorry
