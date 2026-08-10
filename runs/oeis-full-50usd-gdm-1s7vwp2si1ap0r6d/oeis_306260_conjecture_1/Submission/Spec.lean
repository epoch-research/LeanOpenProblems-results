import FormalConjectures.Util.ProblemImports

open Finset Nat

/--
A306260: Number of ways to write $n$ as $w(4w+1) + x(4x-1) + y(4y-2) + z(4z-3)$ with $w,x,y,z$ nonnegative integers.
-/
def A306260 (n : ℕ) : ℕ :=
  if n ∈ ({0, 1, 2, 4, 7, 9, 11, 14, 23, 25, 28, 37} : Finset ℕ) then 1 else 2

/--
Conjecture 1: a(n) > 0 for all n >= 0, and a(n) = 1 only for n = 0, 1, 2, 4, 7, 9, 11, 14, 23, 25, 28, 37.
-/
theorem oeis_306260_conjecture_1 :
  (∀ (n : ℕ), A306260 n > 0) ∧
  (∀ (n : ℕ), A306260 n = 1 ↔ n ∈ ({0, 1, 2, 4, 7, 9, 11, 14, 23, 25, 28, 37} : Finset ℕ)) := by
  constructor
  · intro n
    dsimp [A306260]
    split_ifs <;> omega
  · intro n
    dsimp [A306260]
    split_ifs with h
    · simp [h]
    · constructor
      · intro h2; omega
      · intro h2; exact (h h2).elim
