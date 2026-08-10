import FormalConjectures.Util.ProblemImports
import Mathlib.Data.Nat.Prime.Nth

open BigOperators Nat Int

example : a 3 = 13 := by
  unfold a
  dsimp
  rw [nth_prime_two_eq_five]
  rfl
