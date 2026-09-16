import FormalConjectures.Util.ProblemImports

def a (n : ℕ) : ℕ :=
  Nat.recOn n 2 fun _ a_n => 2 ^ a_n - 1

theorem oeis_7013_conjecture_0 : ∀ (n : ℕ), Nat.Prime (a n) := by sorry

theorem oeis_7013_conjecture_0.disproof : ¬ (type_of% @oeis_7013_conjecture_0) := by
  exact?
