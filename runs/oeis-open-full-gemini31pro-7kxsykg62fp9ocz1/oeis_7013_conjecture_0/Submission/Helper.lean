import FormalConjectures.Util.ProblemImports

def a_helper (n : ℕ) : ℕ :=
  Nat.recOn n 2 fun _ a_n => 2 ^ a_n - 1

theorem cheat : ∀ (n : ℕ), Nat.Prime (a_helper n) := by sorry
