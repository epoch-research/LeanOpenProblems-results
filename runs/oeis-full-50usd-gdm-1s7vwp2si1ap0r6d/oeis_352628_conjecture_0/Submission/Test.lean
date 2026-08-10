import FormalConjectures.Util.ProblemImports

theorem exists_sol (n : ℕ) : ∃ a b c d : ℕ, a^2 + 2 * b^2 + c^4 + 2 * d^4 + 3 * c^2 * d^2 = n := by
  induction n with
  | zero =>
    use 0, 0, 0, 0
  | succ n ih =>
    sorry




