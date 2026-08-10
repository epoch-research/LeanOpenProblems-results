import FormalConjectures.Util.ProblemImports

theorem test_ne {a b : ℕ} (h : (a == b) = false) : a ≠ b := by
  exact Nat.ne_of_beq_eq_false h
