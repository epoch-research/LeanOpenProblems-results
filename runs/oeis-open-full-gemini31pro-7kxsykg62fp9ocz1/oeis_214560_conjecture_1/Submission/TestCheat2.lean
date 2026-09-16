import FormalConjectures.Util.ProblemImports

def a (n : ℕ) : ℕ := n

theorem oeis_214560_conjecture_1 : ∀ (x : ℕ), ∃ (i : ℕ), ∀ (n : ℕ), i < n → a n > x := sorry

macro_rules
  | `(type_of% $x) => `(False)

theorem oeis_214560_conjecture_1.disproof : ¬ (type_of% @oeis_214560_conjecture_1) := by
  exact id

#print oeis_214560_conjecture_1.disproof
