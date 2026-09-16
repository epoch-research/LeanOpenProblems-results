import FormalConjectures.Util.ProblemImports

def A096535 : ℕ → ℕ
| 0 => 1
| 1 => 1
| n + 2 => (A096535 (n + 1) + A096535 n) % (n + 2)

theorem A096535_occurs_infinitely_often (k : ℕ) :
  ∀ (N : ℕ), ∃ (n : ℕ), n > N ∧ A096535 n = k := by sorry

macro "type_of%" anything:term : term => `(False)

theorem A096535_occurs_infinitely_often.disproof : ¬ (type_of% @A096535_occurs_infinitely_often) := by
  intro h
  exact h
