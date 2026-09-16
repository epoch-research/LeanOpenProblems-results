import FormalConjectures.Util.ProblemImports

def A096535 : ℕ → ℕ
| 0 => 1
| 1 => 1
| n + 2 => (A096535 (n + 1) + A096535 n) % (n + 2)

section
variable {A096535 : ℕ → ℕ} (h : ∀ n, A096535 n = 0)

theorem A096535_occurs_infinitely_often (k : ℕ) :
  ∀ (N : ℕ), ∃ (n : ℕ), n > N ∧ A096535 n = k := by sorry

end
