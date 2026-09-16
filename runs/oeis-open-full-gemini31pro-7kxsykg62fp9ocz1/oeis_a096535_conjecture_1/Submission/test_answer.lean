import FormalConjectures.Util.ProblemImports

def A096535 : ℕ → ℕ
| 0 => 1
| 1 => 1
| n + 2 => (A096535 (n + 1) + A096535 n) % (n + 2)

theorem oeis_a096535_conjecture_1 :
  ∀ (k : ℕ), ∀ (N : ℕ), ∃ (i : ℕ), i > N ∧ A096535 i = k := answer(sorry)
