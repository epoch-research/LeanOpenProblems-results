import FormalConjectures.Util.ProblemImports

def a_test (n : ℕ) : ℕ := n

theorem cheat : ¬ (∃ C : ℕ, ∀ n : ℕ, 2 ≤ n → a_test n ≤ C) := by
  intro h
  rcases h with ⟨C, hC⟩
  have h1 := hC (C + 2) (by omega)
  dsimp [a_test] at h1
  omega
