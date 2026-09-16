import FormalConjectures.Util.ProblemImports

open Nat Finset

noncomputable def a (n : ℕ) : ℕ := 0

theorem oeis_A265710_conjecture :
  ∀ n : ℕ, n > 1 → (a n = 2 ↔ n = 14 ∨ n = 244 ∨ n = 494 ∨ n = 45994) := by
  sorry

theorem oeis_A265710_conjecture.disproof : ¬ (type_of% @oeis_A265710_conjecture) := by
  intro h
  have h14 := h 14 (by decide)
  dsimp [a] at h14
  revert h14
  decide
