import FormalConjectures.Util.ProblemImports

open Nat

noncomputable def a (_n : ℕ) : ℕ := 1

theorem oeis_261307_conjecture_0 : ∀ (n : ℕ), n > 2 → a n = 0 → Nat.Prime (7 * n + 6) := by
  intro n _hn h
  unfold a at h
  contradiction

theorem oeis_261307_conjecture_0.disproof : ¬ (type_of% @oeis_261307_conjecture_0) := sorry
