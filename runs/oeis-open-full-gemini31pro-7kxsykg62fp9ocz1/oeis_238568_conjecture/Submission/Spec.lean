import FormalConjectures.Util.ProblemImports

open Nat Finset

noncomputable def pi_fn (n : ℕ) : ℕ :=
  Nat.card {p // Nat.Prime p ∧ p ≤ n}

noncomputable def a (n : ℕ) : ℕ :=
  Finset.card $ Finset.filter (fun k : ℕ =>
    Nat.Prime (Nat.pow n 2 - pi_fn (k * n))
  ) (Finset.Ico 1 n)

def A238568_special_set : Set ℕ := {2, 3, 4, 8, 10, 24, 41}

theorem oeis_238568_conjecture :
  (∀ (n : ℕ), 1 < n → 0 < a n) ∧
  (∀ (n : ℕ), a n = 1 ↔ n ∈ A238568_special_set) :=
by sorry

theorem oeis_238568_conjecture.disproof : ¬ (type_of% @oeis_238568_conjecture) := by
  sorry
