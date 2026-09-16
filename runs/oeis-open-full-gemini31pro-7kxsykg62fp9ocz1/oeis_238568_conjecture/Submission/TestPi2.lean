import FormalConjectures.Util.ProblemImports

open Nat

noncomputable def pi_fn (n : ℕ) : ℕ :=
  Nat.card {p // Nat.Prime p ∧ p ≤ n}

lemma pi_fn_two : pi_fn 2 = 1 := by
  sorry
