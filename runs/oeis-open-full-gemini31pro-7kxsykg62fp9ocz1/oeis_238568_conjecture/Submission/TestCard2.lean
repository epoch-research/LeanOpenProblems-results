import FormalConjectures.Util.ProblemImports

noncomputable def pi_fn (n : ℕ) : ℕ :=
  Nat.card {p // Nat.Prime p ∧ p ≤ n}

lemma pi_fn_two : pi_fn 2 = 1 := by
  have : Finite {p // Nat.Prime p ∧ p ≤ 2} := sorry
  sorry
