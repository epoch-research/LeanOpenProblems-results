import FormalConjectures.Util.ProblemImports

noncomputable def pi_fn (n : ℕ) : ℕ :=
  Nat.card {p // Nat.Prime p ∧ p ≤ n}

lemma pi_fn_not_finite (n : ℕ) : Finite {p // Nat.Prime p ∧ p ≤ n} := by
  have : Fintype {p // Nat.Prime p ∧ p ≤ n} := by
    apply Fintype.ofFinset (Finset.filter Nat.Prime (Finset.Iic n))
    intro x
    simp only [Finset.mem_filter, Finset.mem_Iic]
    exact and_comm
  exact Finite.of_fintype _
