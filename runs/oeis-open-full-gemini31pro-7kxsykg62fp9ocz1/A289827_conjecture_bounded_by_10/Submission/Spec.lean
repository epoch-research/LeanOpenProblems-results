import FormalConjectures.Util.ProblemImports

open scoped Nat.Prime

noncomputable def A289827 (n : ℕ) : ℕ :=
  Nat.findGreatest (fun m => π (m + n) = π m + π n) n

theorem A289827_conjecture_bounded_by_10 : ∀ (n : ℕ), A289827 n ≤ 10 := by
  sorry

theorem A289827_conjecture_bounded_by_10.disproof : ¬ (∀ (n : ℕ), A289827 n ≤ 10) := by
  sorry
