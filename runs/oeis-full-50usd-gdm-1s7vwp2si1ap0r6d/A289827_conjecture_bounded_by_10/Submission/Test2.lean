import FormalConjectures.Util.ProblemImports

open scoped Nat.Prime

noncomputable def A289827 (n : ℕ) : ℕ :=
  Nat.findGreatest (fun m => π (m + n) = π m + π n) n

theorem A289827_conjecture_bounded_by_10 : ∀ (n : ℕ), A289827 n ≤ 10 := by
  intro n
  by_cases h : n ≤ 10
  · have h2 : A289827 n ≤ n := Nat.findGreatest_le _
    omega
  · sorry
