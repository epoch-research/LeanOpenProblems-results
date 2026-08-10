import FormalConjectures.Util.ProblemImports

noncomputable def a (n : ℕ) : ℤ :=
  Matrix.det fun (i j : Fin n) =>
    let k := i.val + j.val + 2
    if k = 2 ∨ (k % 2 = 1 ∧ ¬ k.Prime) then (1 : ℤ) else (0 : ℤ)

theorem oeis_228591_conjecture_0 : ∀ n : ℕ, 15 < n → a n ≠ 0 := by
  sorry
