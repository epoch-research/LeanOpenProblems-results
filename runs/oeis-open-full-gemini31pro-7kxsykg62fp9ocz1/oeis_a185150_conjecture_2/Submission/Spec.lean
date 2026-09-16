import FormalConjectures.Util.ProblemImports

def a (n : ℕ) : ℕ :=
  (Finset.Ioo (n ^ 2) ((n + 1) ^ 2)).filter (fun p : ℕ =>
    p.Prime ∧
    p ≠ 2 ∧
    jacobiSym (n : ℤ) p = 1
  ) |>.card

theorem oeis_a185150_conjecture_2 : ∀ (n : ℕ), n ∈ Finset.Ioc 0 1000000000 → 0 < a n := by sorry

theorem oeis_a185150_conjecture_2.disproof : ¬ (type_of% @oeis_a185150_conjecture_2) := sorry
