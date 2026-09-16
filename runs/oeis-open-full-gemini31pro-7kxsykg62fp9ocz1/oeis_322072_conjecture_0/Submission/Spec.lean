import FormalConjectures.Util.ProblemImports

open BigOperators

noncomputable def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.Icc 1 n) fun k : ℕ =>
    let num : ℕ := 2 * n ^ k
    let den : ℕ := k ^ k
    let term_q : ℚ := (num : ℚ) / (den : ℚ)
    (Rat.floor term_q).toNat

theorem oeis_322072_conjecture_0 {n : ℕ} (hn : 1 ≤ n) :
  (∃ m : ℕ, a (n + 1) - a n = m ^ 2) ↔ n = 1 ∨ n = 5 ∨ n = 6 :=
by sorry

theorem oeis_322072_conjecture_0.disproof : ¬ (type_of% @oeis_322072_conjecture_0) := by exact sorry
