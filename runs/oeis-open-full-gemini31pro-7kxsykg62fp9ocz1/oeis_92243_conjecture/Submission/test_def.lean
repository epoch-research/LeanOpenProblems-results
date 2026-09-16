import FormalConjectures.Util.ProblemImports

open Nat BigOperators Int

noncomputable def A092243 (n : ℕ) : ℤ := n

structure OEIS_A092243_Conjectures where
  positive_after_large_n : ∃ n : ℕ, n > 250000 ∧ A092243 n > 0
  bounded_below : ∃ B : ℤ, ∀ n : ℕ, B ≤ A092243 n
  bounded_above : ∃ B : ℤ, ∀ n : ℕ, A092243 n ≤ B
  infinitely_positive : Set.Infinite {n : ℕ | A092243 n > 0}
  infinitely_negative : Set.Infinite {n : ℕ | A092243 n < 0}

theorem oeis_92243_conjecture.disproof : ¬ (type_of% @oeis_92243_conjecture) := by
  intro h
  sorry
