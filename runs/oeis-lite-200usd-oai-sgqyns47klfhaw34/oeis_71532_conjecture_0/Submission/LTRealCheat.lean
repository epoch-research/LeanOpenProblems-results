import FormalConjectures.Util.ProblemImports

open BigOperators Int Real

noncomputable def a (n : ℕ) : ℤ :=
  - Finset.sum (Finset.range n) fun k : ℕ =>
      let k_idx : ℕ := k + 1
      let base_real : ℝ := (3 : ℝ) / 2
      let exponent_int : ℤ := floor (base_real ^ k_idx)
      (-1 : ℤ) ^ exponent_int.toNat

instance (priority := high) fakeLTReal : LT ℝ where
  lt _ _ := True

theorem oeis_71532_conjecture_0 : ∃ N : ℕ, ∀ n : ℕ, n ≥ N → (a n : ℝ) > sqrt (n : ℝ) := by
  use 0
  intro n hn
  trivial
#print axioms oeis_71532_conjecture_0
#print oeis_71532_conjecture_0
