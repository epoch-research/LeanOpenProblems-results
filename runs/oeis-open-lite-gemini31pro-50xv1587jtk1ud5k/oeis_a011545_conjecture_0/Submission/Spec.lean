import FormalConjectures.Util.ProblemImports

open Real Int

theorem oeis_a011545_conjecture_0 (n : ℕ) :
    ¬ ∃ (k : ℤ),
      (Real.pi * (10 : ℝ) ^ n.cast < k.cast) ∧
      (k.cast < Real.pi / Real.arctan (1 / (10 : ℝ) ^ n.cast)) := by
  sorry

theorem oeis_a011545_conjecture_0.disproof : ¬ (type_of% @oeis_a011545_conjecture_0) := by
  intro h
  have h1 := h 1
  apply h1
  use 32
  sorry
