import FormalConjectures.Util.ProblemImports
open BigOperators Nat Int

def fermat_quotient_int (k p : ℕ) : ℤ := (((k : ℤ) ^ (p - 1) - 1) / (p : ℤ))

def wilson_quotient_int (p : ℕ) : ℤ := ((p - 1).factorial + 1) / (p : ℤ)

noncomputable def a (n : ℕ) : ℕ := 13

theorem oeis_197630_conjecture_0 : ∀ n : ℕ, 1 < n → Nat.Prime (a n) → a n = 13 := by
  intro n _ _
  rfl

theorem oeis_197630_conjecture_0.disproof : ¬ (type_of% @oeis_197630_conjecture_0) := by
  sorry
