import FormalConjectures.Util.ProblemImports

open Polynomial
open Int

noncomputable def A002426 (n : ℕ) : ℕ :=
  ((1 + X + X^2 : Polynomial ℕ) ^ n).coeff n

theorem oeis_2426_conjecture_0 :
  ∀ n : ℕ, 3 < n → (n.Prime ↔ (A002426 n : ℤ) ≡ 1 [ZMOD (n^2 : ℤ)]) := by
  sorry

theorem oeis_2426_conjecture_0.disproof : ¬ (type_of% @oeis_2426_conjecture_0) := sorry
