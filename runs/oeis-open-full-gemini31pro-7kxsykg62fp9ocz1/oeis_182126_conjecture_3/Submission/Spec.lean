import FormalConjectures.Util.ProblemImports

open Nat

noncomputable def a (n : ℕ) : ℕ :=
  let p_n := fun k : ℕ => (Nat.nth Nat.Prime (k - 1))
  if n = 0 then 0
  else (p_n n * p_n (n + 1)) % p_n (n + 2)

theorem oeis_182126_conjecture_3 :
  ∀ n : ℕ, n > 0 → (Nat.Prime (a n) ↔ a n ∈ ([2, 7, 11, 13, 29] : List ℕ)) :=
by sorry

theorem oeis_182126_conjecture_3.disproof : ¬ (type_of% @oeis_182126_conjecture_3) := sorry
