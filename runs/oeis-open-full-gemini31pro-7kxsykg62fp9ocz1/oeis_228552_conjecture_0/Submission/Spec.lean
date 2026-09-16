import FormalConjectures.Util.ProblemImports

open Matrix Nat

noncomputable def a (n : ℕ) : ℕ :=
  (Matrix.det (Matrix.of (fun (i j : Fin n) =>
    if Nat.Prime (i.val + j.val + 2) then (1 : ℤ) else (0 : ℤ)))).natAbs.sqrt

theorem oeis_228552_conjecture_0 : ∀ n : ℕ, 15 < n → a n > 0 :=
  by sorry

theorem oeis_228552_conjecture_0.disproof : ¬ (type_of% @oeis_228552_conjecture_0) :=
  by sorry
