import FormalConjectures.Util.ProblemImports

open Nat

noncomputable def a020330 (n : ℕ) : ℕ :=
  (2 ^ (log2 n + 1) + 1) * n

noncomputable def a (n : ℕ) : ℕ :=
  let L := a020330 n
  let R := a020330 (n + 1)
  (R - 1).primeCounting - L.primeCounting

theorem oeis_a293833_conjecture :
  ∀ n : ℕ, n > 0 → (a n > 0 ∧ (a n = 1 ↔ n = 12)) :=
by sorry

theorem oeis_a293833_conjecture.disproof : ¬ (type_of% @oeis_a293833_conjecture) :=
by sorry
