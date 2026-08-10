import FormalConjectures.Util.ProblemImports

open Nat Set

noncomputable def A268597 (n : ℕ) : ℕ :=
  sInf { x : ℕ | x > 0 ∧ (x - 1) % Nat.totient x = n }

theorem oeis_268597_conjecture_test (n : ℕ) : A268597 n > 0 := answer(sorry)
