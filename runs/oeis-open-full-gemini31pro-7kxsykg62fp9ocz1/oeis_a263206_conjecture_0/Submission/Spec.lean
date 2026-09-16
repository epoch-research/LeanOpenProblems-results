import FormalConjectures.Util.ProblemImports

open Nat

noncomputable def a (n : ℕ) : ℕ :=
  let L : ℕ := (n^2).primeCounting + 1
  let R : ℕ := ((n + 2)^2 - 1).primeCounting
  R.primeCounting - (L - 1).primeCounting

theorem oeis_a263206_conjecture_0 (n : ℕ) : 0 < n → a n > 0 := by
  sorry

theorem oeis_a263206_conjecture_0.disproof : ¬ (type_of% @oeis_a263206_conjecture_0) := sorry
