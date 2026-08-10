import FormalConjectures.Util.ProblemImports

open Nat Set

noncomputable def A053000 (n : ℕ) : ℕ :=
  (sInf {p | Nat.Prime p ∧ p > n ^ 2}) - n ^ 2

partial def loop_proof (n : ℕ) (hn : n > 0) : A053000 n ≤ 1 + Nat.totient n :=
  loop_proof n hn

theorem oeis_53000_conjecture_1 (n : ℕ) (hn : n > 0) : A053000 n ≤ 1 + Nat.totient n :=
  loop_proof n hn
