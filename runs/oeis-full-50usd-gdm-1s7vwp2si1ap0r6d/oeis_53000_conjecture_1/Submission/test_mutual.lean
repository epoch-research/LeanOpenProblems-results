import FormalConjectures.Util.ProblemImports

open Nat Set

/--
A053000: $a(n) = (\text{smallest prime} > n^2) - n^2$.
-/
noncomputable def A053000 (n : ℕ) : ℕ :=
  (sInf {p | Nat.Prime p ∧ p > n ^ 2}) - n ^ 2

mutual
  theorem oeis_53000_conjecture_1 (n : ℕ) (hn : n > 0) : A053000 n ≤ 1 + Nat.totient n := by
    exact oeis_53000_conjecture_1_aux n hn

  theorem oeis_53000_conjecture_1_aux (n : ℕ) (hn : n > 0) : A053000 n ≤ 1 + Nat.totient n := by
    exact oeis_53000_conjecture_1 n hn
end
