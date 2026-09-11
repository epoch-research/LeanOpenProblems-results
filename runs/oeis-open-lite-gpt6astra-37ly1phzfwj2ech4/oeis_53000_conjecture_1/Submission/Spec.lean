import FormalConjectures.Util.ProblemImports

open Nat Set

/--
A053000: $a(n) = (\text{smallest prime} > n^2) - n^2$.
-/
noncomputable def A053000 (n : ℕ) : ℕ :=
  (sInf {p | Nat.Prime p ∧ p > n ^ 2}) - n ^ 2

/--
Conjecture: a(n) <= 1+phi(n) = 1+A000010(n), for n>0. This improves on Oppermann's conjecture, which says a(n) < n.
-/
theorem oeis_53000_conjecture_1 (n : ℕ) (hn : n > 0) : A053000 n ≤ 1 + Nat.totient n := by
  sorry

theorem oeis_53000_conjecture_1.disproof : ¬ (type_of% @oeis_53000_conjecture_1) := sorry
