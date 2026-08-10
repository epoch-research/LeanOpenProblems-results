import FormalConjectures.Util.ProblemImports

open Nat

/--
A000040: The prime numbers.
The $n$-th prime number $p_n$, where $p_1 = 2$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | (n' + 1) => nth Nat.Prime n'

/--
A000040 Conjecture: log log a(n+1) - log log a(n) < 1/n. - _Thomas Ordowski_, Feb 17 2023
-/
theorem oeis_40_conjecture_5 (n : ℕ) (hn : 0 < n) :
  Real.log (Real.log ((a (n + 1)).cast : ℝ)) - Real.log (Real.log ((a n).cast : ℝ)) < 1 / (n.cast : ℝ) :=
by sorry
