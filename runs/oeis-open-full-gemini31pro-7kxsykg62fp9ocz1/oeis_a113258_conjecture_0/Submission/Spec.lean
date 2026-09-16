import FormalConjectures.Util.ProblemImports

open Nat
open Finset

/--
A113258: Ascending descending base exponent transform of factorials.
$$a(n) = \sum_{i = 1}^n (i!) ^ {(n-i+1)!}$$
-/
def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range n) fun i => (Nat.factorial (i + 1)) ^ (Nat.factorial (n - i))

theorem oeis_a113258_conjecture_0 :
  ∃ (n : ℕ), 4 < n ∧ ∃ (b e : ℕ), 1 < b ∧ 1 < e ∧ a n = b ^ e := by
  sorry

theorem oeis_a113258_conjecture_0.disproof : ¬ (type_of% @oeis_a113258_conjecture_0) := by
  sorry
