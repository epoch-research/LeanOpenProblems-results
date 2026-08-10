import FormalConjectures.Util.ProblemImports

open Nat

/--
A051903: Maximum exponent in the prime factorization of $n$.
-/
def a (n : ℕ) : ℕ :=
  n.factorization.support.sup n.factorization

/--
A051903 (*) Are there composite numbers n > 4 such that n == a(n) (mod phi(n))?
This formalizes the conjecture that there are no such numbers.
Note: We use `¬ Nat.Prime n ∧ 4 < n` to formally express $n$ is a composite number greater than 4, as $4 < n$ implies $1 < n$.
-/
theorem oeis_51903_conjecture_0 :
  ¬ ∃ n, (¬ Nat.Prime n) ∧ 4 < n ∧ Nat.totient n ∣ (n - a n) := by
  sorry
