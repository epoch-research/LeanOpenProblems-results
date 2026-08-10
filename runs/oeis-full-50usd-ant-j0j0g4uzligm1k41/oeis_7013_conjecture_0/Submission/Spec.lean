import FormalConjectures.Util.ProblemImports

/--
A007013 Catalan-Mersenne numbers: $a(0) = 2$; for $n \ge 0$, $a(n+1) = 2^{a(n)} - 1$.
-/
def a (n : ℕ) : ℕ :=
  Nat.recOn n 2 fun _ a_n => 2 ^ a_n - 1

/--
A007013 conjecture: All terms of the Catalan-Mersenne sequence are prime.
This is the most common interpretation of the OEIS comment:
"All terms shown are primes, the status of the next term is currently unknown."
-/
theorem oeis_7013_conjecture_0 : ∀ (n : ℕ), Nat.Prime (a n) := by
  intro n
  -- The known terms a 0 = 2, a 1 = 3, a 2 = 7, a 3 = 127 are prime (verified by `decide`).
  -- The next term a 4 = 2^127 - 1 is the Mersenne prime M127.
  -- The crux is a 5 = 2^(2^127 - 1) - 1 = MM127, the Catalan–Mersenne number whose
  -- primality is a famous open problem (it is the smallest double Mersenne number of
  -- unknown status, with no known factor and ~10^38 bits, infeasible to test).
  rcases n with _|_|_|_|n
  · decide
  · decide
  · decide
  · decide
  · sorry
