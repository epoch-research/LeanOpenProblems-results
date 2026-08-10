import FormalConjectures.Util.ProblemImports

open ArithmeticFunction Finset Nat


/--
A080326: Denominator of $\sum_{k=1}^n k^{\mu(k)}$, where $\mu$ is the Moebius function (A008683).
-/
noncomputable def a (n : ℕ) : ℕ :=
  (Finset.sum (Icc 1 n) fun k : ℕ =>
    (k : ℚ) ^ (moebius k : ℤ)
  ).den


/--
Does a(n) = A034386(n) for infinitely many n?
Conjecture: The set of $n$ such that $a(n)$ equals the primorial of $n$ is infinite.
A034386(n) is `Nat.primorial n`.
-/
theorem oeis_a080326_eq_primorial_infinitely_often :
    Set.Infinite {n : ℕ | a n = primorial n} := by
  sorry
