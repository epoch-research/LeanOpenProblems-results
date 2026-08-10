import FormalConjectures.Util.ProblemImports

open ArithmeticFunction Nat BigOperators

/--
A286971: Number of ways to write $n$ as a sum of two numbers, one of which is the product of an even number of distinct primes (including 1) (A030229) and another is the product of an odd number of distinct primes (A030059).
This counts ordered pairs $(e, o)$ of positive integers such that $e+o=n$, $\mu(e)=1$, and $\mu(o)=-1$.
-/
def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.Ico 1 n) fun e =>
    let o : ℕ := n - e
    -- The values of moebius e and moebius o are compared with Int 1 and Int -1.
    if moebius e = 1 ∧ moebius o = -1 then 1 else 0

/-- A286971 Conjecture: a(n) > 0 for all n > 10. -/
theorem oeis_286971_conjecture_0 :
  ∀ n, 10 < n → a n > 0 := by sorry
