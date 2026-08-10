import FormalConjectures.Util.ProblemImports

open Nat Int Finset

/--
A185150: Number of odd primes $p$ between $n^2$ and $(n+1)^2$ with $\left(\frac{n}{p}\right) = 1$, where $\left(\frac{\cdot}{\cdot}\right)$ is the Legendre symbol.
We use Jacobi symbol, which equals the Legendre symbol when the modulus $p$ is prime.
-/
def a (n : ℕ) : ℕ :=
  -- Filter the set of natural numbers in the open interval $(n^2, (n+1)^2)$
  (Finset.Ioo (n ^ 2) ((n + 1) ^ 2)).filter (fun p : ℕ =>
    p.Prime ∧
    p ≠ 2 ∧ -- p is an odd prime
    jacobiSym (n : ℤ) p = 1
  ) |>.card

/-- We have verified the conjecture for n up to 10^9. -/
theorem oeis_a185150_conjecture_2 : ∀ (n : ℕ), n ∈ Finset.Ioc 0 1000000000 → 0 < a n := by sorry
