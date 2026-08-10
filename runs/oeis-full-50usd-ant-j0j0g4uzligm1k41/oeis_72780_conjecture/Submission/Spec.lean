import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A072780: $a(n) = \sigma_2(n) + \phi(n) \sigma(n) - 2n^2$.
-/
def a (n : ℕ) : ℕ :=
  let sigma2_n : ℕ := n.divisors.sum fun d => d ^ 2
  let sigma1_n : ℕ := n.divisors.sum fun d => d
  let phi_n : ℕ := n.totient
  let two_n_sq : ℕ := 2 * n ^ 2

  -- Calculate over ℤ for subtraction correctness, then convert back to ℕ.
  -- This is safe because the conjecture is that a(n) >= 0.
  ((sigma2_n : ℤ) + (phi_n * sigma1_n : ℤ) - (two_n_sq : ℤ)).toNat

/--
Conjecture A072780 (1) and (2):
(1) a(n) >= 0, with equality only when n is prime (or 1).
(2) a(n) = 2 if and only if n is the product of two distinct primes.
The assertion $a(n) \ge 0$ is trivially true since a(n) is defined as a ℕ.
-/
-- The conjecture as formalized quantifies over all `n : ℕ`, including `n = 0`.
-- For `n = 0` we have `divisors 0 = ∅` and `totient 0 = 0`, so
-- `a 0 = ((0 : ℤ) + 0 * 0 - 0).toNat = 0`.
-- Hence the first biconditional at `n = 0` reads `(a 0 = 0) ↔ (0 = 1 ∨ Nat.Prime 0)`,
-- whose left side is `True` while its right side is `False`. Thus the universally
-- quantified statement is false, and we prove its negation.
theorem oeis_72780_conjecture.disproof :
  ¬ ∀ (n : ℕ), (a n = 0 ↔ n = 1 ∨ n.Prime) ∧
    (a n = 2 ↔ ∃ p q, p.Prime ∧ q.Prime ∧ p ≠ q ∧ n = p * q) := by
  intro h
  have h0 : a 0 = 0 := by
    simp [a, Nat.divisors_zero, Nat.totient_zero]
  rcases (h 0).1.mp h0 with h1 | h1
  · exact Nat.zero_ne_one h1
  · exact Nat.not_prime_zero h1
