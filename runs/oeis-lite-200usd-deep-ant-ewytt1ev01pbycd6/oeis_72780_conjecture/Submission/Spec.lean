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

This conjecture, as stated with `n` ranging over **all** of `ℕ`, is FALSE.
The mathematical statement is intended for `n ≥ 1` (where it is indeed true:
`a(n) = σ₂(n) + φ(n)σ(n) - 2n²` vanishes exactly for `n = 1` or `n` prime, and
equals `2` exactly for products of two distinct primes). However at `n = 0` we
have `a 0 = 0` (all of `σ₂(0)`, `φ(0)`, `σ(0)`, `0²` are `0`), while `0` is
neither equal to `1` nor prime. Hence the first equivalence fails at `n = 0`,
so the universally quantified conjecture is refuted there.
-/
theorem oeis_72780_conjecture.disproof :
    ¬ ∀ (n : ℕ),
      (a n = 0 ↔ n = 1 ∨ n.Prime) ∧
      (a n = 2 ↔ ∃ p q, p.Prime ∧ q.Prime ∧ p ≠ q ∧ n = p * q) := by
  intro h
  -- Specialize the (false) first equivalence at `n = 0`.
  have h0 : (a 0 = 0 ↔ (0 : ℕ) = 1 ∨ Nat.Prime 0) := (h 0).1
  have ha0 : a 0 = 0 := by simp [a]
  -- `a 0 = 0` is true, so the right-hand side `0 = 1 ∨ Prime 0` would have to hold.
  rcases h0.mp ha0 with h1 | h2
  · exact absurd h1 (by decide)
  · exact absurd h2 (by decide)
