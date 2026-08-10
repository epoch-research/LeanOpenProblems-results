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
The stated conjecture is false: it quantifies over all natural numbers `n`,
including `n = 0`. Since `Nat.divisors 0 = ∅` and `Nat.totient 0 = 0`,
we get `a 0 = 0`, yet `0 ≠ 1` and `0` is not prime, so part (1) fails at `n = 0`.
-/
theorem oeis_72780_conjecture.disproof :
    ¬ ∀ (n : ℕ),
      (a n = 0 ↔ n = 1 ∨ n.Prime) ∧
      (a n = 2 ↔ ∃ p q, p.Prime ∧ q.Prime ∧ p ≠ q ∧ n = p * q) := by
  intro h
  have h0 : (0 : ℕ) = 1 ∨ Nat.Prime 0 := (h 0).1.mp (by decide)
  rcases h0 with h0 | h0
  · exact absurd h0 (by decide)
  · exact absurd h0 Nat.not_prime_zero
