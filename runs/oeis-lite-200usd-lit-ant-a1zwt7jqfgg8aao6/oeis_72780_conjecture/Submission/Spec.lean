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
Disproof of Conjecture A072780 (1) and (2):
The conjecture fails at `n = 0`. Since `Nat.divisors 0 = ∅` and `Nat.totient 0 = 0`,
all components of `a 0` vanish, so `a 0 = 0`. But `0` is neither `1` nor prime,
contradicting the forward direction of part (1).
-/
theorem oeis_72780_conjecture.disproof :
    ¬ ∀ (n : ℕ),
      (a n = 0 ↔ n = 1 ∨ n.Prime) ∧
      (a n = 2 ↔ ∃ p q, p.Prime ∧ q.Prime ∧ p ≠ q ∧ n = p * q) := by
  intro h
  have ha0 : a 0 = 0 := by decide
  rcases (h 0).1.mp ha0 with h1 | h2
  · exact absurd h1 (by decide)
  · exact absurd h2 (by decide)
