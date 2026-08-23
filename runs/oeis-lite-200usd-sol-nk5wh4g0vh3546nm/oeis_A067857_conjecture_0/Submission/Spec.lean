import FormalConjectures.Util.ProblemImports

open Nat ArithmeticFunction

/--
A067857: Sum_{k|n} a(k)/k! = Sum_{j=1 to n} 1/j, sum on left is over positive divisors k of n.
The formula for $a(n)$ derived from Möbius inversion is
$$a(n) = n! \sum_{d \mid n} \mu(n/d) H_d$$
where $H_d = \sum_{j=1}^d \frac{1}{j}$ is the $d$-th Harmonic Number (`harmonic d` in Mathlib), and $\mu$ is the Möbius function (`ArithmeticFunction.moebius`).
The sequence members are integers (the first negative one is $a(30)$), but the definition is most naturally computed in $\mathbb{Q}$. We define the result as a rational number.
-/
def a (n : ℕ) : ℚ :=
  if n = 0 then 0
  else
    (n.factorial : ℚ) *
    (n.divisors.sum fun d =>
      -- d is a positive divisor of n.
      -- The ArithmeticFunction.moebius returns a ℤ, which is coerced to ℚ.
      let mu_val : ℤ := moebius (n / d)
      let h_val : ℚ := harmonic d
      (mu_val : ℚ) * h_val)

/--
The terms are not all positive.  The first negative one is a(30) = -22690644647302814715858124800000.
Conjecture: a(n) < 0 if and only if A001221(n) is an odd number >= 3.
A001221(n) is $\Omega(n)$, the total number of prime factors of $n$ (counted with multiplicity), which is `ArithmeticFunction.cardFactors n`.
-/
theorem oeis_A067857_conjecture_0.disproof : ¬ (∀ (n : ℕ), n > 0 →
    (a n < 0 ↔ Odd (cardFactors n) ∧ cardFactors n ≥ 3)) := by
  intro h
  have hh := h 8 (by norm_num)
  have hdiv : (8 : ℕ).divisors = {1, 2, 4, 8} := by decide
  have hsf8 : ¬ Squarefree (8 : ℕ) := by decide
  have hsf4 : ¬ Squarefree (4 : ℕ) := by decide
  have hsf2 : Squarefree (2 : ℕ) := Nat.prime_two.squarefree
  have hsf1 : Squarefree (1 : ℕ) := squarefree_one
  have hcf8 : cardFactors 8 = 3 := by
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num]
    exact cardFactors_apply_prime_pow Nat.prime_two
  norm_num [a, hdiv, harmonic, moebius, hsf8, hsf4, hsf2, hsf1, hcf8,
    cardFactors_apply, Nat.primeFactorsList] at hh
