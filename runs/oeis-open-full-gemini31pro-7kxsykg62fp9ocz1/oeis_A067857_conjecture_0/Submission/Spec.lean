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
theorem oeis_A067857_conjecture_0 (n : ℕ) (hn : n > 0) :
  a n < 0 ↔ Odd (cardFactors n) ∧ cardFactors n ≥ 3 :=
by sorry

theorem oeis_A067857_conjecture_0.disproof : ¬ (type_of% @oeis_A067857_conjecture_0) := by
  intro h
  have h8 : a 8 < 0 ↔ Odd (cardFactors 8) ∧ cardFactors 8 ≥ 3 := h 8 (by decide)
  have d8 : Nat.divisors 8 = {1, 2, 4, 8} := by decide
  have m1 : moebius 1 = 1 := moebius_apply_one
  have m2 : moebius 2 = -1 := moebius_apply_prime Nat.prime_two
  have m4 : moebius 4 = 0 := moebius_eq_zero_of_not_squarefree (by decide)
  have m8 : moebius 8 = 0 := moebius_eq_zero_of_not_squarefree (by decide)
  have a8_val : a 8 = 25584 := by
    dsimp [a]
    rw [d8]
    simp [m1, m2, m4, m8, harmonic]
    norm_num
  have h8_cf : 8 = 2 ^ 3 := by decide
  have cf8 : cardFactors 8 = 3 := by
    rw [h8_cf]
    exact cardFactors_apply_prime_pow Nat.prime_two
  rw [a8_val, cf8] at h8
  revert h8
  decide
