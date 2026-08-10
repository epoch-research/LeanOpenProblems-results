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
private lemma divisors_eight : (8 : ℕ).divisors = {1, 2, 4, 8} := by
  rw [show 8 = 2 ^ 3 by norm_num]
  rw [Nat.divisors_prime_pow (by norm_num : Nat.Prime 2) 3]
  decide

private lemma a_eight : a 8 = (25584 : ℚ) := by
  rw [a]
  simp
  rw [divisors_eight]
  simp
  rw [show moebius 8 = (0 : ℤ) by
    rw [show 8 = 2 ^ 3 by norm_num]
    rw [moebius_apply_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 3 ≠ 0)]
    norm_num]
  rw [show moebius 4 = (0 : ℤ) by
    rw [show 4 = 2 ^ 2 by norm_num]
    rw [moebius_apply_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 2 ≠ 0)]
    norm_num]
  rw [show moebius 2 = (-1 : ℤ) by
    exact moebius_apply_prime (by norm_num : Nat.Prime 2)]
  norm_num [harmonic]

private lemma cardFactors_eight : cardFactors 8 = 3 := by
  rw [show 8 = 2 ^ 3 by norm_num]
  exact cardFactors_apply_prime_pow (by norm_num : Nat.Prime 2)

theorem oeis_A067857_conjecture_0.disproof :
  ¬ (∀ (n : ℕ) (_hn : n > 0),
    a n < 0 ↔ Odd (cardFactors n) ∧ cardFactors n ≥ 3) := by
  intro h
  have h8 : ¬ (a 8 < 0 ↔ Odd (cardFactors 8) ∧ cardFactors 8 ≥ 3) := by
    rw [a_eight, cardFactors_eight]
    norm_num
  exact h8 (h 8 (by norm_num))
