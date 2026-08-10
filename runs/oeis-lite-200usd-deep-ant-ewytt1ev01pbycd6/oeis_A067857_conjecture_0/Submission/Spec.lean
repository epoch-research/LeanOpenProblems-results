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
theorem oeis_A067857_conjecture_0.disproof :
  ¬ (∀ (n : ℕ) (hn : n > 0),
      a n < 0 ↔ Odd (cardFactors n) ∧ cardFactors n ≥ 3) := by
  intro h
  have hiff := h 8 (by norm_num)
  have ha : a 8 = 25584 := by
    unfold a
    rw [show Nat.divisors 8 = {1, 2, 4, 8} from by decide]
    norm_num [Finset.sum_insert, Finset.mem_insert, harmonic, Finset.sum_range_succ,
      show moebius 8 = 0 from by decide, show moebius 4 = 0 from by decide,
      show moebius 2 = -1 from moebius_apply_prime (by norm_num),
      show moebius 1 = 1 from moebius_apply_one]
  have hc : cardFactors 8 = 3 := by
    rw [show (8 : ℕ) = 2 ^ 3 from by norm_num, cardFactors_apply_prime_pow (by norm_num)]
  rw [ha, hc] at hiff
  have hpos : (25584 : ℚ) < 0 := hiff.mpr ⟨by decide, by norm_num⟩
  norm_num at hpos

