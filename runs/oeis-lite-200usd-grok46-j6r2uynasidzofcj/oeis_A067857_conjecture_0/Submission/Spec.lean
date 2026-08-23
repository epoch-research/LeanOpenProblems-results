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
    ¬∀ (n : ℕ) (_hn : n > 0), a n < 0 ↔ Odd (cardFactors n) ∧ cardFactors n ≥ 3 := by
  intro h
  have h8 := h 8 (by decide)
  have hcard : cardFactors 8 = 3 := by
    have hpow : 8 = 2 ^ 3 := by decide
    rw [hpow, cardFactors_apply_prime_pow Nat.prime_two]
  have hodd : Odd (cardFactors 8) ∧ cardFactors 8 ≥ 3 := by
    rw [hcard]
    decide
  have ha : a 8 < 0 := h8.mpr hodd
  have hdiv : (8).divisors = {1, 2, 4, 8} := by decide
  have μ1 : moebius 1 = 1 := moebius_apply_one
  have μ2 : moebius 2 = -1 := moebius_apply_prime Nat.prime_two
  have μ4 : moebius 4 = 0 := by
    have hpow : 4 = 2 ^ 2 := by decide
    rw [hpow, moebius_apply_prime_pow Nat.prime_two (by decide)]
    decide
  have μ8 : moebius 8 = 0 := by
    have hpow : 8 = 2 ^ 3 := by decide
    rw [hpow, moebius_apply_prime_pow Nat.prime_two (by decide)]
    decide
  have hH4 : harmonic 4 = 25 / 12 := by
    unfold harmonic
    simp [Finset.sum_range_succ]
    norm_num
  have hH8 : harmonic 8 = 761 / 280 := by
    unfold harmonic
    simp [Finset.sum_range_succ]
    norm_num
  have ha_val : a 8 = (40320 : ℚ) * (harmonic 8 - harmonic 4) := by
    unfold a
    simp only []
    rw [hdiv]
    simp [μ1, μ2, μ4, μ8]
    norm_num
  have ha_pos : 0 < a 8 := by
    rw [ha_val, hH4, hH8]
    norm_num
  exact not_lt_of_gt ha_pos ha
