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
  -- Counterexample: n = 8 = 2^3 has Ω(8) = 3 (odd, ≥ 3), but a 8 = 8! * (H_8 - H_4) > 0.
  have hc : cardFactors 8 = 3 := by
    rw [show (8:ℕ) = 2^3 by norm_num, cardFactors_apply_prime_pow Nat.prime_two]
  have hpos : 0 < a 8 := by
    have hd : Nat.divisors 8 = {1, 2, 4, 8} := by decide
    have h8 : moebius 8 = 0 := by
      rw [show (8:ℕ) = 2^3 by norm_num, moebius_apply_prime_pow Nat.prime_two (by norm_num)]; simp
    have h4 : moebius 4 = 0 := by
      rw [show (4:ℕ) = 2^2 by norm_num, moebius_apply_prime_pow Nat.prime_two (by norm_num)]; simp
    have h2 : moebius 2 = -1 := moebius_apply_prime Nat.prime_two
    have hH4 : (harmonic 4 : ℚ) = 25/12 := by
      simp [harmonic_succ]; norm_num
    have hH8 : (harmonic 8 : ℚ) = 761/280 := by
      simp [harmonic_succ]; norm_num
    simp only [a, hd]
    norm_num [h8, h4, h2, hH4, hH8]
  have h8 := (h 8 (by norm_num)).mpr ⟨by rw [hc]; decide, by rw [hc]⟩
  exact absurd h8 (not_lt.mpr hpos.le)
