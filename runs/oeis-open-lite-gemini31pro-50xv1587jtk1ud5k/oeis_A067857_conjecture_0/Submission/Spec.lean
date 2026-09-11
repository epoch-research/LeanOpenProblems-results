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

theorem moebius_8 : moebius 8 = 0 := by
  rw [moebius_eq_zero_of_not_squarefree]
  intro h
  have h_dvd : 2 * 2 ∣ 8 := by decide
  have h_sq := h 2 h_dvd
  rw [Nat.isUnit_iff] at h_sq
  revert h_sq
  decide

theorem moebius_4 : moebius 4 = 0 := by
  rw [moebius_eq_zero_of_not_squarefree]
  intro h
  have h_dvd : 2 * 2 ∣ 4 := by decide
  have h_sq := h 2 h_dvd
  rw [Nat.isUnit_iff] at h_sq
  revert h_sq
  decide

theorem moebius_2 : moebius 2 = -1 := by
  have h : Nat.Prime 2 := by decide
  exact moebius_apply_prime h

theorem moebius_1 : moebius 1 = 1 := by simp

theorem harmonic_1 : harmonic 1 = 1 := by norm_num [harmonic]
theorem harmonic_2 : harmonic 2 = 3 / 2 := by norm_num [harmonic]
theorem harmonic_4 : harmonic 4 = 25 / 12 := by norm_num [harmonic]
theorem harmonic_8 : harmonic 8 = 761 / 280 := by norm_num [harmonic]

theorem a_8 : a 8 = 25584 := by
  unfold a
  rw [if_neg (by decide)]
  have h_div : divisors 8 = {1, 2, 4, 8} := by decide
  rw [h_div]
  dsimp only
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  have h8 : 8 / 1 = 8 := by decide
  have h4 : 8 / 2 = 4 := by decide
  have h2 : 8 / 4 = 2 := by decide
  have h1 : 8 / 8 = 1 := by decide
  rw [h8, h4, h2, h1]
  rw [moebius_8, moebius_4, moebius_2, moebius_1]
  rw [harmonic_1, harmonic_2, harmonic_4, harmonic_8]
  norm_num

theorem cardFactors_8 : cardFactors 8 = 3 := by
  change cardFactors (2^3) = 3
  exact cardFactors_apply_prime_pow (by decide)

theorem oeis_A067857_conjecture_0.disproof : ¬ (type_of% @oeis_A067857_conjecture_0) := by
  intro h
  have h8 := h 8 (by decide)
  rw [a_8, cardFactors_8] at h8
  revert h8
  decide
