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
  ¬ (∀ (n : ℕ) (_ : n > 0),
    a n < 0 ↔ Odd (cardFactors n) ∧ cardFactors n ≥ 3) :=
by
  intro h
  have h8 := h 8 (by norm_num)
  have ha8 : a 8 = 25584 := by
    have hdiv : (Nat.divisors 8) = ({1, 2, 4, 8} : Finset ℕ) := by decide
    have hμ8 : moebius 8 = (0 : ℤ) := by
      rw [moebius_eq_zero_of_not_squarefree]
      rw [Nat.squarefree_iff_prime_squarefree]
      push_neg
      exact ⟨2, Nat.prime_two, by norm_num⟩
    have hμ4 : moebius 4 = (0 : ℤ) := by
      rw [moebius_eq_zero_of_not_squarefree]
      rw [Nat.squarefree_iff_prime_squarefree]
      push_neg
      exact ⟨2, Nat.prime_two, by norm_num⟩
    have hμ2 : moebius 2 = (-1 : ℤ) := by
      simp [moebius, Nat.squarefree_two, cardFactors]
    have hμ1 : moebius 1 = (1 : ℤ) := by
      simp [moebius]
    simp [a, hdiv, hμ8, hμ4, hμ2, hμ1, harmonic]
    norm_num
  have hnot : ¬ a 8 < 0 := by
    rw [ha8]
    norm_num
  have hrhs : Odd (cardFactors 8) ∧ cardFactors 8 ≥ 3 := by
    have hcf : cardFactors 8 = 3 := by
      simp [cardFactors, Nat.primeFactorsList, Nat.minFac]
    rw [hcf]
    norm_num
  exact hnot (h8.mpr hrhs)
