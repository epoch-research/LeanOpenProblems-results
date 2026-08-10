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
The conjecture as stated (using `cardFactors`, i.e. the number of prime factors counted
*with multiplicity*, A001222 / big Omega) is false.  A counterexample is `n = 8`:
here `a 8 = 25584 > 0`, while `cardFactors 8 = 3` is odd and `≥ 3`.  Thus the left side of
the iff is false but the right side is true.
(The intended conjecture concerns `A001221`, the number of *distinct* prime factors.)
-/
theorem oeis_A067857_conjecture_0.disproof :
    ¬ ∀ (n : ℕ) (_ : n > 0),
      a n < 0 ↔ Odd (cardFactors n) ∧ cardFactors n ≥ 3 := by
  intro h
  have hh := h 8 (by norm_num)
  have hrhs : Odd (cardFactors 8) ∧ cardFactors 8 ≥ 3 := by
    have hc : cardFactors 8 = 3 := by simp [ArithmeticFunction.cardFactors_apply]
    rw [hc]
    exact ⟨by decide, by decide⟩
  have hlt : a 8 < 0 := hh.mpr hrhs
  have ha : a 8 = 25584 := by
    have hd : Nat.divisors 8 = {1, 2, 4, 8} := by decide
    have hm8 : (moebius 8 : ℤ) = 0 := by decide
    have hm4 : (moebius 4 : ℤ) = 0 := by decide
    have hm2 : (moebius 2 : ℤ) = -1 := by
      rw [ArithmeticFunction.moebius_apply_prime (by norm_num)]
    have hm1 : (moebius 1 : ℤ) = 1 := by simp
    rw [a, if_neg (by norm_num : (8 : ℕ) ≠ 0), hd]
    norm_num [Finset.sum_insert, Finset.mem_insert, hm8, hm4, hm2, hm1,
      harmonic, Finset.sum_range_succ]
  rw [ha] at hlt
  norm_num at hlt
