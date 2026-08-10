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

set_option linter.unusedVariables false

/--
The terms are not all positive.  The first negative one is a(30) = -22690644647302814715858124800000.
Conjecture: a(n) < 0 if and only if A001221(n) is an odd number >= 3.
A001221(n) is $\Omega(n)$, the total number of prime factors of $n$ (counted with multiplicity), which is `ArithmeticFunction.cardFactors n`.
-/
theorem oeis_A067857_conjecture_0.disproof :
  ¬ ∀ (n : ℕ) (hn : n > 0), a n < 0 ↔ Odd (cardFactors n) ∧ cardFactors n ≥ 3 := by
  intro h
  have h8 : a 8 < 0 ↔ Odd (cardFactors 8) ∧ cardFactors 8 ≥ 3 := h 8 (by decide)
  have h_a8 : a 8 = 25584 := by
    have h_m1 : moebius 1 = 1 := moebius_apply_one
    have h_m2 : moebius 2 = -1 := by
      have hp : Nat.Prime 2 := by norm_num
      exact moebius_apply_prime hp
    have h_m4 : moebius 4 = 0 := by
      have h_not : ¬ Squarefree 4 := by decide
      exact moebius_eq_zero_of_not_squarefree h_not
    have h_m8 : moebius 8 = 0 := by
      have h_not : ¬ Squarefree 8 := by decide
      exact moebius_eq_zero_of_not_squarefree h_not

    have h_h1 : harmonic 1 = 1 := by unfold harmonic; norm_num
    have h_h2 : harmonic 2 = 3 / 2 := by unfold harmonic; norm_num
    have h_h4 : harmonic 4 = 25 / 12 := by unfold harmonic; norm_num
    have h_h8 : harmonic 8 = 761 / 280 := by unfold harmonic; norm_num

    unfold a
    have h_ne : 8 ≠ 0 := by decide
    rw [if_neg h_ne]

    have h_sum : (divisors 8).sum (fun d => (moebius (8 / d) : ℚ) * harmonic d) =
                 ((moebius 8 : ℚ) * harmonic 1) + ((moebius 4 : ℚ) * harmonic 2) +
                 ((moebius 2 : ℚ) * harmonic 4) + ((moebius 1 : ℚ) * harmonic 8) := by
      have h_div : divisors 8 = {1, 2, 4, 8} := by decide
      rw [h_div]
      simp
      ring

    rw [h_sum]
    rw [h_m1, h_m2, h_m4, h_m8, h_h1, h_h2, h_h4, h_h8]
    norm_num

  have h_not_lt : ¬ a 8 < 0 := by
    rw [h_a8]
    norm_num

  have h_rhs : Odd (cardFactors 8) ∧ cardFactors 8 ≥ 3 := by
    have h_card : cardFactors 8 = 3 := by
      rw [cardFactors_apply]
      simp
    rw [h_card]
    decide

  exact h_not_lt (h8.mpr h_rhs)
