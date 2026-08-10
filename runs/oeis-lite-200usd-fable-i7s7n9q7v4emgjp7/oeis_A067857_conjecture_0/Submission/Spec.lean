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
The conjectured statement is false as stated: it uses `cardFactors n` (= Ω(n), the number of
prime factors counted **with** multiplicity), whereas the OEIS conjecture concerns A001221 = ω(n),
the number of **distinct** prime factors. A counterexample is `n = 8`: we have Ω(8) = 3, which is
odd and ≥ 3, but a(8) = 8!·(H₈ − H₄) = 25584 > 0 (since μ(8) = μ(4) = 0).
-/
theorem oeis_A067857_conjecture_0.disproof :
    ¬ ∀ (n : ℕ), n > 0 → (a n < 0 ↔ Odd (cardFactors n) ∧ cardFactors n ≥ 3) := by
  intro h
  have hc : cardFactors 8 = 3 := by
    rw [show (8:ℕ) = 2^3 by norm_num, cardFactors_apply_prime_pow Nat.prime_two]
  have hμ1 : (moebius 1 : ℤ) = 1 := moebius_apply_one
  have hμ2 : (moebius 2 : ℤ) = -1 := moebius_apply_prime Nat.prime_two
  have hμ4 : (moebius 4 : ℤ) = 0 := by
    rw [show (4:ℕ) = 2^2 by norm_num, moebius_apply_prime_pow Nat.prime_two two_ne_zero]
    norm_num
  have hμ8 : (moebius 8 : ℤ) = 0 := by
    rw [show (8:ℕ) = 2^3 by norm_num, moebius_apply_prime_pow Nat.prime_two three_ne_zero]
    norm_num
  have ha : a 8 = 25584 := by
    unfold a
    rw [if_neg (by norm_num), show (8:ℕ).divisors = {1, 2, 4, 8} from by decide]
    norm_num [hμ1, hμ2, hμ4, hμ8, harmonic, Finset.sum_range_succ]
  have h8 : a 8 < 0 := (h 8 (by norm_num)).mpr ⟨by rw [hc]; decide, by rw [hc]⟩
  rw [ha] at h8
  norm_num at h8
