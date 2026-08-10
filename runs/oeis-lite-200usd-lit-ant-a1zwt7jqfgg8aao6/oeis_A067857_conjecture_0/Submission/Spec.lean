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
/- The conjecture as stated is false: it uses `cardFactors`, which is `Ω(n)`, the number of
prime factors of `n` counted *with multiplicity* (A001222), whereas the sign behaviour of
`a(n)` is governed by `ω(n) = A001221`, the number of *distinct* prime factors (which is what
the OEIS comment refers to). A counterexample is `n = 8`: here `Ω(8) = 3` is odd and `≥ 3`, so
the right-hand side holds, but `a(8) = 25584 > 0`, so `a(8) < 0` fails. -/
theorem oeis_A067857_conjecture_0.disproof :
    ¬ (∀ (n : ℕ), n > 0 →
      (a n < 0 ↔ Odd (cardFactors n) ∧ cardFactors n ≥ 3)) := by
  intro h
  have ha8 : a 8 = 25584 := by
    unfold a
    rw [if_neg (by norm_num), show (8:ℕ).divisors = {1,2,4,8} from by decide]
    rw [show (Nat.factorial 8 : ℚ) = 40320 from by norm_num]
    have s8 : ¬ Squarefree 8 := by decide
    have s4 : ¬ Squarefree 4 := by decide
    have s2 : Squarefree 2 := Nat.prime_two.squarefree
    norm_num [moebius, harmonic, Finset.sum_range_succ, s8, s4, s2]
  have hcf : cardFactors 8 = 3 := by
    rw [show (8:ℕ) = 2^3 from by norm_num, cardFactors_apply_prime_pow Nat.prime_two]
  have key := (h 8 (by norm_num)).mpr ⟨by rw [hcf]; decide, by rw [hcf]⟩
  rw [ha8] at key
  norm_num at key

theorem foo.disproof :
    ¬ (∀ (n : ℕ), n > 0 →
      (a n < 0 ↔ Odd (cardFactors n) ∧ cardFactors n ≥ 3)) :=
  oeis_A067857_conjecture_0.disproof
