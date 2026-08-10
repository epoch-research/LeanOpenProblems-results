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
    a n < 0 ↔ Odd (cardFactors n) ∧ cardFactors n ≥ 3) :=
by
  intro h
  have hdiv8 : (8 : ℕ).divisors = {1, 2, 4, 8} := by
    ext x
    simp [Nat.divisors]
    constructor
    · intro hx
      have hx1 : 1 ≤ x := hx.1.1
      have hx2 : x ≤ 8 := by omega
      interval_cases x <;> try norm_num at hx <;> norm_num
    · intro hx
      rcases hx with rfl | rfl | rfl | rfl <;> norm_num
  have hsf8 : ¬ Squarefree (8 : ℕ) := by
    rw [Nat.squarefree_iff_nodup_primeFactorsList (by norm_num : (8 : ℕ) ≠ 0)]
    norm_num [Nat.primeFactorsList, Nat.minFac]
  have hsf4 : ¬ Squarefree (4 : ℕ) := by
    rw [Nat.squarefree_iff_nodup_primeFactorsList (by norm_num : (4 : ℕ) ≠ 0)]
    norm_num [Nat.primeFactorsList, Nat.minFac]
  have hsf2 : Squarefree (2 : ℕ) := by
    rw [Nat.squarefree_iff_nodup_primeFactorsList (by norm_num : (2 : ℕ) ≠ 0)]
    norm_num [Nat.primeFactorsList, Nat.minFac]
  have hsf1 : Squarefree (1 : ℕ) := squarefree_one
  have h8false : ¬ (a 8 < 0 ↔ Odd (cardFactors 8) ∧ cardFactors 8 ≥ 3) := by
    norm_num [a, hdiv8, harmonic, moebius, cardFactors, Nat.primeFactorsList, Nat.minFac,
      hsf8, hsf4, hsf2, hsf1]
  exact h8false (h 8 (by norm_num))
