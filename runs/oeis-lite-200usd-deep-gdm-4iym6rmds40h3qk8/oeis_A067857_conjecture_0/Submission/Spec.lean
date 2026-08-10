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
lemma not_squarefree_27 : ¬ Squarefree 27 := by
  intro h
  have hu : IsUnit 3 := h 3 (by decide)
  rw [Nat.isUnit_iff] at hu
  contradiction

lemma not_squarefree_9 : ¬ Squarefree 9 := by
  intro h
  have hu : IsUnit 3 := h 3 (by decide)
  rw [Nat.isUnit_iff] at hu
  contradiction

lemma moebius_27 : moebius 27 = 0 := moebius_eq_zero_of_not_squarefree not_squarefree_27
lemma moebius_9 : moebius 9 = 0 := moebius_eq_zero_of_not_squarefree not_squarefree_9
lemma moebius_3 : moebius 3 = -1 := moebius_apply_prime (by decide)
lemma moebius_1 : moebius 1 = 1 := moebius_apply_one

lemma prime_le_three_ne_two {p : ℕ} (hp : Nat.Prime p) (hle : p ≤ 3) (hne : p ≠ 2) : p = 3 := by
  have : 2 ≤ p := hp.two_le
  omega

theorem a_27 : a 27 = (27 : ℕ).factorial * (harmonic 27 - harmonic 9) := by
  dsimp [a]
  congr 1
  have hd : divisors 27 = {1, 3, 9, 27} := by decide
  rw [hd]
  simp
  rw [moebius_27, moebius_9, moebius_3]
  ring

theorem a_27_pos : a 27 > 0 := by
  rw [a_27]
  norm_num

lemma minFac_27 : minFac 27 = 3 := by
  apply prime_le_three_ne_two
  · exact minFac_prime (by decide)
  · apply minFac_le_of_dvd (by decide) (by decide)
  · intro h
    rw [minFac_eq_two_iff] at h
    revert h
    decide

lemma minFac_9 : minFac 9 = 3 := by
  apply prime_le_three_ne_two
  · exact minFac_prime (by decide)
  · apply minFac_le_of_dvd (by decide) (by decide)
  · intro h
    rw [minFac_eq_two_iff] at h
    revert h
    decide

theorem primeFactorsList_27 : primeFactorsList 27 = [3, 3, 3] := by
  -- 27 = 25 + 2
  rw [primeFactorsList_add_two 25]
  have h1 : minFac 27 = 3 := minFac_27
  rw [h1]
  have h2 : (25 + 2 : ℕ) / 3 = 9 := rfl
  rw [h2]
  -- 9 = 7 + 2
  rw [primeFactorsList_add_two 7]
  have h3 : minFac 9 = 3 := minFac_9
  rw [h3]
  have h4 : (7 + 2 : ℕ) / 3 = 3 := rfl
  rw [h4]
  -- 3 is prime
  rw [primeFactorsList_prime (by decide)]

theorem cardFactors_27 : cardFactors 27 = 3 := by
  change (primeFactorsList 27).length = 3
  rw [primeFactorsList_27]
  rfl

theorem oeis_A067857_conjecture_0.disproof : ¬ (∀ (n : ℕ) (hn : n > 0), a n < 0 ↔ Odd (cardFactors n) ∧ cardFactors n ≥ 3) := by
  intro hc
  have h27 : 27 > 0 := by decide
  have h_iff := hc 27 h27
  have h_factors : cardFactors 27 = 3 := cardFactors_27
  have h_odd : Odd (cardFactors 27) := by
    rw [h_factors]
    decide
  have h_ge : cardFactors 27 ≥ 3 := by
    rw [h_factors]
  have h_rhs : Odd (cardFactors 27) ∧ cardFactors 27 ≥ 3 := ⟨h_odd, h_ge⟩
  rw [← h_iff] at h_rhs
  -- now h_rhs says a 27 < 0, but we have a_27_pos : a 27 > 0
  have h_not : ¬ (a 27 < 0) := by linarith [a_27_pos]
  exact h_not h_rhs

