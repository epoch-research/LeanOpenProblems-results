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

theorem a_eight : a 8 = 25584 := by
  unfold a
  have h_neq : 8 ≠ 0 := by decide
  rw [if_neg h_neq]
  have h_div : (8 : ℕ).divisors = {1, 2, 4, 8} := by decide
  rw [h_div]
  simp
  have h_m8 : moebius 8 = 0 := by decide
  have h_m4 : moebius 4 = 0 := by decide
  have h_m2 : moebius 2 = -1 := by
    have h_prime2 : Nat.Prime 2 := Nat.prime_two
    exact moebius_apply_prime h_prime2
  rw [h_m8, h_m4, h_m2]
  norm_num

set_option linter.unusedVariables false

theorem oeis_A067857_conjecture_0.disproof :
    ¬ ∀ (n : ℕ) (hn : n > 0), a n < 0 ↔ Odd (cardFactors n) ∧ cardFactors n ≥ 3 := by
  intro h
  have h8 : a 8 < 0 ↔ Odd (cardFactors 8) ∧ cardFactors 8 ≥ 3 := h 8 (by decide)
  have h_a8 : a 8 = 25584 := a_eight
  have h_not_lhs : ¬ a 8 < 0 := by
    rw [h_a8]
    decide
  have h_factors : primeFactorsList 8 = [2, 2, 2] := by
    have h1 : primeFactorsList 8 = minFac 8 :: primeFactorsList (8 / minFac 8) := primeFactorsList_add_two 6
    have h_minFac8 : minFac 8 = 2 := rfl
    have h_div : 8 / 2 = 4 := rfl
    rw [h_minFac8, h_div] at h1
    have h2 : primeFactorsList 4 = minFac 4 :: primeFactorsList (4 / minFac 4) := primeFactorsList_add_two 2
    have h_minFac4 : minFac 4 = 2 := rfl
    have h_div4 : 4 / 2 = 2 := rfl
    rw [h_minFac4, h_div4] at h2
    rw [h2, primeFactorsList_two] at h1
    exact h1
  have h_cardFactors8 : cardFactors 8 = 3 := by
    change (primeFactorsList 8).length = 3
    rw [h_factors]
    rfl
  have h_rhs : Odd (cardFactors 8) ∧ cardFactors 8 ≥ 3 := by
    rw [h_cardFactors8]
    decide
  rcases h8 with ⟨h_to, h_from⟩
  have h_lhs : a 8 < 0 := h_from h_rhs
  exact h_not_lhs h_lhs
