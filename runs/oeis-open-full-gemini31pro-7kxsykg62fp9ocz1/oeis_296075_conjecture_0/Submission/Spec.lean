import FormalConjectures.Util.ProblemImports

open Nat Finset ArithmeticFunction

/--
A296075: Sum of deficiencies of divisors of $n$.
The deficiency of a number $d$ is $2d - \sigma_1(d)$, where $\sigma_1(d)$ is the sum of the divisors of $d$.
$$a(n) = \sum_{d|n} (2d - \sigma_1(d))$$
-/
def a (n : ℕ) : ℤ :=
  (divisors n).sum fun d =>
    (2 * d : ℤ) - (ArithmeticFunction.sigma 1 d : ℤ)

/--
Conjecture from OEIS A296075, by Robert Israel:
Are 1 and 12 the only solutions to a(n)=1?
-/
theorem oeis_296075_conjecture_0 : ∀ n : ℕ,
  a n = 1 ↔ n = 1 ∨ n = 12 := by
  sorry

def H : ArithmeticFunction ℤ := (sigma 1 : ArithmeticFunction ℤ) * zeta

lemma H_apply (n : ℕ) : H n = (divisors n).sum fun d => (sigma 1 d : ℤ) := by
  exact coe_mul_zeta_apply

lemma a_eq (n : ℕ) : a n = 2 * (sigma 1 : ArithmeticFunction ℤ) n - H n := by
  dsimp [a]
  rw [H_apply, sum_sub_distrib, ← mul_sum]
  congr 1
  congr 1
  rw [sigma_one_apply]
  push_cast
  rfl

lemma H_mult : H.IsMultiplicative := by
  apply IsMultiplicative.mul
  · exact (@isMultiplicative_sigma 1).natCast (R := ℤ)
  · exact isMultiplicative_zeta.natCast (R := ℤ)

def my_n := 33085221781504

set_option maxRecDepth 200000

lemma s0 : (sigma 1 : ArithmeticFunction ℤ) 16384 = 32767 := by
  rw [natCoe_apply, sigma_one_apply]
  decide

lemma h0 : H 16384 = 65519 := by
  have hd : Nat.divisors 16384 = {1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384} := by decide
  change ((sigma 1 : ArithmeticFunction ℤ) * ↑zeta) 16384 = 65519
  rw [coe_mul_zeta_apply, hd]
  repeat rw [sum_insert (by decide)]
  rw [sum_singleton]
  repeat rw [natCoe_apply, sigma_one_apply]
  decide

lemma p1 : Nat.Prime 4409 := by norm_num
lemma p2 : Nat.Prime 458009 := by norm_num

lemma s1 : (sigma 1 : ArithmeticFunction ℤ) 4409 = 4410 := by
  rw [natCoe_apply, sigma_one_apply, Nat.Prime.divisors p1]
  rfl

lemma h1 : H 4409 = 4411 := by
  change ((sigma 1 : ArithmeticFunction ℤ) * ↑zeta) 4409 = 4411
  rw [coe_mul_zeta_apply, Nat.Prime.divisors p1]
  rw [sum_insert (by decide), sum_singleton]
  rw [natCoe_apply, sigma_one_apply, Nat.divisors_one, sum_singleton]
  rw [natCoe_apply, sigma_one_apply, Nat.Prime.divisors p1]
  rfl

lemma s2 : (sigma 1 : ArithmeticFunction ℤ) 458009 = 458010 := by
  rw [natCoe_apply, sigma_one_apply, Nat.Prime.divisors p2]
  rfl

lemma h2 : H 458009 = 458011 := by
  change ((sigma 1 : ArithmeticFunction ℤ) * ↑zeta) 458009 = 458011
  rw [coe_mul_zeta_apply, Nat.Prime.divisors p2]
  rw [sum_insert (by decide), sum_singleton]
  rw [natCoe_apply, sigma_one_apply, Nat.divisors_one, sum_singleton]
  rw [natCoe_apply, sigma_one_apply, Nat.Prime.divisors p2]
  rfl

lemma h_coprime1 : Nat.gcd 16384 (4409 * 458009) = 1 := by decide
lemma h_coprime2 : Nat.gcd 4409 458009 = 1 := by decide

lemma my_n_eq : my_n = 16384 * (4409 * 458009) := by rfl

lemma a_my_n : a my_n = 1 := by
  rw [a_eq]
  have Hsigma_mult := (@isMultiplicative_sigma 1).natCast (R := ℤ)
  have sig_eval : (sigma 1 : ArithmeticFunction ℤ) my_n = 66183576284700 := by
    rw [my_n_eq]
    rw [IsMultiplicative.map_mul_of_coprime Hsigma_mult h_coprime1]
    rw [IsMultiplicative.map_mul_of_coprime Hsigma_mult h_coprime2]
    rw [s0, s1, s2]
    norm_num
  have H_eval : H my_n = 132367152569399 := by
    rw [my_n_eq]
    rw [IsMultiplicative.map_mul_of_coprime H_mult h_coprime1]
    rw [IsMultiplicative.map_mul_of_coprime H_mult h_coprime2]
    rw [h0, h1, h2]
    norm_num
  rw [sig_eval, H_eval]
  norm_num

theorem oeis_296075_conjecture_0.disproof : ¬ (∀ n : ℕ, a n = 1 ↔ n = 1 ∨ n = 12) := by
  intro h
  have := (h my_n).mp a_my_n
  rcases this with h1 | h12
  · revert h1; decide
  · revert h12; decide

