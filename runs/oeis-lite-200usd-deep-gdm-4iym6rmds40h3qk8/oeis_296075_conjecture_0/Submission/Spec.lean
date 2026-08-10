import FormalConjectures.Util.ProblemImports

open Nat Finset
open scoped Pointwise

set_option maxRecDepth 20000

/--
A296075: Sum of deficiencies of divisors of $n$.
The deficiency of a number $d$ is $2d - \sigma_1(d)$, where $\sigma_1(d)$ is the sum of the divisors of $d$.
$$a(n) = \sum_{d|n} (2d - \sigma_1(d))$$
-/
def a (n : ℕ) : ℤ :=
  (divisors n).sum fun d =>
    -- Deficiency of d: 2*d - sigma_1(d)
    (2 * d : ℤ) - (ArithmeticFunction.sigma 1 d : ℤ)

lemma sigma_pow_2_0 : (ArithmeticFunction.sigma 1 (2^0) : ℤ) = 1 := by
  have h_sig := ArithmeticFunction.sigma_one_apply_prime_pow (p := 2) (i := 0) Nat.prime_two
  rw [h_sig]
  decide

lemma sigma_pow_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℤ) = 3 := by
  have h_sig := ArithmeticFunction.sigma_one_apply_prime_pow (p := 2) (i := 1) Nat.prime_two
  rw [h_sig]
  decide

lemma sigma_pow_2_2 : (ArithmeticFunction.sigma 1 (2^2) : ℤ) = 7 := by
  have h_sig := ArithmeticFunction.sigma_one_apply_prime_pow (p := 2) (i := 2) Nat.prime_two
  rw [h_sig]
  decide

lemma sigma_pow_2_3 : (ArithmeticFunction.sigma 1 (2^3) : ℤ) = 15 := by
  have h_sig := ArithmeticFunction.sigma_one_apply_prime_pow (p := 2) (i := 3) Nat.prime_two
  rw [h_sig]
  decide

lemma sigma_pow_2_4 : (ArithmeticFunction.sigma 1 (2^4) : ℤ) = 31 := by
  have h_sig := ArithmeticFunction.sigma_one_apply_prime_pow (p := 2) (i := 4) Nat.prime_two
  rw [h_sig]
  decide

lemma sigma_pow_2_5 : (ArithmeticFunction.sigma 1 (2^5) : ℤ) = 63 := by
  have h_sig := ArithmeticFunction.sigma_one_apply_prime_pow (p := 2) (i := 5) Nat.prime_two
  rw [h_sig]
  decide

lemma sigma_pow_2_6 : (ArithmeticFunction.sigma 1 (2^6) : ℤ) = 127 := by
  have h_sig := ArithmeticFunction.sigma_one_apply_prime_pow (p := 2) (i := 6) Nat.prime_two
  rw [h_sig]
  decide

lemma sigma_pow_2_7 : (ArithmeticFunction.sigma 1 (2^7) : ℤ) = 255 := by
  have h_sig := ArithmeticFunction.sigma_one_apply_prime_pow (p := 2) (i := 7) Nat.prime_two
  rw [h_sig]
  decide

lemma sigma_pow_2_8 : (ArithmeticFunction.sigma 1 (2^8) : ℤ) = 511 := by
  have h_sig := ArithmeticFunction.sigma_one_apply_prime_pow (p := 2) (i := 8) Nat.prime_two
  rw [h_sig]
  decide

lemma sigma_pow_2_9 : (ArithmeticFunction.sigma 1 (2^9) : ℤ) = 1023 := by
  have h_sig := ArithmeticFunction.sigma_one_apply_prime_pow (p := 2) (i := 9) Nat.prime_two
  rw [h_sig]
  decide

lemma sigma_pow_2_10 : (ArithmeticFunction.sigma 1 (2^10) : ℤ) = 2047 := by
  have h_sig := ArithmeticFunction.sigma_one_apply_prime_pow (p := 2) (i := 10) Nat.prime_two
  rw [h_sig]
  decide

lemma sigma_pow_2_11 : (ArithmeticFunction.sigma 1 (2^11) : ℤ) = 4095 := by
  have h_sig := ArithmeticFunction.sigma_one_apply_prime_pow (p := 2) (i := 11) Nat.prime_two
  rw [h_sig]
  decide

lemma sigma_pow_2_12 : (ArithmeticFunction.sigma 1 (2^12) : ℤ) = 8191 := by
  have h_sig := ArithmeticFunction.sigma_one_apply_prime_pow (p := 2) (i := 12) Nat.prime_two
  rw [h_sig]
  decide

lemma sigma_pow_2_13 : (ArithmeticFunction.sigma 1 (2^13) : ℤ) = 16383 := by
  have h_sig := ArithmeticFunction.sigma_one_apply_prime_pow (p := 2) (i := 13) Nat.prime_two
  rw [h_sig]
  decide

lemma sigma_pow_2_14 : (ArithmeticFunction.sigma 1 (2^14) : ℤ) = 32767 := by
  have h_sig := ArithmeticFunction.sigma_one_apply_prime_pow (p := 2) (i := 14) Nat.prime_two
  rw [h_sig]
  decide

lemma sigma_4409 : (ArithmeticFunction.sigma 1 (4409^1) : ℤ) = 4410 := by
  have h_prime : Nat.Prime 4409 := by norm_num
  have h_sig := ArithmeticFunction.sigma_one_apply_prime_pow (p := 4409) (i := 1) h_prime
  rw [h_sig]
  decide

lemma sigma_458009 : (ArithmeticFunction.sigma 1 (458009^1) : ℤ) = 458010 := by
  have h_prime : Nat.Prime 458009 := by norm_num
  have h_sig := ArithmeticFunction.sigma_one_apply_prime_pow (p := 458009) (i := 1) h_prime
  rw [h_sig]
  decide

lemma sigma_eq_0 : (ArithmeticFunction.sigma 1 (2^0 * 4409^0 * 458009^0) : ℤ) = 1 := by
  have h_simp : 2^0 * 4409^0 * 458009^0 = 2^0 := rfl
  rw [h_simp]
  exact sigma_pow_2_0

lemma sigma_eq_1 : (ArithmeticFunction.sigma 1 (2^1 * 4409^0 * 458009^0) : ℤ) = 3 := by
  have h_simp : 2^1 * 4409^0 * 458009^0 = 2^1 := rfl
  rw [h_simp]
  exact sigma_pow_2_1

lemma sigma_eq_2 : (ArithmeticFunction.sigma 1 (2^2 * 4409^0 * 458009^0) : ℤ) = 7 := by
  have h_simp : 2^2 * 4409^0 * 458009^0 = 2^2 := rfl
  rw [h_simp]
  exact sigma_pow_2_2

lemma sigma_eq_3 : (ArithmeticFunction.sigma 1 (2^3 * 4409^0 * 458009^0) : ℤ) = 15 := by
  have h_simp : 2^3 * 4409^0 * 458009^0 = 2^3 := rfl
  rw [h_simp]
  exact sigma_pow_2_3

lemma sigma_eq_4 : (ArithmeticFunction.sigma 1 (2^4 * 4409^0 * 458009^0) : ℤ) = 31 := by
  have h_simp : 2^4 * 4409^0 * 458009^0 = 2^4 := rfl
  rw [h_simp]
  exact sigma_pow_2_4

lemma sigma_eq_5 : (ArithmeticFunction.sigma 1 (2^5 * 4409^0 * 458009^0) : ℤ) = 63 := by
  have h_simp : 2^5 * 4409^0 * 458009^0 = 2^5 := rfl
  rw [h_simp]
  exact sigma_pow_2_5

lemma sigma_eq_6 : (ArithmeticFunction.sigma 1 (2^6 * 4409^0 * 458009^0) : ℤ) = 127 := by
  have h_simp : 2^6 * 4409^0 * 458009^0 = 2^6 := rfl
  rw [h_simp]
  exact sigma_pow_2_6

lemma sigma_eq_7 : (ArithmeticFunction.sigma 1 (2^7 * 4409^0 * 458009^0) : ℤ) = 255 := by
  have h_simp : 2^7 * 4409^0 * 458009^0 = 2^7 := rfl
  rw [h_simp]
  exact sigma_pow_2_7

lemma sigma_eq_8 : (ArithmeticFunction.sigma 1 (2^8 * 4409^0 * 458009^0) : ℤ) = 511 := by
  have h_simp : 2^8 * 4409^0 * 458009^0 = 2^8 := rfl
  rw [h_simp]
  exact sigma_pow_2_8

lemma sigma_eq_9 : (ArithmeticFunction.sigma 1 (2^9 * 4409^0 * 458009^0) : ℤ) = 1023 := by
  have h_simp : 2^9 * 4409^0 * 458009^0 = 2^9 := rfl
  rw [h_simp]
  exact sigma_pow_2_9

lemma sigma_eq_10 : (ArithmeticFunction.sigma 1 (2^10 * 4409^0 * 458009^0) : ℤ) = 2047 := by
  have h_simp : 2^10 * 4409^0 * 458009^0 = 2^10 := rfl
  rw [h_simp]
  exact sigma_pow_2_10

lemma sigma_eq_11 : (ArithmeticFunction.sigma 1 (2^11 * 4409^0 * 458009^0) : ℤ) = 4095 := by
  have h_simp : 2^11 * 4409^0 * 458009^0 = 2^11 := rfl
  rw [h_simp]
  exact sigma_pow_2_11

lemma sigma_eq_12 : (ArithmeticFunction.sigma 1 (2^12 * 4409^0 * 458009^0) : ℤ) = 8191 := by
  have h_simp : 2^12 * 4409^0 * 458009^0 = 2^12 := rfl
  rw [h_simp]
  exact sigma_pow_2_12

lemma sigma_eq_13 : (ArithmeticFunction.sigma 1 (2^0 * 4409^1 * 458009^0) : ℤ) = 4410 := by
  have h_simp : 2^0 * 4409^1 * 458009^0 = 2^0 * 4409^1 := rfl
  rw [h_simp]
  have h_cop : Coprime (2^0) (4409^1) := by decide
  have h_mul := ArithmeticFunction.IsMultiplicative.map_mul_of_coprime (f := ArithmeticFunction.sigma 1) (ArithmeticFunction.isMultiplicative_sigma (k := 1)) h_cop
  let A := ArithmeticFunction.sigma 1 (2^0)
  let B := ArithmeticFunction.sigma 1 (4409^1)
  have h_cast : (↑(A * B) : ℤ) = (↑A : ℤ) * (↑B : ℤ) := Nat.cast_mul A B
  rw [h_mul, h_cast]
  have h1 : (ArithmeticFunction.sigma 1 (2^0) : ℤ) = 1 := sigma_pow_2_0
  have h2 : (ArithmeticFunction.sigma 1 (4409^1) : ℤ) = 4410 := sigma_4409
  rw [h1, h2]
  decide

lemma sigma_eq_14 : (ArithmeticFunction.sigma 1 (2^13 * 4409^0 * 458009^0) : ℤ) = 16383 := by
  have h_simp : 2^13 * 4409^0 * 458009^0 = 2^13 := rfl
  rw [h_simp]
  exact sigma_pow_2_13

lemma sigma_eq_15 : (ArithmeticFunction.sigma 1 (2^1 * 4409^1 * 458009^0) : ℤ) = 13230 := by
  have h_simp : 2^1 * 4409^1 * 458009^0 = 2^1 * 4409^1 := rfl
  rw [h_simp]
  have h_cop : Coprime (2^1) (4409^1) := by decide
  have h_mul := ArithmeticFunction.IsMultiplicative.map_mul_of_coprime (f := ArithmeticFunction.sigma 1) (ArithmeticFunction.isMultiplicative_sigma (k := 1)) h_cop
  let A := ArithmeticFunction.sigma 1 (2^1)
  let B := ArithmeticFunction.sigma 1 (4409^1)
  have h_cast : (↑(A * B) : ℤ) = (↑A : ℤ) * (↑B : ℤ) := Nat.cast_mul A B
  rw [h_mul, h_cast]
  have h1 : (ArithmeticFunction.sigma 1 (2^1) : ℤ) = 3 := sigma_pow_2_1
  have h2 : (ArithmeticFunction.sigma 1 (4409^1) : ℤ) = 4410 := sigma_4409
  rw [h1, h2]
  decide

lemma sigma_eq_16 : (ArithmeticFunction.sigma 1 (2^14 * 4409^0 * 458009^0) : ℤ) = 32767 := by
  have h_simp : 2^14 * 4409^0 * 458009^0 = 2^14 := rfl
  rw [h_simp]
  exact sigma_pow_2_14

lemma sigma_eq_17 : (ArithmeticFunction.sigma 1 (2^2 * 4409^1 * 458009^0) : ℤ) = 30870 := by
  have h_simp : 2^2 * 4409^1 * 458009^0 = 2^2 * 4409^1 := rfl
  rw [h_simp]
  have h_cop : Coprime (2^2) (4409^1) := by decide
  have h_mul := ArithmeticFunction.IsMultiplicative.map_mul_of_coprime (f := ArithmeticFunction.sigma 1) (ArithmeticFunction.isMultiplicative_sigma (k := 1)) h_cop
  let A := ArithmeticFunction.sigma 1 (2^2)
  let B := ArithmeticFunction.sigma 1 (4409^1)
  have h_cast : (↑(A * B) : ℤ) = (↑A : ℤ) * (↑B : ℤ) := Nat.cast_mul A B
  rw [h_mul, h_cast]
  have h1 : (ArithmeticFunction.sigma 1 (2^2) : ℤ) = 7 := sigma_pow_2_2
  have h2 : (ArithmeticFunction.sigma 1 (4409^1) : ℤ) = 4410 := sigma_4409
  rw [h1, h2]
  decide

lemma sigma_eq_18 : (ArithmeticFunction.sigma 1 (2^3 * 4409^1 * 458009^0) : ℤ) = 66150 := by
  have h_simp : 2^3 * 4409^1 * 458009^0 = 2^3 * 4409^1 := rfl
  rw [h_simp]
  have h_cop : Coprime (2^3) (4409^1) := by decide
  have h_mul := ArithmeticFunction.IsMultiplicative.map_mul_of_coprime (f := ArithmeticFunction.sigma 1) (ArithmeticFunction.isMultiplicative_sigma (k := 1)) h_cop
  let A := ArithmeticFunction.sigma 1 (2^3)
  let B := ArithmeticFunction.sigma 1 (4409^1)
  have h_cast : (↑(A * B) : ℤ) = (↑A : ℤ) * (↑B : ℤ) := Nat.cast_mul A B
  rw [h_mul, h_cast]
  have h1 : (ArithmeticFunction.sigma 1 (2^3) : ℤ) = 15 := sigma_pow_2_3
  have h2 : (ArithmeticFunction.sigma 1 (4409^1) : ℤ) = 4410 := sigma_4409
  rw [h1, h2]
  decide

lemma sigma_eq_19 : (ArithmeticFunction.sigma 1 (2^4 * 4409^1 * 458009^0) : ℤ) = 136710 := by
  have h_simp : 2^4 * 4409^1 * 458009^0 = 2^4 * 4409^1 := rfl
  rw [h_simp]
  have h_cop : Coprime (2^4) (4409^1) := by decide
  have h_mul := ArithmeticFunction.IsMultiplicative.map_mul_of_coprime (f := ArithmeticFunction.sigma 1) (ArithmeticFunction.isMultiplicative_sigma (k := 1)) h_cop
  let A := ArithmeticFunction.sigma 1 (2^4)
  let B := ArithmeticFunction.sigma 1 (4409^1)
  have h_cast : (↑(A * B) : ℤ) = (↑A : ℤ) * (↑B : ℤ) := Nat.cast_mul A B
  rw [h_mul, h_cast]
  have h1 : (ArithmeticFunction.sigma 1 (2^4) : ℤ) = 31 := sigma_pow_2_4
  have h2 : (ArithmeticFunction.sigma 1 (4409^1) : ℤ) = 4410 := sigma_4409
  rw [h1, h2]
  decide

lemma sigma_eq_20 : (ArithmeticFunction.sigma 1 (2^5 * 4409^1 * 458009^0) : ℤ) = 277830 := by
  have h_simp : 2^5 * 4409^1 * 458009^0 = 2^5 * 4409^1 := rfl
  rw [h_simp]
  have h_cop : Coprime (2^5) (4409^1) := by decide
  have h_mul := ArithmeticFunction.IsMultiplicative.map_mul_of_coprime (f := ArithmeticFunction.sigma 1) (ArithmeticFunction.isMultiplicative_sigma (k := 1)) h_cop
  let A := ArithmeticFunction.sigma 1 (2^5)
  let B := ArithmeticFunction.sigma 1 (4409^1)
  have h_cast : (↑(A * B) : ℤ) = (↑A : ℤ) * (↑B : ℤ) := Nat.cast_mul A B
  rw [h_mul, h_cast]
  have h1 : (ArithmeticFunction.sigma 1 (2^5) : ℤ) = 63 := sigma_pow_2_5
  have h2 : (ArithmeticFunction.sigma 1 (4409^1) : ℤ) = 4410 := sigma_4409
  rw [h1, h2]
  decide

lemma sigma_eq_21 : (ArithmeticFunction.sigma 1 (2^6 * 4409^1 * 458009^0) : ℤ) = 560070 := by
  have h_simp : 2^6 * 4409^1 * 458009^0 = 2^6 * 4409^1 := rfl
  rw [h_simp]
  have h_cop : Coprime (2^6) (4409^1) := by decide
  have h_mul := ArithmeticFunction.IsMultiplicative.map_mul_of_coprime (f := ArithmeticFunction.sigma 1) (ArithmeticFunction.isMultiplicative_sigma (k := 1)) h_cop
  let A := ArithmeticFunction.sigma 1 (2^6)
  let B := ArithmeticFunction.sigma 1 (4409^1)
  have h_cast : (↑(A * B) : ℤ) = (↑A : ℤ) * (↑B : ℤ) := Nat.cast_mul A B
  rw [h_mul, h_cast]
  have h1 : (ArithmeticFunction.sigma 1 (2^6) : ℤ) = 127 := sigma_pow_2_6
  have h2 : (ArithmeticFunction.sigma 1 (4409^1) : ℤ) = 4410 := sigma_4409
  rw [h1, h2]
  decide

lemma sigma_eq_22 : (ArithmeticFunction.sigma 1 (2^0 * 4409^0 * 458009^1) : ℤ) = 458010 := by
  have h_simp : 2^0 * 4409^0 * 458009^1 = 2^0 * 458009^1 := rfl
  rw [h_simp]
  have h_cop : Coprime (2^0) (458009^1) := by decide
  have h_mul := ArithmeticFunction.IsMultiplicative.map_mul_of_coprime (f := ArithmeticFunction.sigma 1) (ArithmeticFunction.isMultiplicative_sigma (k := 1)) h_cop
  let A := ArithmeticFunction.sigma 1 (2^0)
  let B := ArithmeticFunction.sigma 1 (458009^1)
  have h_cast : (↑(A * B) : ℤ) = (↑A : ℤ) * (↑B : ℤ) := Nat.cast_mul A B
  rw [h_mul, h_cast]
  have h1 : (ArithmeticFunction.sigma 1 (2^0) : ℤ) = 1 := sigma_pow_2_0
  have h2 : (ArithmeticFunction.sigma 1 (458009^1) : ℤ) = 458010 := sigma_458009
  rw [h1, h2]
  decide

lemma sigma_eq_23 : (ArithmeticFunction.sigma 1 (2^7 * 4409^1 * 458009^0) : ℤ) = 1124550 := by
  have h_simp : 2^7 * 4409^1 * 458009^0 = 2^7 * 4409^1 := rfl
  rw [h_simp]
  have h_cop : Coprime (2^7) (4409^1) := by decide
  have h_mul := ArithmeticFunction.IsMultiplicative.map_mul_of_coprime (f := ArithmeticFunction.sigma 1) (ArithmeticFunction.isMultiplicative_sigma (k := 1)) h_cop
  let A := ArithmeticFunction.sigma 1 (2^7)
  let B := ArithmeticFunction.sigma 1 (4409^1)
  have h_cast : (↑(A * B) : ℤ) = (↑A : ℤ) * (↑B : ℤ) := Nat.cast_mul A B
  rw [h_mul, h_cast]
  have h1 : (ArithmeticFunction.sigma 1 (2^7) : ℤ) = 255 := sigma_pow_2_7
  have h2 : (ArithmeticFunction.sigma 1 (4409^1) : ℤ) = 4410 := sigma_4409
  rw [h1, h2]
  decide

lemma sigma_eq_24 : (ArithmeticFunction.sigma 1 (2^1 * 4409^0 * 458009^1) : ℤ) = 1374030 := by
  have h_simp : 2^1 * 4409^0 * 458009^1 = 2^1 * 458009^1 := rfl
  rw [h_simp]
  have h_cop : Coprime (2^1) (458009^1) := by decide
  have h_mul := ArithmeticFunction.IsMultiplicative.map_mul_of_coprime (f := ArithmeticFunction.sigma 1) (ArithmeticFunction.isMultiplicative_sigma (k := 1)) h_cop
  let A := ArithmeticFunction.sigma 1 (2^1)
  let B := ArithmeticFunction.sigma 1 (458009^1)
  have h_cast : (↑(A * B) : ℤ) = (↑A : ℤ) * (↑B : ℤ) := Nat.cast_mul A B
  rw [h_mul, h_cast]
  have h1 : (ArithmeticFunction.sigma 1 (2^1) : ℤ) = 3 := sigma_pow_2_1
  have h2 : (ArithmeticFunction.sigma 1 (458009^1) : ℤ) = 458010 := sigma_458009
  rw [h1, h2]
  decide

lemma sigma_eq_25 : (ArithmeticFunction.sigma 1 (2^8 * 4409^1 * 458009^0) : ℤ) = 2253510 := by
  have h_simp : 2^8 * 4409^1 * 458009^0 = 2^8 * 4409^1 := rfl
  rw [h_simp]
  have h_cop : Coprime (2^8) (4409^1) := by decide
  have h_mul := ArithmeticFunction.IsMultiplicative.map_mul_of_coprime (f := ArithmeticFunction.sigma 1) (ArithmeticFunction.isMultiplicative_sigma (k := 1)) h_cop
  let A := ArithmeticFunction.sigma 1 (2^8)
  let B := ArithmeticFunction.sigma 1 (4409^1)
  have h_cast : (↑(A * B) : ℤ) = (↑A : ℤ) * (↑B : ℤ) := Nat.cast_mul A B
  rw [h_mul, h_cast]
  have h1 : (ArithmeticFunction.sigma 1 (2^8) : ℤ) = 511 := sigma_pow_2_8
  have h2 : (ArithmeticFunction.sigma 1 (4409^1) : ℤ) = 4410 := sigma_4409
  rw [h1, h2]
  decide

lemma sigma_eq_26 : (ArithmeticFunction.sigma 1 (2^2 * 4409^0 * 458009^1) : ℤ) = 3206070 := by
  have h_simp : 2^2 * 4409^0 * 458009^1 = 2^2 * 458009^1 := rfl
  rw [h_simp]
  have h_cop : Coprime (2^2) (458009^1) := by decide
  have h_mul := ArithmeticFunction.IsMultiplicative.map_mul_of_coprime (f := ArithmeticFunction.sigma 1) (ArithmeticFunction.isMultiplicative_sigma (k := 1)) h_cop
  let A := ArithmeticFunction.sigma 1 (2^2)
  let B := ArithmeticFunction.sigma 1 (458009^1)
  have h_cast : (↑(A * B) : ℤ) = (↑A : ℤ) * (↑B : ℤ) := Nat.cast_mul A B
  rw [h_mul, h_cast]
  have h1 : (ArithmeticFunction.sigma 1 (2^2) : ℤ) = 7 := sigma_pow_2_2
  have h2 : (ArithmeticFunction.sigma 1 (458009^1) : ℤ) = 458010 := sigma_458009
  rw [h1, h2]
  decide

lemma sigma_eq_27 : (ArithmeticFunction.sigma 1 (2^9 * 4409^1 * 458009^0) : ℤ) = 4511430 := by
  have h_simp : 2^9 * 4409^1 * 458009^0 = 2^9 * 4409^1 := rfl
  rw [h_simp]
  have h_cop : Coprime (2^9) (4409^1) := by decide
  have h_mul := ArithmeticFunction.IsMultiplicative.map_mul_of_coprime (f := ArithmeticFunction.sigma 1) (ArithmeticFunction.isMultiplicative_sigma (k := 1)) h_cop
  let A := ArithmeticFunction.sigma 1 (2^9)
  let B := ArithmeticFunction.sigma 1 (4409^1)
  have h_cast : (↑(A * B) : ℤ) = (↑A : ℤ) * (↑B : ℤ) := Nat.cast_mul A B
  rw [h_mul, h_cast]
  have h1 : (ArithmeticFunction.sigma 1 (2^9) : ℤ) = 1023 := sigma_pow_2_9
  have h2 : (ArithmeticFunction.sigma 1 (4409^1) : ℤ) = 4410 := sigma_4409
  rw [h1, h2]
  decide

lemma sigma_eq_28 : (ArithmeticFunction.sigma 1 (2^3 * 4409^0 * 458009^1) : ℤ) = 6870150 := by
  have h_simp : 2^3 * 4409^0 * 458009^1 = 2^3 * 458009^1 := rfl
  rw [h_simp]
  have h_cop : Coprime (2^3) (458009^1) := by decide
  have h_mul := ArithmeticFunction.IsMultiplicative.map_mul_of_coprime (f := ArithmeticFunction.sigma 1) (ArithmeticFunction.isMultiplicative_sigma (k := 1)) h_cop
  let A := ArithmeticFunction.sigma 1 (2^3)
  let B := ArithmeticFunction.sigma 1 (458009^1)
  have h_cast : (↑(A * B) : ℤ) = (↑A : ℤ) * (↑B : ℤ) := Nat.cast_mul A B
  rw [h_mul, h_cast]
  have h1 : (ArithmeticFunction.sigma 1 (2^3) : ℤ) = 15 := sigma_pow_2_3
  have h2 : (ArithmeticFunction.sigma 1 (458009^1) : ℤ) = 458010 := sigma_458009
  rw [h1, h2]
  decide

lemma sigma_eq_29 : (ArithmeticFunction.sigma 1 (2^10 * 4409^1 * 458009^0) : ℤ) = 9027270 := by
  have h_simp : 2^10 * 4409^1 * 458009^0 = 2^10 * 4409^1 := rfl
  rw [h_simp]
  have h_cop : Coprime (2^10) (4409^1) := by decide
  have h_mul := ArithmeticFunction.IsMultiplicative.map_mul_of_coprime (f := ArithmeticFunction.sigma 1) (ArithmeticFunction.isMultiplicative_sigma (k := 1)) h_cop
  let A := ArithmeticFunction.sigma 1 (2^10)
  let B := ArithmeticFunction.sigma 1 (4409^1)
  have h_cast : (↑(A * B) : ℤ) = (↑A : ℤ) * (↑B : ℤ) := Nat.cast_mul A B
  rw [h_mul, h_cast]
  have h1 : (ArithmeticFunction.sigma 1 (2^10) : ℤ) = 2047 := sigma_pow_2_10
  have h2 : (ArithmeticFunction.sigma 1 (4409^1) : ℤ) = 4410 := sigma_4409
  rw [h1, h2]
  decide

lemma sigma_eq_30 : (ArithmeticFunction.sigma 1 (2^4 * 4409^0 * 458009^1) : ℤ) = 14198310 := by
  have h_simp : 2^4 * 4409^0 * 458009^1 = 2^4 * 458009^1 := rfl
  rw [h_simp]
  have h_cop : Coprime (2^4) (458009^1) := by decide
  have h_mul := ArithmeticFunction.IsMultiplicative.map_mul_of_coprime (f := ArithmeticFunction.sigma 1) (ArithmeticFunction.isMultiplicative_sigma (k := 1)) h_cop
  let A := ArithmeticFunction.sigma 1 (2^4)
  let B := ArithmeticFunction.sigma 1 (458009^1)
  have h_cast : (↑(A * B) : ℤ) = (↑A : ℤ) * (↑B : ℤ) := Nat.cast_mul A B
  rw [h_mul, h_cast]
  have h1 : (ArithmeticFunction.sigma 1 (2^4) : ℤ) = 31 := sigma_pow_2_4
  have h2 : (ArithmeticFunction.sigma 1 (458009^1) : ℤ) = 458010 := sigma_458009
  rw [h1, h2]
  decide

lemma sigma_eq_31 : (ArithmeticFunction.sigma 1 (2^11 * 4409^1 * 458009^0) : ℤ) = 18058950 := by
  have h_simp : 2^11 * 4409^1 * 458009^0 = 2^11 * 4409^1 := rfl
  rw [h_simp]
  have h_cop : Coprime (2^11) (4409^1) := by decide
  have h_mul := ArithmeticFunction.IsMultiplicative.map_mul_of_coprime (f := ArithmeticFunction.sigma 1) (ArithmeticFunction.isMultiplicative_sigma (k := 1)) h_cop
  let A := ArithmeticFunction.sigma 1 (2^11)
  let B := ArithmeticFunction.sigma 1 (4409^1)
  have h_cast : (↑(A * B) : ℤ) = (↑A : ℤ) * (↑B : ℤ) := Nat.cast_mul A B
  rw [h_mul, h_cast]
  have h1 : (ArithmeticFunction.sigma 1 (2^11) : ℤ) = 4095 := sigma_pow_2_11
  have h2 : (ArithmeticFunction.sigma 1 (4409^1) : ℤ) = 4410 := sigma_4409
  rw [h1, h2]
  decide

lemma sigma_eq_32 : (ArithmeticFunction.sigma 1 (2^5 * 4409^0 * 458009^1) : ℤ) = 28854630 := by
  have h_simp : 2^5 * 4409^0 * 458009^1 = 2^5 * 458009^1 := rfl
  rw [h_simp]
  have h_cop : Coprime (2^5) (458009^1) := by decide
  have h_mul := ArithmeticFunction.IsMultiplicative.map_mul_of_coprime (f := ArithmeticFunction.sigma 1) (ArithmeticFunction.isMultiplicative_sigma (k := 1)) h_cop
  let A := ArithmeticFunction.sigma 1 (2^5)
  let B := ArithmeticFunction.sigma 1 (458009^1)
  have h_cast : (↑(A * B) : ℤ) = (↑A : ℤ) * (↑B : ℤ) := Nat.cast_mul A B
  rw [h_mul, h_cast]
  have h1 : (ArithmeticFunction.sigma 1 (2^5) : ℤ) = 63 := sigma_pow_2_5
  have h2 : (ArithmeticFunction.sigma 1 (458009^1) : ℤ) = 458010 := sigma_458009
  rw [h1, h2]
  decide

lemma sigma_eq_33 : (ArithmeticFunction.sigma 1 (2^12 * 4409^1 * 458009^0) : ℤ) = 36122310 := by
  have h_simp : 2^12 * 4409^1 * 458009^0 = 2^12 * 4409^1 := rfl
  rw [h_simp]
  have h_cop : Coprime (2^12) (4409^1) := by decide
  have h_mul := ArithmeticFunction.IsMultiplicative.map_mul_of_coprime (f := ArithmeticFunction.sigma 1) (ArithmeticFunction.isMultiplicative_sigma (k := 1)) h_cop
  let A := ArithmeticFunction.sigma 1 (2^12)
  let B := ArithmeticFunction.sigma 1 (4409^1)
  have h_cast : (↑(A * B) : ℤ) = (↑A : ℤ) * (↑B : ℤ) := Nat.cast_mul A B
  rw [h_mul, h_cast]
  have h1 : (ArithmeticFunction.sigma 1 (2^12) : ℤ) = 8191 := sigma_pow_2_12
  have h2 : (ArithmeticFunction.sigma 1 (4409^1) : ℤ) = 4410 := sigma_4409
  rw [h1, h2]
  decide

lemma sigma_eq_34 : (ArithmeticFunction.sigma 1 (2^6 * 4409^0 * 458009^1) : ℤ) = 58167270 := by
  have h_simp : 2^6 * 4409^0 * 458009^1 = 2^6 * 458009^1 := rfl
  rw [h_simp]
  have h_cop : Coprime (2^6) (458009^1) := by decide
  have h_mul := ArithmeticFunction.IsMultiplicative.map_mul_of_coprime (f := ArithmeticFunction.sigma 1) (ArithmeticFunction.isMultiplicative_sigma (k := 1)) h_cop
  let A := ArithmeticFunction.sigma 1 (2^6)
  let B := ArithmeticFunction.sigma 1 (458009^1)
  have h_cast : (↑(A * B) : ℤ) = (↑A : ℤ) * (↑B : ℤ) := Nat.cast_mul A B
  rw [h_mul, h_cast]
  have h1 : (ArithmeticFunction.sigma 1 (2^6) : ℤ) = 127 := sigma_pow_2_6
  have h2 : (ArithmeticFunction.sigma 1 (458009^1) : ℤ) = 458010 := sigma_458009
  rw [h1, h2]
  decide

lemma sigma_eq_35 : (ArithmeticFunction.sigma 1 (2^13 * 4409^1 * 458009^0) : ℤ) = 72249030 := by
  have h_simp : 2^13 * 4409^1 * 458009^0 = 2^13 * 4409^1 := rfl
  rw [h_simp]
  have h_cop : Coprime (2^13) (4409^1) := by decide
  have h_mul := ArithmeticFunction.IsMultiplicative.map_mul_of_coprime (f := ArithmeticFunction.sigma 1) (ArithmeticFunction.isMultiplicative_sigma (k := 1)) h_cop
  let A := ArithmeticFunction.sigma 1 (2^13)
  let B := ArithmeticFunction.sigma 1 (4409^1)
  have h_cast : (↑(A * B) : ℤ) = (↑A : ℤ) * (↑B : ℤ) := Nat.cast_mul A B
  rw [h_mul, h_cast]
  have h1 : (ArithmeticFunction.sigma 1 (2^13) : ℤ) = 16383 := sigma_pow_2_13
  have h2 : (ArithmeticFunction.sigma 1 (4409^1) : ℤ) = 4410 := sigma_4409
  rw [h1, h2]
  decide

lemma sigma_eq_36 : (ArithmeticFunction.sigma 1 (2^7 * 4409^0 * 458009^1) : ℤ) = 116792550 := by
  have h_simp : 2^7 * 4409^0 * 458009^1 = 2^7 * 458009^1 := rfl
  rw [h_simp]
  have h_cop : Coprime (2^7) (458009^1) := by decide
  have h_mul := ArithmeticFunction.IsMultiplicative.map_mul_of_coprime (f := ArithmeticFunction.sigma 1) (ArithmeticFunction.isMultiplicative_sigma (k := 1)) h_cop
  let A := ArithmeticFunction.sigma 1 (2^7)
  let B := ArithmeticFunction.sigma 1 (458009^1)
  have h_cast : (↑(A * B) : ℤ) = (↑A : ℤ) * (↑B : ℤ) := Nat.cast_mul A B
  rw [h_mul, h_cast]
  have h1 : (ArithmeticFunction.sigma 1 (2^7) : ℤ) = 255 := sigma_pow_2_7
  have h2 : (ArithmeticFunction.sigma 1 (458009^1) : ℤ) = 458010 := sigma_458009
  rw [h1, h2]
  decide

lemma sigma_eq_37 : (ArithmeticFunction.sigma 1 (2^14 * 4409^1 * 458009^0) : ℤ) = 144502470 := by
  have h_simp : 2^14 * 4409^1 * 458009^0 = 2^14 * 4409^1 := rfl
  rw [h_simp]
  have h_cop : Coprime (2^14) (4409^1) := by decide
  have h_mul := ArithmeticFunction.IsMultiplicative.map_mul_of_coprime (f := ArithmeticFunction.sigma 1) (ArithmeticFunction.isMultiplicative_sigma (k := 1)) h_cop
  let A := ArithmeticFunction.sigma 1 (2^14)
  let B := ArithmeticFunction.sigma 1 (4409^1)
  have h_cast : (↑(A * B) : ℤ) = (↑A : ℤ) * (↑B : ℤ) := Nat.cast_mul A B
  rw [h_mul, h_cast]
  have h1 : (ArithmeticFunction.sigma 1 (2^14) : ℤ) = 32767 := sigma_pow_2_14
  have h2 : (ArithmeticFunction.sigma 1 (4409^1) : ℤ) = 4410 := sigma_4409
  rw [h1, h2]
  decide

lemma sigma_eq_38 : (ArithmeticFunction.sigma 1 (2^8 * 4409^0 * 458009^1) : ℤ) = 234043110 := by
  have h_simp : 2^8 * 4409^0 * 458009^1 = 2^8 * 458009^1 := rfl
  rw [h_simp]
  have h_cop : Coprime (2^8) (458009^1) := by decide
  have h_mul := ArithmeticFunction.IsMultiplicative.map_mul_of_coprime (f := ArithmeticFunction.sigma 1) (ArithmeticFunction.isMultiplicative_sigma (k := 1)) h_cop
  let A := ArithmeticFunction.sigma 1 (2^8)
  let B := ArithmeticFunction.sigma 1 (458009^1)
  have h_cast : (↑(A * B) : ℤ) = (↑A : ℤ) * (↑B : ℤ) := Nat.cast_mul A B
  rw [h_mul, h_cast]
  have h1 : (ArithmeticFunction.sigma 1 (2^8) : ℤ) = 511 := sigma_pow_2_8
  have h2 : (ArithmeticFunction.sigma 1 (458009^1) : ℤ) = 458010 := sigma_458009
  rw [h1, h2]
  decide

lemma sigma_eq_39 : (ArithmeticFunction.sigma 1 (2^9 * 4409^0 * 458009^1) : ℤ) = 468544230 := by
  have h_simp : 2^9 * 4409^0 * 458009^1 = 2^9 * 458009^1 := rfl
  rw [h_simp]
  have h_cop : Coprime (2^9) (458009^1) := by decide
  have h_mul := ArithmeticFunction.IsMultiplicative.map_mul_of_coprime (f := ArithmeticFunction.sigma 1) (ArithmeticFunction.isMultiplicative_sigma (k := 1)) h_cop
  let A := ArithmeticFunction.sigma 1 (2^9)
  let B := ArithmeticFunction.sigma 1 (458009^1)
  have h_cast : (↑(A * B) : ℤ) = (↑A : ℤ) * (↑B : ℤ) := Nat.cast_mul A B
  rw [h_mul, h_cast]
  have h1 : (ArithmeticFunction.sigma 1 (2^9) : ℤ) = 1023 := sigma_pow_2_9
  have h2 : (ArithmeticFunction.sigma 1 (458009^1) : ℤ) = 458010 := sigma_458009
  rw [h1, h2]
  decide

lemma sigma_eq_40 : (ArithmeticFunction.sigma 1 (2^10 * 4409^0 * 458009^1) : ℤ) = 937546470 := by
  have h_simp : 2^10 * 4409^0 * 458009^1 = 2^10 * 458009^1 := rfl
  rw [h_simp]
  have h_cop : Coprime (2^10) (458009^1) := by decide
  have h_mul := ArithmeticFunction.IsMultiplicative.map_mul_of_coprime (f := ArithmeticFunction.sigma 1) (ArithmeticFunction.isMultiplicative_sigma (k := 1)) h_cop
  let A := ArithmeticFunction.sigma 1 (2^10)
  let B := ArithmeticFunction.sigma 1 (458009^1)
  have h_cast : (↑(A * B) : ℤ) = (↑A : ℤ) * (↑B : ℤ) := Nat.cast_mul A B
  rw [h_mul, h_cast]
  have h1 : (ArithmeticFunction.sigma 1 (2^10) : ℤ) = 2047 := sigma_pow_2_10
  have h2 : (ArithmeticFunction.sigma 1 (458009^1) : ℤ) = 458010 := sigma_458009
  rw [h1, h2]
  decide

lemma sigma_eq_41 : (ArithmeticFunction.sigma 1 (2^11 * 4409^0 * 458009^1) : ℤ) = 1875550950 := by
  have h_simp : 2^11 * 4409^0 * 458009^1 = 2^11 * 458009^1 := rfl
  rw [h_simp]
  have h_cop : Coprime (2^11) (458009^1) := by decide
  have h_mul := ArithmeticFunction.IsMultiplicative.map_mul_of_coprime (f := ArithmeticFunction.sigma 1) (ArithmeticFunction.isMultiplicative_sigma (k := 1)) h_cop
  let A := ArithmeticFunction.sigma 1 (2^11)
  let B := ArithmeticFunction.sigma 1 (458009^1)
  have h_cast : (↑(A * B) : ℤ) = (↑A : ℤ) * (↑B : ℤ) := Nat.cast_mul A B
  rw [h_mul, h_cast]
  have h1 : (ArithmeticFunction.sigma 1 (2^11) : ℤ) = 4095 := sigma_pow_2_11
  have h2 : (ArithmeticFunction.sigma 1 (458009^1) : ℤ) = 458010 := sigma_458009
  rw [h1, h2]
  decide

lemma sigma_eq_42 : (ArithmeticFunction.sigma 1 (2^12 * 4409^0 * 458009^1) : ℤ) = 3751559910 := by
  have h_simp : 2^12 * 4409^0 * 458009^1 = 2^12 * 458009^1 := rfl
  rw [h_simp]
  have h_cop : Coprime (2^12) (458009^1) := by decide
  have h_mul := ArithmeticFunction.IsMultiplicative.map_mul_of_coprime (f := ArithmeticFunction.sigma 1) (ArithmeticFunction.isMultiplicative_sigma (k := 1)) h_cop
  let A := ArithmeticFunction.sigma 1 (2^12)
  let B := ArithmeticFunction.sigma 1 (458009^1)
  have h_cast : (↑(A * B) : ℤ) = (↑A : ℤ) * (↑B : ℤ) := Nat.cast_mul A B
  rw [h_mul, h_cast]
  have h1 : (ArithmeticFunction.sigma 1 (2^12) : ℤ) = 8191 := sigma_pow_2_12
  have h2 : (ArithmeticFunction.sigma 1 (458009^1) : ℤ) = 458010 := sigma_458009
  rw [h1, h2]
  decide

lemma sigma_eq_43 : (ArithmeticFunction.sigma 1 (2^0 * 4409^1 * 458009^1) : ℤ) = 2019824100 := by
  have h_cop : Coprime (2^0) (4409^1 * 458009^1) := by decide
  have h_mul := ArithmeticFunction.IsMultiplicative.map_mul_of_coprime (f := ArithmeticFunction.sigma 1) (ArithmeticFunction.isMultiplicative_sigma (k := 1)) h_cop
  rw [mul_assoc]
  let A := ArithmeticFunction.sigma 1 (2^0)
  let B := ArithmeticFunction.sigma 1 (4409^1 * 458009^1)
  have h_cast : (↑(A * B) : ℤ) = (↑A : ℤ) * (↑B : ℤ) := Nat.cast_mul A B
  rw [h_mul, h_cast]
  have h1 : (ArithmeticFunction.sigma 1 (2^0) : ℤ) = 1 := sigma_pow_2_0
  have h2 : (ArithmeticFunction.sigma 1 (4409^1 * 458009^1) : ℤ) = 2019824100 := by
    have h_cop2 : Coprime (4409^1) (458009^1) := by decide
    have h_mul2 := ArithmeticFunction.IsMultiplicative.map_mul_of_coprime (f := ArithmeticFunction.sigma 1) (ArithmeticFunction.isMultiplicative_sigma (k := 1)) h_cop2
    let A2 := ArithmeticFunction.sigma 1 (4409^1)
    let B2 := ArithmeticFunction.sigma 1 (458009^1)
    have h_cast2 : (↑(A2 * B2) : ℤ) = (↑A2 : ℤ) * (↑B2 : ℤ) := Nat.cast_mul A2 B2
    rw [h_mul2, h_cast2]
    have ha : (ArithmeticFunction.sigma 1 (4409^1) : ℤ) = 4410 := sigma_4409
    have hb : (ArithmeticFunction.sigma 1 (458009^1) : ℤ) = 458010 := sigma_458009
    rw [ha, hb]
    decide
  rw [h1, h2]
  decide

lemma sigma_eq_44 : (ArithmeticFunction.sigma 1 (2^13 * 4409^0 * 458009^1) : ℤ) = 7503577830 := by
  have h_simp : 2^13 * 4409^0 * 458009^1 = 2^13 * 458009^1 := rfl
  rw [h_simp]
  have h_cop : Coprime (2^13) (458009^1) := by decide
  have h_mul := ArithmeticFunction.IsMultiplicative.map_mul_of_coprime (f := ArithmeticFunction.sigma 1) (ArithmeticFunction.isMultiplicative_sigma (k := 1)) h_cop
  let A := ArithmeticFunction.sigma 1 (2^13)
  let B := ArithmeticFunction.sigma 1 (458009^1)
  have h_cast : (↑(A * B) : ℤ) = (↑A : ℤ) * (↑B : ℤ) := Nat.cast_mul A B
  rw [h_mul, h_cast]
  have h1 : (ArithmeticFunction.sigma 1 (2^13) : ℤ) = 16383 := sigma_pow_2_13
  have h2 : (ArithmeticFunction.sigma 1 (458009^1) : ℤ) = 458010 := sigma_458009
  rw [h1, h2]
  decide

lemma sigma_eq_45 : (ArithmeticFunction.sigma 1 (2^1 * 4409^1 * 458009^1) : ℤ) = 6059472300 := by
  have h_cop : Coprime (2^1) (4409^1 * 458009^1) := by decide
  have h_mul := ArithmeticFunction.IsMultiplicative.map_mul_of_coprime (f := ArithmeticFunction.sigma 1) (ArithmeticFunction.isMultiplicative_sigma (k := 1)) h_cop
  rw [mul_assoc]
  let A := ArithmeticFunction.sigma 1 (2^1)
  let B := ArithmeticFunction.sigma 1 (4409^1 * 458009^1)
  have h_cast : (↑(A * B) : ℤ) = (↑A : ℤ) * (↑B : ℤ) := Nat.cast_mul A B
  rw [h_mul, h_cast]
  have h1 : (ArithmeticFunction.sigma 1 (2^1) : ℤ) = 3 := sigma_pow_2_1
  have h2 : (ArithmeticFunction.sigma 1 (4409^1 * 458009^1) : ℤ) = 2019824100 := by
    have h_cop2 : Coprime (4409^1) (458009^1) := by decide
    have h_mul2 := ArithmeticFunction.IsMultiplicative.map_mul_of_coprime (f := ArithmeticFunction.sigma 1) (ArithmeticFunction.isMultiplicative_sigma (k := 1)) h_cop2
    let A2 := ArithmeticFunction.sigma 1 (4409^1)
    let B2 := ArithmeticFunction.sigma 1 (458009^1)
    have h_cast2 : (↑(A2 * B2) : ℤ) = (↑A2 : ℤ) * (↑B2 : ℤ) := Nat.cast_mul A2 B2
    rw [h_mul2, h_cast2]
    have ha : (ArithmeticFunction.sigma 1 (4409^1) : ℤ) = 4410 := sigma_4409
    have hb : (ArithmeticFunction.sigma 1 (458009^1) : ℤ) = 458010 := sigma_458009
    rw [ha, hb]
    decide
  rw [h1, h2]
  decide

lemma sigma_eq_46 : (ArithmeticFunction.sigma 1 (2^14 * 4409^0 * 458009^1) : ℤ) = 15007613670 := by
  have h_simp : 2^14 * 4409^0 * 458009^1 = 2^14 * 458009^1 := rfl
  rw [h_simp]
  have h_cop : Coprime (2^14) (458009^1) := by decide
  have h_mul := ArithmeticFunction.IsMultiplicative.map_mul_of_coprime (f := ArithmeticFunction.sigma 1) (ArithmeticFunction.isMultiplicative_sigma (k := 1)) h_cop
  let A := ArithmeticFunction.sigma 1 (2^14)
  let B := ArithmeticFunction.sigma 1 (458009^1)
  have h_cast : (↑(A * B) : ℤ) = (↑A : ℤ) * (↑B : ℤ) := Nat.cast_mul A B
  rw [h_mul, h_cast]
  have h1 : (ArithmeticFunction.sigma 1 (2^14) : ℤ) = 32767 := sigma_pow_2_14
  have h2 : (ArithmeticFunction.sigma 1 (458009^1) : ℤ) = 458010 := sigma_458009
  rw [h1, h2]
  decide

lemma sigma_eq_47 : (ArithmeticFunction.sigma 1 (2^2 * 4409^1 * 458009^1) : ℤ) = 14138768700 := by
  have h_cop : Coprime (2^2) (4409^1 * 458009^1) := by decide
  have h_mul := ArithmeticFunction.IsMultiplicative.map_mul_of_coprime (f := ArithmeticFunction.sigma 1) (ArithmeticFunction.isMultiplicative_sigma (k := 1)) h_cop
  rw [mul_assoc]
  let A := ArithmeticFunction.sigma 1 (2^2)
  let B := ArithmeticFunction.sigma 1 (4409^1 * 458009^1)
  have h_cast : (↑(A * B) : ℤ) = (↑A : ℤ) * (↑B : ℤ) := Nat.cast_mul A B
  rw [h_mul, h_cast]
  have h1 : (ArithmeticFunction.sigma 1 (2^2) : ℤ) = 7 := sigma_pow_2_2
  have h2 : (ArithmeticFunction.sigma 1 (4409^1 * 458009^1) : ℤ) = 2019824100 := by
    have h_cop2 : Coprime (4409^1) (458009^1) := by decide
    have h_mul2 := ArithmeticFunction.IsMultiplicative.map_mul_of_coprime (f := ArithmeticFunction.sigma 1) (ArithmeticFunction.isMultiplicative_sigma (k := 1)) h_cop2
    let A2 := ArithmeticFunction.sigma 1 (4409^1)
    let B2 := ArithmeticFunction.sigma 1 (458009^1)
    have h_cast2 : (↑(A2 * B2) : ℤ) = (↑A2 : ℤ) * (↑B2 : ℤ) := Nat.cast_mul A2 B2
    rw [h_mul2, h_cast2]
    have ha : (ArithmeticFunction.sigma 1 (4409^1) : ℤ) = 4410 := sigma_4409
    have hb : (ArithmeticFunction.sigma 1 (458009^1) : ℤ) = 458010 := sigma_458009
    rw [ha, hb]
    decide
  rw [h1, h2]
  decide

lemma sigma_eq_48 : (ArithmeticFunction.sigma 1 (2^3 * 4409^1 * 458009^1) : ℤ) = 30297361500 := by
  have h_cop : Coprime (2^3) (4409^1 * 458009^1) := by decide
  have h_mul := ArithmeticFunction.IsMultiplicative.map_mul_of_coprime (f := ArithmeticFunction.sigma 1) (ArithmeticFunction.isMultiplicative_sigma (k := 1)) h_cop
  rw [mul_assoc]
  let A := ArithmeticFunction.sigma 1 (2^3)
  let B := ArithmeticFunction.sigma 1 (4409^1 * 458009^1)
  have h_cast : (↑(A * B) : ℤ) = (↑A : ℤ) * (↑B : ℤ) := Nat.cast_mul A B
  rw [h_mul, h_cast]
  have h1 : (ArithmeticFunction.sigma 1 (2^3) : ℤ) = 15 := sigma_pow_2_3
  have h2 : (ArithmeticFunction.sigma 1 (4409^1 * 458009^1) : ℤ) = 2019824100 := by
    have h_cop2 : Coprime (4409^1) (458009^1) := by decide
    have h_mul2 := ArithmeticFunction.IsMultiplicative.map_mul_of_coprime (f := ArithmeticFunction.sigma 1) (ArithmeticFunction.isMultiplicative_sigma (k := 1)) h_cop2
    let A2 := ArithmeticFunction.sigma 1 (4409^1)
    let B2 := ArithmeticFunction.sigma 1 (458009^1)
    have h_cast2 : (↑(A2 * B2) : ℤ) = (↑A2 : ℤ) * (↑B2 : ℤ) := Nat.cast_mul A2 B2
    rw [h_mul2, h_cast2]
    have ha : (ArithmeticFunction.sigma 1 (4409^1) : ℤ) = 4410 := sigma_4409
    have hb : (ArithmeticFunction.sigma 1 (458009^1) : ℤ) = 458010 := sigma_458009
    rw [ha, hb]
    decide
  rw [h1, h2]
  decide

lemma sigma_eq_49 : (ArithmeticFunction.sigma 1 (2^4 * 4409^1 * 458009^1) : ℤ) = 62614547100 := by
  have h_cop : Coprime (2^4) (4409^1 * 458009^1) := by decide
  have h_mul := ArithmeticFunction.IsMultiplicative.map_mul_of_coprime (f := ArithmeticFunction.sigma 1) (ArithmeticFunction.isMultiplicative_sigma (k := 1)) h_cop
  rw [mul_assoc]
  let A := ArithmeticFunction.sigma 1 (2^4)
  let B := ArithmeticFunction.sigma 1 (4409^1 * 458009^1)
  have h_cast : (↑(A * B) : ℤ) = (↑A : ℤ) * (↑B : ℤ) := Nat.cast_mul A B
  rw [h_mul, h_cast]
  have h1 : (ArithmeticFunction.sigma 1 (2^4) : ℤ) = 31 := sigma_pow_2_4
  have h2 : (ArithmeticFunction.sigma 1 (4409^1 * 458009^1) : ℤ) = 2019824100 := by
    have h_cop2 : Coprime (4409^1) (458009^1) := by decide
    have h_mul2 := ArithmeticFunction.IsMultiplicative.map_mul_of_coprime (f := ArithmeticFunction.sigma 1) (ArithmeticFunction.isMultiplicative_sigma (k := 1)) h_cop2
    let A2 := ArithmeticFunction.sigma 1 (4409^1)
    let B2 := ArithmeticFunction.sigma 1 (458009^1)
    have h_cast2 : (↑(A2 * B2) : ℤ) = (↑A2 : ℤ) * (↑B2 : ℤ) := Nat.cast_mul A2 B2
    rw [h_mul2, h_cast2]
    have ha : (ArithmeticFunction.sigma 1 (4409^1) : ℤ) = 4410 := sigma_4409
    have hb : (ArithmeticFunction.sigma 1 (458009^1) : ℤ) = 458010 := sigma_458009
    rw [ha, hb]
    decide
  rw [h1, h2]
  decide

lemma sigma_eq_50 : (ArithmeticFunction.sigma 1 (2^5 * 4409^1 * 458009^1) : ℤ) = 127248918300 := by
  have h_cop : Coprime (2^5) (4409^1 * 458009^1) := by decide
  have h_mul := ArithmeticFunction.IsMultiplicative.map_mul_of_coprime (f := ArithmeticFunction.sigma 1) (ArithmeticFunction.isMultiplicative_sigma (k := 1)) h_cop
  rw [mul_assoc]
  let A := ArithmeticFunction.sigma 1 (2^5)
  let B := ArithmeticFunction.sigma 1 (4409^1 * 458009^1)
  have h_cast : (↑(A * B) : ℤ) = (↑A : ℤ) * (↑B : ℤ) := Nat.cast_mul A B
  rw [h_mul, h_cast]
  have h1 : (ArithmeticFunction.sigma 1 (2^5) : ℤ) = 63 := sigma_pow_2_5
  have h2 : (ArithmeticFunction.sigma 1 (4409^1 * 458009^1) : ℤ) = 2019824100 := by
    have h_cop2 : Coprime (4409^1) (458009^1) := by decide
    have h_mul2 := ArithmeticFunction.IsMultiplicative.map_mul_of_coprime (f := ArithmeticFunction.sigma 1) (ArithmeticFunction.isMultiplicative_sigma (k := 1)) h_cop2
    let A2 := ArithmeticFunction.sigma 1 (4409^1)
    let B2 := ArithmeticFunction.sigma 1 (458009^1)
    have h_cast2 : (↑(A2 * B2) : ℤ) = (↑A2 : ℤ) * (↑B2 : ℤ) := Nat.cast_mul A2 B2
    rw [h_mul2, h_cast2]
    have ha : (ArithmeticFunction.sigma 1 (4409^1) : ℤ) = 4410 := sigma_4409
    have hb : (ArithmeticFunction.sigma 1 (458009^1) : ℤ) = 458010 := sigma_458009
    rw [ha, hb]
    decide
  rw [h1, h2]
  decide

lemma sigma_eq_51 : (ArithmeticFunction.sigma 1 (2^6 * 4409^1 * 458009^1) : ℤ) = 256517660700 := by
  have h_cop : Coprime (2^6) (4409^1 * 458009^1) := by decide
  have h_mul := ArithmeticFunction.IsMultiplicative.map_mul_of_coprime (f := ArithmeticFunction.sigma 1) (ArithmeticFunction.isMultiplicative_sigma (k := 1)) h_cop
  rw [mul_assoc]
  let A := ArithmeticFunction.sigma 1 (2^6)
  let B := ArithmeticFunction.sigma 1 (4409^1 * 458009^1)
  have h_cast : (↑(A * B) : ℤ) = (↑A : ℤ) * (↑B : ℤ) := Nat.cast_mul A B
  rw [h_mul, h_cast]
  have h1 : (ArithmeticFunction.sigma 1 (2^6) : ℤ) = 127 := sigma_pow_2_6
  have h2 : (ArithmeticFunction.sigma 1 (4409^1 * 458009^1) : ℤ) = 2019824100 := by
    have h_cop2 : Coprime (4409^1) (458009^1) := by decide
    have h_mul2 := ArithmeticFunction.IsMultiplicative.map_mul_of_coprime (f := ArithmeticFunction.sigma 1) (ArithmeticFunction.isMultiplicative_sigma (k := 1)) h_cop2
    let A2 := ArithmeticFunction.sigma 1 (4409^1)
    let B2 := ArithmeticFunction.sigma 1 (458009^1)
    have h_cast2 : (↑(A2 * B2) : ℤ) = (↑A2 : ℤ) * (↑B2 : ℤ) := Nat.cast_mul A2 B2
    rw [h_mul2, h_cast2]
    have ha : (ArithmeticFunction.sigma 1 (4409^1) : ℤ) = 4410 := sigma_4409
    have hb : (ArithmeticFunction.sigma 1 (458009^1) : ℤ) = 458010 := sigma_458009
    rw [ha, hb]
    decide
  rw [h1, h2]
  decide

lemma sigma_eq_52 : (ArithmeticFunction.sigma 1 (2^7 * 4409^1 * 458009^1) : ℤ) = 515055145500 := by
  have h_cop : Coprime (2^7) (4409^1 * 458009^1) := by decide
  have h_mul := ArithmeticFunction.IsMultiplicative.map_mul_of_coprime (f := ArithmeticFunction.sigma 1) (ArithmeticFunction.isMultiplicative_sigma (k := 1)) h_cop
  rw [mul_assoc]
  let A := ArithmeticFunction.sigma 1 (2^7)
  let B := ArithmeticFunction.sigma 1 (4409^1 * 458009^1)
  have h_cast : (↑(A * B) : ℤ) = (↑A : ℤ) * (↑B : ℤ) := Nat.cast_mul A B
  rw [h_mul, h_cast]
  have h1 : (ArithmeticFunction.sigma 1 (2^7) : ℤ) = 255 := sigma_pow_2_7
  have h2 : (ArithmeticFunction.sigma 1 (4409^1 * 458009^1) : ℤ) = 2019824100 := by
    have h_cop2 : Coprime (4409^1) (458009^1) := by decide
    have h_mul2 := ArithmeticFunction.IsMultiplicative.map_mul_of_coprime (f := ArithmeticFunction.sigma 1) (ArithmeticFunction.isMultiplicative_sigma (k := 1)) h_cop2
    let A2 := ArithmeticFunction.sigma 1 (4409^1)
    let B2 := ArithmeticFunction.sigma 1 (458009^1)
    have h_cast2 : (↑(A2 * B2) : ℤ) = (↑A2 : ℤ) * (↑B2 : ℤ) := Nat.cast_mul A2 B2
    rw [h_mul2, h_cast2]
    have ha : (ArithmeticFunction.sigma 1 (4409^1) : ℤ) = 4410 := sigma_4409
    have hb : (ArithmeticFunction.sigma 1 (458009^1) : ℤ) = 458010 := sigma_458009
    rw [ha, hb]
    decide
  rw [h1, h2]
  decide

lemma sigma_eq_53 : (ArithmeticFunction.sigma 1 (2^8 * 4409^1 * 458009^1) : ℤ) = 1032130115100 := by
  have h_cop : Coprime (2^8) (4409^1 * 458009^1) := by decide
  have h_mul := ArithmeticFunction.IsMultiplicative.map_mul_of_coprime (f := ArithmeticFunction.sigma 1) (ArithmeticFunction.isMultiplicative_sigma (k := 1)) h_cop
  rw [mul_assoc]
  let A := ArithmeticFunction.sigma 1 (2^8)
  let B := ArithmeticFunction.sigma 1 (4409^1 * 458009^1)
  have h_cast : (↑(A * B) : ℤ) = (↑A : ℤ) * (↑B : ℤ) := Nat.cast_mul A B
  rw [h_mul, h_cast]
  have h1 : (ArithmeticFunction.sigma 1 (2^8) : ℤ) = 511 := sigma_pow_2_8
  have h2 : (ArithmeticFunction.sigma 1 (4409^1 * 458009^1) : ℤ) = 2019824100 := by
    have h_cop2 : Coprime (4409^1) (458009^1) := by decide
    have h_mul2 := ArithmeticFunction.IsMultiplicative.map_mul_of_coprime (f := ArithmeticFunction.sigma 1) (ArithmeticFunction.isMultiplicative_sigma (k := 1)) h_cop2
    let A2 := ArithmeticFunction.sigma 1 (4409^1)
    let B2 := ArithmeticFunction.sigma 1 (458009^1)
    have h_cast2 : (↑(A2 * B2) : ℤ) = (↑A2 : ℤ) * (↑B2 : ℤ) := Nat.cast_mul A2 B2
    rw [h_mul2, h_cast2]
    have ha : (ArithmeticFunction.sigma 1 (4409^1) : ℤ) = 4410 := sigma_4409
    have hb : (ArithmeticFunction.sigma 1 (458009^1) : ℤ) = 458010 := sigma_458009
    rw [ha, hb]
    decide
  rw [h1, h2]
  decide

lemma sigma_eq_54 : (ArithmeticFunction.sigma 1 (2^9 * 4409^1 * 458009^1) : ℤ) = 2066280054300 := by
  have h_cop : Coprime (2^9) (4409^1 * 458009^1) := by decide
  have h_mul := ArithmeticFunction.IsMultiplicative.map_mul_of_coprime (f := ArithmeticFunction.sigma 1) (ArithmeticFunction.isMultiplicative_sigma (k := 1)) h_cop
  rw [mul_assoc]
  let A := ArithmeticFunction.sigma 1 (2^9)
  let B := ArithmeticFunction.sigma 1 (4409^1 * 458009^1)
  have h_cast : (↑(A * B) : ℤ) = (↑A : ℤ) * (↑B : ℤ) := Nat.cast_mul A B
  rw [h_mul, h_cast]
  have h1 : (ArithmeticFunction.sigma 1 (2^9) : ℤ) = 1023 := sigma_pow_2_9
  have h2 : (ArithmeticFunction.sigma 1 (4409^1 * 458009^1) : ℤ) = 2019824100 := by
    have h_cop2 : Coprime (4409^1) (458009^1) := by decide
    have h_mul2 := ArithmeticFunction.IsMultiplicative.map_mul_of_coprime (f := ArithmeticFunction.sigma 1) (ArithmeticFunction.isMultiplicative_sigma (k := 1)) h_cop2
    let A2 := ArithmeticFunction.sigma 1 (4409^1)
    let B2 := ArithmeticFunction.sigma 1 (458009^1)
    have h_cast2 : (↑(A2 * B2) : ℤ) = (↑A2 : ℤ) * (↑B2 : ℤ) := Nat.cast_mul A2 B2
    rw [h_mul2, h_cast2]
    have ha : (ArithmeticFunction.sigma 1 (4409^1) : ℤ) = 4410 := sigma_4409
    have hb : (ArithmeticFunction.sigma 1 (458009^1) : ℤ) = 458010 := sigma_458009
    rw [ha, hb]
    decide
  rw [h1, h2]
  decide

lemma sigma_eq_55 : (ArithmeticFunction.sigma 1 (2^10 * 4409^1 * 458009^1) : ℤ) = 4134579932700 := by
  have h_cop : Coprime (2^10) (4409^1 * 458009^1) := by decide
  have h_mul := ArithmeticFunction.IsMultiplicative.map_mul_of_coprime (f := ArithmeticFunction.sigma 1) (ArithmeticFunction.isMultiplicative_sigma (k := 1)) h_cop
  rw [mul_assoc]
  let A := ArithmeticFunction.sigma 1 (2^10)
  let B := ArithmeticFunction.sigma 1 (4409^1 * 458009^1)
  have h_cast : (↑(A * B) : ℤ) = (↑A : ℤ) * (↑B : ℤ) := Nat.cast_mul A B
  rw [h_mul, h_cast]
  have h1 : (ArithmeticFunction.sigma 1 (2^10) : ℤ) = 2047 := sigma_pow_2_10
  have h2 : (ArithmeticFunction.sigma 1 (4409^1 * 458009^1) : ℤ) = 2019824100 := by
    have h_cop2 : Coprime (4409^1) (458009^1) := by decide
    have h_mul2 := ArithmeticFunction.IsMultiplicative.map_mul_of_coprime (f := ArithmeticFunction.sigma 1) (ArithmeticFunction.isMultiplicative_sigma (k := 1)) h_cop2
    let A2 := ArithmeticFunction.sigma 1 (4409^1)
    let B2 := ArithmeticFunction.sigma 1 (458009^1)
    have h_cast2 : (↑(A2 * B2) : ℤ) = (↑A2 : ℤ) * (↑B2 : ℤ) := Nat.cast_mul A2 B2
    rw [h_mul2, h_cast2]
    have ha : (ArithmeticFunction.sigma 1 (4409^1) : ℤ) = 4410 := sigma_4409
    have hb : (ArithmeticFunction.sigma 1 (458009^1) : ℤ) = 458010 := sigma_458009
    rw [ha, hb]
    decide
  rw [h1, h2]
  decide

lemma sigma_eq_56 : (ArithmeticFunction.sigma 1 (2^11 * 4409^1 * 458009^1) : ℤ) = 8271179689500 := by
  have h_cop : Coprime (2^11) (4409^1 * 458009^1) := by decide
  have h_mul := ArithmeticFunction.IsMultiplicative.map_mul_of_coprime (f := ArithmeticFunction.sigma 1) (ArithmeticFunction.isMultiplicative_sigma (k := 1)) h_cop
  rw [mul_assoc]
  let A := ArithmeticFunction.sigma 1 (2^11)
  let B := ArithmeticFunction.sigma 1 (4409^1 * 458009^1)
  have h_cast : (↑(A * B) : ℤ) = (↑A : ℤ) * (↑B : ℤ) := Nat.cast_mul A B
  rw [h_mul, h_cast]
  have h1 : (ArithmeticFunction.sigma 1 (2^11) : ℤ) = 4095 := sigma_pow_2_11
  have h2 : (ArithmeticFunction.sigma 1 (4409^1 * 458009^1) : ℤ) = 2019824100 := by
    have h_cop2 : Coprime (4409^1) (458009^1) := by decide
    have h_mul2 := ArithmeticFunction.IsMultiplicative.map_mul_of_coprime (f := ArithmeticFunction.sigma 1) (ArithmeticFunction.isMultiplicative_sigma (k := 1)) h_cop2
    let A2 := ArithmeticFunction.sigma 1 (4409^1)
    let B2 := ArithmeticFunction.sigma 1 (458009^1)
    have h_cast2 : (↑(A2 * B2) : ℤ) = (↑A2 : ℤ) * (↑B2 : ℤ) := Nat.cast_mul A2 B2
    rw [h_mul2, h_cast2]
    have ha : (ArithmeticFunction.sigma 1 (4409^1) : ℤ) = 4410 := sigma_4409
    have hb : (ArithmeticFunction.sigma 1 (458009^1) : ℤ) = 458010 := sigma_458009
    rw [ha, hb]
    decide
  rw [h1, h2]
  decide

lemma sigma_eq_57 : (ArithmeticFunction.sigma 1 (2^12 * 4409^1 * 458009^1) : ℤ) = 16544379203100 := by
  have h_cop : Coprime (2^12) (4409^1 * 458009^1) := by decide
  have h_mul := ArithmeticFunction.IsMultiplicative.map_mul_of_coprime (f := ArithmeticFunction.sigma 1) (ArithmeticFunction.isMultiplicative_sigma (k := 1)) h_cop
  rw [mul_assoc]
  let A := ArithmeticFunction.sigma 1 (2^12)
  let B := ArithmeticFunction.sigma 1 (4409^1 * 458009^1)
  have h_cast : (↑(A * B) : ℤ) = (↑A : ℤ) * (↑B : ℤ) := Nat.cast_mul A B
  rw [h_mul, h_cast]
  have h1 : (ArithmeticFunction.sigma 1 (2^12) : ℤ) = 8191 := sigma_pow_2_12
  have h2 : (ArithmeticFunction.sigma 1 (4409^1 * 458009^1) : ℤ) = 2019824100 := by
    have h_cop2 : Coprime (4409^1) (458009^1) := by decide
    have h_mul2 := ArithmeticFunction.IsMultiplicative.map_mul_of_coprime (f := ArithmeticFunction.sigma 1) (ArithmeticFunction.isMultiplicative_sigma (k := 1)) h_cop2
    let A2 := ArithmeticFunction.sigma 1 (4409^1)
    let B2 := ArithmeticFunction.sigma 1 (458009^1)
    have h_cast2 : (↑(A2 * B2) : ℤ) = (↑A2 : ℤ) * (↑B2 : ℤ) := Nat.cast_mul A2 B2
    rw [h_mul2, h_cast2]
    have ha : (ArithmeticFunction.sigma 1 (4409^1) : ℤ) = 4410 := sigma_4409
    have hb : (ArithmeticFunction.sigma 1 (458009^1) : ℤ) = 458010 := sigma_458009
    rw [ha, hb]
    decide
  rw [h1, h2]
  decide

lemma sigma_eq_58 : (ArithmeticFunction.sigma 1 (2^13 * 4409^1 * 458009^1) : ℤ) = 33090778230300 := by
  have h_cop : Coprime (2^13) (4409^1 * 458009^1) := by decide
  have h_mul := ArithmeticFunction.IsMultiplicative.map_mul_of_coprime (f := ArithmeticFunction.sigma 1) (ArithmeticFunction.isMultiplicative_sigma (k := 1)) h_cop
  rw [mul_assoc]
  let A := ArithmeticFunction.sigma 1 (2^13)
  let B := ArithmeticFunction.sigma 1 (4409^1 * 458009^1)
  have h_cast : (↑(A * B) : ℤ) = (↑A : ℤ) * (↑B : ℤ) := Nat.cast_mul A B
  rw [h_mul, h_cast]
  have h1 : (ArithmeticFunction.sigma 1 (2^13) : ℤ) = 16383 := sigma_pow_2_13
  have h2 : (ArithmeticFunction.sigma 1 (4409^1 * 458009^1) : ℤ) = 2019824100 := by
    have h_cop2 : Coprime (4409^1) (458009^1) := by decide
    have h_mul2 := ArithmeticFunction.IsMultiplicative.map_mul_of_coprime (f := ArithmeticFunction.sigma 1) (ArithmeticFunction.isMultiplicative_sigma (k := 1)) h_cop2
    let A2 := ArithmeticFunction.sigma 1 (4409^1)
    let B2 := ArithmeticFunction.sigma 1 (458009^1)
    have h_cast2 : (↑(A2 * B2) : ℤ) = (↑A2 : ℤ) * (↑B2 : ℤ) := Nat.cast_mul A2 B2
    rw [h_mul2, h_cast2]
    have ha : (ArithmeticFunction.sigma 1 (4409^1) : ℤ) = 4410 := sigma_4409
    have hb : (ArithmeticFunction.sigma 1 (458009^1) : ℤ) = 458010 := sigma_458009
    rw [ha, hb]
    decide
  rw [h1, h2]
  decide

lemma sigma_eq_59 : (ArithmeticFunction.sigma 1 (2^14 * 4409^1 * 458009^1) : ℤ) = 66183576284700 := by
  have h_cop : Coprime (2^14) (4409^1 * 458009^1) := by decide
  have h_mul := ArithmeticFunction.IsMultiplicative.map_mul_of_coprime (f := ArithmeticFunction.sigma 1) (ArithmeticFunction.isMultiplicative_sigma (k := 1)) h_cop
  rw [mul_assoc]
  let A := ArithmeticFunction.sigma 1 (2^14)
  let B := ArithmeticFunction.sigma 1 (4409^1 * 458009^1)
  have h_cast : (↑(A * B) : ℤ) = (↑A : ℤ) * (↑B : ℤ) := Nat.cast_mul A B
  rw [h_mul, h_cast]
  have h1 : (ArithmeticFunction.sigma 1 (2^14) : ℤ) = 32767 := sigma_pow_2_14
  have h2 : (ArithmeticFunction.sigma 1 (4409^1 * 458009^1) : ℤ) = 2019824100 := by
    have h_cop2 : Coprime (4409^1) (458009^1) := by decide
    have h_mul2 := ArithmeticFunction.IsMultiplicative.map_mul_of_coprime (f := ArithmeticFunction.sigma 1) (ArithmeticFunction.isMultiplicative_sigma (k := 1)) h_cop2
    let A2 := ArithmeticFunction.sigma 1 (4409^1)
    let B2 := ArithmeticFunction.sigma 1 (458009^1)
    have h_cast2 : (↑(A2 * B2) : ℤ) = (↑A2 : ℤ) * (↑B2 : ℤ) := Nat.cast_mul A2 B2
    rw [h_mul2, h_cast2]
    have ha : (ArithmeticFunction.sigma 1 (4409^1) : ℤ) = 4410 := sigma_4409
    have hb : (ArithmeticFunction.sigma 1 (458009^1) : ℤ) = 458010 := sigma_458009
    rw [ha, hb]
    decide
  rw [h1, h2]
  decide

lemma f_eq_0 : ((2 * 1 : ℤ) - (ArithmeticFunction.sigma 1 1 : ℤ)) = 1 := by
  have h_eq : (2 * 1 : ℤ) - (ArithmeticFunction.sigma 1 1 : ℤ) = (2 * (2^0 * 4409^0 * 458009^0) : ℤ) - (ArithmeticFunction.sigma 1 (2^0 * 4409^0 * 458009^0) : ℤ) := rfl
  rw [h_eq]
  rw [sigma_eq_0]
  decide

lemma f_eq_1 : ((2 * 2 : ℤ) - (ArithmeticFunction.sigma 1 2 : ℤ)) = 1 := by
  have h_eq : (2 * 2 : ℤ) - (ArithmeticFunction.sigma 1 2 : ℤ) = (2 * (2^1 * 4409^0 * 458009^0) : ℤ) - (ArithmeticFunction.sigma 1 (2^1 * 4409^0 * 458009^0) : ℤ) := rfl
  rw [h_eq]
  rw [sigma_eq_1]
  decide

lemma f_eq_2 : ((2 * 4 : ℤ) - (ArithmeticFunction.sigma 1 4 : ℤ)) = 1 := by
  have h_eq : (2 * 4 : ℤ) - (ArithmeticFunction.sigma 1 4 : ℤ) = (2 * (2^2 * 4409^0 * 458009^0) : ℤ) - (ArithmeticFunction.sigma 1 (2^2 * 4409^0 * 458009^0) : ℤ) := rfl
  rw [h_eq]
  rw [sigma_eq_2]
  decide

lemma f_eq_3 : ((2 * 8 : ℤ) - (ArithmeticFunction.sigma 1 8 : ℤ)) = 1 := by
  have h_eq : (2 * 8 : ℤ) - (ArithmeticFunction.sigma 1 8 : ℤ) = (2 * (2^3 * 4409^0 * 458009^0) : ℤ) - (ArithmeticFunction.sigma 1 (2^3 * 4409^0 * 458009^0) : ℤ) := rfl
  rw [h_eq]
  rw [sigma_eq_3]
  decide

lemma f_eq_4 : ((2 * 16 : ℤ) - (ArithmeticFunction.sigma 1 16 : ℤ)) = 1 := by
  have h_eq : (2 * 16 : ℤ) - (ArithmeticFunction.sigma 1 16 : ℤ) = (2 * (2^4 * 4409^0 * 458009^0) : ℤ) - (ArithmeticFunction.sigma 1 (2^4 * 4409^0 * 458009^0) : ℤ) := rfl
  rw [h_eq]
  rw [sigma_eq_4]
  decide

lemma f_eq_5 : ((2 * 32 : ℤ) - (ArithmeticFunction.sigma 1 32 : ℤ)) = 1 := by
  have h_eq : (2 * 32 : ℤ) - (ArithmeticFunction.sigma 1 32 : ℤ) = (2 * (2^5 * 4409^0 * 458009^0) : ℤ) - (ArithmeticFunction.sigma 1 (2^5 * 4409^0 * 458009^0) : ℤ) := rfl
  rw [h_eq]
  rw [sigma_eq_5]
  decide

lemma f_eq_6 : ((2 * 64 : ℤ) - (ArithmeticFunction.sigma 1 64 : ℤ)) = 1 := by
  have h_eq : (2 * 64 : ℤ) - (ArithmeticFunction.sigma 1 64 : ℤ) = (2 * (2^6 * 4409^0 * 458009^0) : ℤ) - (ArithmeticFunction.sigma 1 (2^6 * 4409^0 * 458009^0) : ℤ) := rfl
  rw [h_eq]
  rw [sigma_eq_6]
  decide

lemma f_eq_7 : ((2 * 128 : ℤ) - (ArithmeticFunction.sigma 1 128 : ℤ)) = 1 := by
  have h_eq : (2 * 128 : ℤ) - (ArithmeticFunction.sigma 1 128 : ℤ) = (2 * (2^7 * 4409^0 * 458009^0) : ℤ) - (ArithmeticFunction.sigma 1 (2^7 * 4409^0 * 458009^0) : ℤ) := rfl
  rw [h_eq]
  rw [sigma_eq_7]
  decide

lemma f_eq_8 : ((2 * 256 : ℤ) - (ArithmeticFunction.sigma 1 256 : ℤ)) = 1 := by
  have h_eq : (2 * 256 : ℤ) - (ArithmeticFunction.sigma 1 256 : ℤ) = (2 * (2^8 * 4409^0 * 458009^0) : ℤ) - (ArithmeticFunction.sigma 1 (2^8 * 4409^0 * 458009^0) : ℤ) := rfl
  rw [h_eq]
  rw [sigma_eq_8]
  decide

lemma f_eq_9 : ((2 * 512 : ℤ) - (ArithmeticFunction.sigma 1 512 : ℤ)) = 1 := by
  have h_eq : (2 * 512 : ℤ) - (ArithmeticFunction.sigma 1 512 : ℤ) = (2 * (2^9 * 4409^0 * 458009^0) : ℤ) - (ArithmeticFunction.sigma 1 (2^9 * 4409^0 * 458009^0) : ℤ) := rfl
  rw [h_eq]
  rw [sigma_eq_9]
  decide

lemma f_eq_10 : ((2 * 1024 : ℤ) - (ArithmeticFunction.sigma 1 1024 : ℤ)) = 1 := by
  have h_eq : (2 * 1024 : ℤ) - (ArithmeticFunction.sigma 1 1024 : ℤ) = (2 * (2^10 * 4409^0 * 458009^0) : ℤ) - (ArithmeticFunction.sigma 1 (2^10 * 4409^0 * 458009^0) : ℤ) := rfl
  rw [h_eq]
  rw [sigma_eq_10]
  decide

lemma f_eq_11 : ((2 * 2048 : ℤ) - (ArithmeticFunction.sigma 1 2048 : ℤ)) = 1 := by
  have h_eq : (2 * 2048 : ℤ) - (ArithmeticFunction.sigma 1 2048 : ℤ) = (2 * (2^11 * 4409^0 * 458009^0) : ℤ) - (ArithmeticFunction.sigma 1 (2^11 * 4409^0 * 458009^0) : ℤ) := rfl
  rw [h_eq]
  rw [sigma_eq_11]
  decide

lemma f_eq_12 : ((2 * 4096 : ℤ) - (ArithmeticFunction.sigma 1 4096 : ℤ)) = 1 := by
  have h_eq : (2 * 4096 : ℤ) - (ArithmeticFunction.sigma 1 4096 : ℤ) = (2 * (2^12 * 4409^0 * 458009^0) : ℤ) - (ArithmeticFunction.sigma 1 (2^12 * 4409^0 * 458009^0) : ℤ) := rfl
  rw [h_eq]
  rw [sigma_eq_12]
  decide

lemma f_eq_13 : ((2 * 4409 : ℤ) - (ArithmeticFunction.sigma 1 4409 : ℤ)) = 4408 := by
  have h_eq : (2 * 4409 : ℤ) - (ArithmeticFunction.sigma 1 4409 : ℤ) = (2 * (2^0 * 4409^1 * 458009^0) : ℤ) - (ArithmeticFunction.sigma 1 (2^0 * 4409^1 * 458009^0) : ℤ) := rfl
  rw [h_eq]
  rw [sigma_eq_13]
  decide

lemma f_eq_14 : ((2 * 8192 : ℤ) - (ArithmeticFunction.sigma 1 8192 : ℤ)) = 1 := by
  have h_eq : (2 * 8192 : ℤ) - (ArithmeticFunction.sigma 1 8192 : ℤ) = (2 * (2^13 * 4409^0 * 458009^0) : ℤ) - (ArithmeticFunction.sigma 1 (2^13 * 4409^0 * 458009^0) : ℤ) := rfl
  rw [h_eq]
  rw [sigma_eq_14]
  decide

lemma f_eq_15 : ((2 * 8818 : ℤ) - (ArithmeticFunction.sigma 1 8818 : ℤ)) = 4406 := by
  have h_eq : (2 * 8818 : ℤ) - (ArithmeticFunction.sigma 1 8818 : ℤ) = (2 * (2^1 * 4409^1 * 458009^0) : ℤ) - (ArithmeticFunction.sigma 1 (2^1 * 4409^1 * 458009^0) : ℤ) := rfl
  rw [h_eq]
  rw [sigma_eq_15]
  decide

lemma f_eq_16 : ((2 * 16384 : ℤ) - (ArithmeticFunction.sigma 1 16384 : ℤ)) = 1 := by
  have h_eq : (2 * 16384 : ℤ) - (ArithmeticFunction.sigma 1 16384 : ℤ) = (2 * (2^14 * 4409^0 * 458009^0) : ℤ) - (ArithmeticFunction.sigma 1 (2^14 * 4409^0 * 458009^0) : ℤ) := rfl
  rw [h_eq]
  rw [sigma_eq_16]
  decide

lemma f_eq_17 : ((2 * 17636 : ℤ) - (ArithmeticFunction.sigma 1 17636 : ℤ)) = 4402 := by
  have h_eq : (2 * 17636 : ℤ) - (ArithmeticFunction.sigma 1 17636 : ℤ) = (2 * (2^2 * 4409^1 * 458009^0) : ℤ) - (ArithmeticFunction.sigma 1 (2^2 * 4409^1 * 458009^0) : ℤ) := rfl
  rw [h_eq]
  rw [sigma_eq_17]
  decide

lemma f_eq_18 : ((2 * 35272 : ℤ) - (ArithmeticFunction.sigma 1 35272 : ℤ)) = 4394 := by
  have h_eq : (2 * 35272 : ℤ) - (ArithmeticFunction.sigma 1 35272 : ℤ) = (2 * (2^3 * 4409^1 * 458009^0) : ℤ) - (ArithmeticFunction.sigma 1 (2^3 * 4409^1 * 458009^0) : ℤ) := rfl
  rw [h_eq]
  rw [sigma_eq_18]
  decide

lemma f_eq_19 : ((2 * 70544 : ℤ) - (ArithmeticFunction.sigma 1 70544 : ℤ)) = 4378 := by
  have h_eq : (2 * 70544 : ℤ) - (ArithmeticFunction.sigma 1 70544 : ℤ) = (2 * (2^4 * 4409^1 * 458009^0) : ℤ) - (ArithmeticFunction.sigma 1 (2^4 * 4409^1 * 458009^0) : ℤ) := rfl
  rw [h_eq]
  rw [sigma_eq_19]
  decide

lemma f_eq_20 : ((2 * 141088 : ℤ) - (ArithmeticFunction.sigma 1 141088 : ℤ)) = 4346 := by
  have h_eq : (2 * 141088 : ℤ) - (ArithmeticFunction.sigma 1 141088 : ℤ) = (2 * (2^5 * 4409^1 * 458009^0) : ℤ) - (ArithmeticFunction.sigma 1 (2^5 * 4409^1 * 458009^0) : ℤ) := rfl
  rw [h_eq]
  rw [sigma_eq_20]
  decide

lemma f_eq_21 : ((2 * 282176 : ℤ) - (ArithmeticFunction.sigma 1 282176 : ℤ)) = 4282 := by
  have h_eq : (2 * 282176 : ℤ) - (ArithmeticFunction.sigma 1 282176 : ℤ) = (2 * (2^6 * 4409^1 * 458009^0) : ℤ) - (ArithmeticFunction.sigma 1 (2^6 * 4409^1 * 458009^0) : ℤ) := rfl
  rw [h_eq]
  rw [sigma_eq_21]
  decide

lemma f_eq_22 : ((2 * 458009 : ℤ) - (ArithmeticFunction.sigma 1 458009 : ℤ)) = 458008 := by
  have h_eq : (2 * 458009 : ℤ) - (ArithmeticFunction.sigma 1 458009 : ℤ) = (2 * (2^0 * 4409^0 * 458009^1) : ℤ) - (ArithmeticFunction.sigma 1 (2^0 * 4409^0 * 458009^1) : ℤ) := rfl
  rw [h_eq]
  rw [sigma_eq_22]
  decide

lemma f_eq_23 : ((2 * 564352 : ℤ) - (ArithmeticFunction.sigma 1 564352 : ℤ)) = 4154 := by
  have h_eq : (2 * 564352 : ℤ) - (ArithmeticFunction.sigma 1 564352 : ℤ) = (2 * (2^7 * 4409^1 * 458009^0) : ℤ) - (ArithmeticFunction.sigma 1 (2^7 * 4409^1 * 458009^0) : ℤ) := rfl
  rw [h_eq]
  rw [sigma_eq_23]
  decide

lemma f_eq_24 : ((2 * 916018 : ℤ) - (ArithmeticFunction.sigma 1 916018 : ℤ)) = 458006 := by
  have h_eq : (2 * 916018 : ℤ) - (ArithmeticFunction.sigma 1 916018 : ℤ) = (2 * (2^1 * 4409^0 * 458009^1) : ℤ) - (ArithmeticFunction.sigma 1 (2^1 * 4409^0 * 458009^1) : ℤ) := rfl
  rw [h_eq]
  rw [sigma_eq_24]
  decide

lemma f_eq_25 : ((2 * 1128704 : ℤ) - (ArithmeticFunction.sigma 1 1128704 : ℤ)) = 3898 := by
  have h_eq : (2 * 1128704 : ℤ) - (ArithmeticFunction.sigma 1 1128704 : ℤ) = (2 * (2^8 * 4409^1 * 458009^0) : ℤ) - (ArithmeticFunction.sigma 1 (2^8 * 4409^1 * 458009^0) : ℤ) := rfl
  rw [h_eq]
  rw [sigma_eq_25]
  decide

lemma f_eq_26 : ((2 * 1832036 : ℤ) - (ArithmeticFunction.sigma 1 1832036 : ℤ)) = 458002 := by
  have h_eq : (2 * 1832036 : ℤ) - (ArithmeticFunction.sigma 1 1832036 : ℤ) = (2 * (2^2 * 4409^0 * 458009^1) : ℤ) - (ArithmeticFunction.sigma 1 (2^2 * 4409^0 * 458009^1) : ℤ) := rfl
  rw [h_eq]
  rw [sigma_eq_26]
  decide

lemma f_eq_27 : ((2 * 2257408 : ℤ) - (ArithmeticFunction.sigma 1 2257408 : ℤ)) = 3386 := by
  have h_eq : (2 * 2257408 : ℤ) - (ArithmeticFunction.sigma 1 2257408 : ℤ) = (2 * (2^9 * 4409^1 * 458009^0) : ℤ) - (ArithmeticFunction.sigma 1 (2^9 * 4409^1 * 458009^0) : ℤ) := rfl
  rw [h_eq]
  rw [sigma_eq_27]
  decide

lemma f_eq_28 : ((2 * 3664072 : ℤ) - (ArithmeticFunction.sigma 1 3664072 : ℤ)) = 457994 := by
  have h_eq : (2 * 3664072 : ℤ) - (ArithmeticFunction.sigma 1 3664072 : ℤ) = (2 * (2^3 * 4409^0 * 458009^1) : ℤ) - (ArithmeticFunction.sigma 1 (2^3 * 4409^0 * 458009^1) : ℤ) := rfl
  rw [h_eq]
  rw [sigma_eq_28]
  decide

lemma f_eq_29 : ((2 * 4514816 : ℤ) - (ArithmeticFunction.sigma 1 4514816 : ℤ)) = 2362 := by
  have h_eq : (2 * 4514816 : ℤ) - (ArithmeticFunction.sigma 1 4514816 : ℤ) = (2 * (2^10 * 4409^1 * 458009^0) : ℤ) - (ArithmeticFunction.sigma 1 (2^10 * 4409^1 * 458009^0) : ℤ) := rfl
  rw [h_eq]
  rw [sigma_eq_29]
  decide

lemma f_eq_30 : ((2 * 7328144 : ℤ) - (ArithmeticFunction.sigma 1 7328144 : ℤ)) = 457978 := by
  have h_eq : (2 * 7328144 : ℤ) - (ArithmeticFunction.sigma 1 7328144 : ℤ) = (2 * (2^4 * 4409^0 * 458009^1) : ℤ) - (ArithmeticFunction.sigma 1 (2^4 * 4409^0 * 458009^1) : ℤ) := rfl
  rw [h_eq]
  rw [sigma_eq_30]
  decide

lemma f_eq_31 : ((2 * 9029632 : ℤ) - (ArithmeticFunction.sigma 1 9029632 : ℤ)) = 314 := by
  have h_eq : (2 * 9029632 : ℤ) - (ArithmeticFunction.sigma 1 9029632 : ℤ) = (2 * (2^11 * 4409^1 * 458009^0) : ℤ) - (ArithmeticFunction.sigma 1 (2^11 * 4409^1 * 458009^0) : ℤ) := rfl
  rw [h_eq]
  rw [sigma_eq_31]
  decide

lemma f_eq_32 : ((2 * 14656288 : ℤ) - (ArithmeticFunction.sigma 1 14656288 : ℤ)) = 457946 := by
  have h_eq : (2 * 14656288 : ℤ) - (ArithmeticFunction.sigma 1 14656288 : ℤ) = (2 * (2^5 * 4409^0 * 458009^1) : ℤ) - (ArithmeticFunction.sigma 1 (2^5 * 4409^0 * 458009^1) : ℤ) := rfl
  rw [h_eq]
  rw [sigma_eq_32]
  decide

lemma f_eq_33 : ((2 * 18059264 : ℤ) - (ArithmeticFunction.sigma 1 18059264 : ℤ)) = -3782 := by
  have h_eq : (2 * 18059264 : ℤ) - (ArithmeticFunction.sigma 1 18059264 : ℤ) = (2 * (2^12 * 4409^1 * 458009^0) : ℤ) - (ArithmeticFunction.sigma 1 (2^12 * 4409^1 * 458009^0) : ℤ) := rfl
  rw [h_eq]
  rw [sigma_eq_33]
  decide

lemma f_eq_34 : ((2 * 29312576 : ℤ) - (ArithmeticFunction.sigma 1 29312576 : ℤ)) = 457882 := by
  have h_eq : (2 * 29312576 : ℤ) - (ArithmeticFunction.sigma 1 29312576 : ℤ) = (2 * (2^6 * 4409^0 * 458009^1) : ℤ) - (ArithmeticFunction.sigma 1 (2^6 * 4409^0 * 458009^1) : ℤ) := rfl
  rw [h_eq]
  rw [sigma_eq_34]
  decide

lemma f_eq_35 : ((2 * 36118528 : ℤ) - (ArithmeticFunction.sigma 1 36118528 : ℤ)) = -11974 := by
  have h_eq : (2 * 36118528 : ℤ) - (ArithmeticFunction.sigma 1 36118528 : ℤ) = (2 * (2^13 * 4409^1 * 458009^0) : ℤ) - (ArithmeticFunction.sigma 1 (2^13 * 4409^1 * 458009^0) : ℤ) := rfl
  rw [h_eq]
  rw [sigma_eq_35]
  decide

lemma f_eq_36 : ((2 * 58625152 : ℤ) - (ArithmeticFunction.sigma 1 58625152 : ℤ)) = 457754 := by
  have h_eq : (2 * 58625152 : ℤ) - (ArithmeticFunction.sigma 1 58625152 : ℤ) = (2 * (2^7 * 4409^0 * 458009^1) : ℤ) - (ArithmeticFunction.sigma 1 (2^7 * 4409^0 * 458009^1) : ℤ) := rfl
  rw [h_eq]
  rw [sigma_eq_36]
  decide

lemma f_eq_37 : ((2 * 72237056 : ℤ) - (ArithmeticFunction.sigma 1 72237056 : ℤ)) = -28358 := by
  have h_eq : (2 * 72237056 : ℤ) - (ArithmeticFunction.sigma 1 72237056 : ℤ) = (2 * (2^14 * 4409^1 * 458009^0) : ℤ) - (ArithmeticFunction.sigma 1 (2^14 * 4409^1 * 458009^0) : ℤ) := rfl
  rw [h_eq]
  rw [sigma_eq_37]
  decide

lemma f_eq_38 : ((2 * 117250304 : ℤ) - (ArithmeticFunction.sigma 1 117250304 : ℤ)) = 457498 := by
  have h_eq : (2 * 117250304 : ℤ) - (ArithmeticFunction.sigma 1 117250304 : ℤ) = (2 * (2^8 * 4409^0 * 458009^1) : ℤ) - (ArithmeticFunction.sigma 1 (2^8 * 4409^0 * 458009^1) : ℤ) := rfl
  rw [h_eq]
  rw [sigma_eq_38]
  decide

lemma f_eq_39 : ((2 * 234500608 : ℤ) - (ArithmeticFunction.sigma 1 234500608 : ℤ)) = 456986 := by
  have h_eq : (2 * 234500608 : ℤ) - (ArithmeticFunction.sigma 1 234500608 : ℤ) = (2 * (2^9 * 4409^0 * 458009^1) : ℤ) - (ArithmeticFunction.sigma 1 (2^9 * 4409^0 * 458009^1) : ℤ) := rfl
  rw [h_eq]
  rw [sigma_eq_39]
  decide

lemma f_eq_40 : ((2 * 469001216 : ℤ) - (ArithmeticFunction.sigma 1 469001216 : ℤ)) = 455962 := by
  have h_eq : (2 * 469001216 : ℤ) - (ArithmeticFunction.sigma 1 469001216 : ℤ) = (2 * (2^10 * 4409^0 * 458009^1) : ℤ) - (ArithmeticFunction.sigma 1 (2^10 * 4409^0 * 458009^1) : ℤ) := rfl
  rw [h_eq]
  rw [sigma_eq_40]
  decide

lemma f_eq_41 : ((2 * 938002432 : ℤ) - (ArithmeticFunction.sigma 1 938002432 : ℤ)) = 453914 := by
  have h_eq : (2 * 938002432 : ℤ) - (ArithmeticFunction.sigma 1 938002432 : ℤ) = (2 * (2^11 * 4409^0 * 458009^1) : ℤ) - (ArithmeticFunction.sigma 1 (2^11 * 4409^0 * 458009^1) : ℤ) := rfl
  rw [h_eq]
  rw [sigma_eq_41]
  decide

lemma f_eq_42 : ((2 * 1876004864 : ℤ) - (ArithmeticFunction.sigma 1 1876004864 : ℤ)) = 449818 := by
  have h_eq : (2 * 1876004864 : ℤ) - (ArithmeticFunction.sigma 1 1876004864 : ℤ) = (2 * (2^12 * 4409^0 * 458009^1) : ℤ) - (ArithmeticFunction.sigma 1 (2^12 * 4409^0 * 458009^1) : ℤ) := rfl
  rw [h_eq]
  rw [sigma_eq_42]
  decide

lemma f_eq_43 : ((2 * 2019361681 : ℤ) - (ArithmeticFunction.sigma 1 2019361681 : ℤ)) = 2018899262 := by
  have h_eq : (2 * 2019361681 : ℤ) - (ArithmeticFunction.sigma 1 2019361681 : ℤ) = (2 * (2^0 * 4409^1 * 458009^1) : ℤ) - (ArithmeticFunction.sigma 1 (2^0 * 4409^1 * 458009^1) : ℤ) := rfl
  rw [h_eq]
  rw [sigma_eq_43]
  decide

lemma f_eq_44 : ((2 * 3752009728 : ℤ) - (ArithmeticFunction.sigma 1 3752009728 : ℤ)) = 441626 := by
  have h_eq : (2 * 3752009728 : ℤ) - (ArithmeticFunction.sigma 1 3752009728 : ℤ) = (2 * (2^13 * 4409^0 * 458009^1) : ℤ) - (ArithmeticFunction.sigma 1 (2^13 * 4409^0 * 458009^1) : ℤ) := rfl
  rw [h_eq]
  rw [sigma_eq_44]
  decide

lemma f_eq_45 : ((2 * 4038723362 : ℤ) - (ArithmeticFunction.sigma 1 4038723362 : ℤ)) = 2017974424 := by
  have h_eq : (2 * 4038723362 : ℤ) - (ArithmeticFunction.sigma 1 4038723362 : ℤ) = (2 * (2^1 * 4409^1 * 458009^1) : ℤ) - (ArithmeticFunction.sigma 1 (2^1 * 4409^1 * 458009^1) : ℤ) := rfl
  rw [h_eq]
  rw [sigma_eq_45]
  decide

lemma f_eq_46 : ((2 * 7504019456 : ℤ) - (ArithmeticFunction.sigma 1 7504019456 : ℤ)) = 425242 := by
  have h_eq : (2 * 7504019456 : ℤ) - (ArithmeticFunction.sigma 1 7504019456 : ℤ) = (2 * (2^14 * 4409^0 * 458009^1) : ℤ) - (ArithmeticFunction.sigma 1 (2^14 * 4409^0 * 458009^1) : ℤ) := rfl
  rw [h_eq]
  rw [sigma_eq_46]
  decide

lemma f_eq_47 : ((2 * 8077446724 : ℤ) - (ArithmeticFunction.sigma 1 8077446724 : ℤ)) = 2016124748 := by
  have h_eq : (2 * 8077446724 : ℤ) - (ArithmeticFunction.sigma 1 8077446724 : ℤ) = (2 * (2^2 * 4409^1 * 458009^1) : ℤ) - (ArithmeticFunction.sigma 1 (2^2 * 4409^1 * 458009^1) : ℤ) := rfl
  rw [h_eq]
  rw [sigma_eq_47]
  decide

lemma f_eq_48 : ((2 * 16154893448 : ℤ) - (ArithmeticFunction.sigma 1 16154893448 : ℤ)) = 2012425396 := by
  have h_eq : (2 * 16154893448 : ℤ) - (ArithmeticFunction.sigma 1 16154893448 : ℤ) = (2 * (2^3 * 4409^1 * 458009^1) : ℤ) - (ArithmeticFunction.sigma 1 (2^3 * 4409^1 * 458009^1) : ℤ) := rfl
  rw [h_eq]
  rw [sigma_eq_48]
  decide

lemma f_eq_49 : ((2 * 32309786896 : ℤ) - (ArithmeticFunction.sigma 1 32309786896 : ℤ)) = 2005026692 := by
  have h_eq : (2 * 32309786896 : ℤ) - (ArithmeticFunction.sigma 1 32309786896 : ℤ) = (2 * (2^4 * 4409^1 * 458009^1) : ℤ) - (ArithmeticFunction.sigma 1 (2^4 * 4409^1 * 458009^1) : ℤ) := rfl
  rw [h_eq]
  rw [sigma_eq_49]
  decide

lemma f_eq_50 : ((2 * 64619573792 : ℤ) - (ArithmeticFunction.sigma 1 64619573792 : ℤ)) = 1990229284 := by
  have h_eq : (2 * 64619573792 : ℤ) - (ArithmeticFunction.sigma 1 64619573792 : ℤ) = (2 * (2^5 * 4409^1 * 458009^1) : ℤ) - (ArithmeticFunction.sigma 1 (2^5 * 4409^1 * 458009^1) : ℤ) := rfl
  rw [h_eq]
  rw [sigma_eq_50]
  decide

lemma f_eq_51 : ((2 * 129239147584 : ℤ) - (ArithmeticFunction.sigma 1 129239147584 : ℤ)) = 1960634468 := by
  have h_eq : (2 * 129239147584 : ℤ) - (ArithmeticFunction.sigma 1 129239147584 : ℤ) = (2 * (2^6 * 4409^1 * 458009^1) : ℤ) - (ArithmeticFunction.sigma 1 (2^6 * 4409^1 * 458009^1) : ℤ) := rfl
  rw [h_eq]
  rw [sigma_eq_51]
  decide

lemma f_eq_52 : ((2 * 258478295168 : ℤ) - (ArithmeticFunction.sigma 1 258478295168 : ℤ)) = 1901444836 := by
  have h_eq : (2 * 258478295168 : ℤ) - (ArithmeticFunction.sigma 1 258478295168 : ℤ) = (2 * (2^7 * 4409^1 * 458009^1) : ℤ) - (ArithmeticFunction.sigma 1 (2^7 * 4409^1 * 458009^1) : ℤ) := rfl
  rw [h_eq]
  rw [sigma_eq_52]
  decide

lemma f_eq_53 : ((2 * 516956590336 : ℤ) - (ArithmeticFunction.sigma 1 516956590336 : ℤ)) = 1783065572 := by
  have h_eq : (2 * 516956590336 : ℤ) - (ArithmeticFunction.sigma 1 516956590336 : ℤ) = (2 * (2^8 * 4409^1 * 458009^1) : ℤ) - (ArithmeticFunction.sigma 1 (2^8 * 4409^1 * 458009^1) : ℤ) := rfl
  rw [h_eq]
  rw [sigma_eq_53]
  decide

lemma f_eq_54 : ((2 * 1033913180672 : ℤ) - (ArithmeticFunction.sigma 1 1033913180672 : ℤ)) = 1546307044 := by
  have h_eq : (2 * 1033913180672 : ℤ) - (ArithmeticFunction.sigma 1 1033913180672 : ℤ) = (2 * (2^9 * 4409^1 * 458009^1) : ℤ) - (ArithmeticFunction.sigma 1 (2^9 * 4409^1 * 458009^1) : ℤ) := rfl
  rw [h_eq]
  rw [sigma_eq_54]
  decide

lemma f_eq_55 : ((2 * 2067826361344 : ℤ) - (ArithmeticFunction.sigma 1 2067826361344 : ℤ)) = 1072789988 := by
  have h_eq : (2 * 2067826361344 : ℤ) - (ArithmeticFunction.sigma 1 2067826361344 : ℤ) = (2 * (2^10 * 4409^1 * 458009^1) : ℤ) - (ArithmeticFunction.sigma 1 (2^10 * 4409^1 * 458009^1) : ℤ) := rfl
  rw [h_eq]
  rw [sigma_eq_55]
  decide

lemma f_eq_56 : ((2 * 4135652722688 : ℤ) - (ArithmeticFunction.sigma 1 4135652722688 : ℤ)) = 125755876 := by
  have h_eq : (2 * 4135652722688 : ℤ) - (ArithmeticFunction.sigma 1 4135652722688 : ℤ) = (2 * (2^11 * 4409^1 * 458009^1) : ℤ) - (ArithmeticFunction.sigma 1 (2^11 * 4409^1 * 458009^1) : ℤ) := rfl
  rw [h_eq]
  rw [sigma_eq_56]
  decide

lemma f_eq_57 : ((2 * 8271305445376 : ℤ) - (ArithmeticFunction.sigma 1 8271305445376 : ℤ)) = -1768312348 := by
  have h_eq : (2 * 8271305445376 : ℤ) - (ArithmeticFunction.sigma 1 8271305445376 : ℤ) = (2 * (2^12 * 4409^1 * 458009^1) : ℤ) - (ArithmeticFunction.sigma 1 (2^12 * 4409^1 * 458009^1) : ℤ) := rfl
  rw [h_eq]
  rw [sigma_eq_57]
  decide

lemma f_eq_58 : ((2 * 16542610890752 : ℤ) - (ArithmeticFunction.sigma 1 16542610890752 : ℤ)) = -5556448796 := by
  have h_eq : (2 * 16542610890752 : ℤ) - (ArithmeticFunction.sigma 1 16542610890752 : ℤ) = (2 * (2^13 * 4409^1 * 458009^1) : ℤ) - (ArithmeticFunction.sigma 1 (2^13 * 4409^1 * 458009^1) : ℤ) := rfl
  rw [h_eq]
  rw [sigma_eq_58]
  decide

lemma f_eq_59 : ((2 * 33085221781504 : ℤ) - (ArithmeticFunction.sigma 1 33085221781504 : ℤ)) = -13132721692 := by
  have h_eq : (2 * 33085221781504 : ℤ) - (ArithmeticFunction.sigma 1 33085221781504 : ℤ) = (2 * (2^14 * 4409^1 * 458009^1) : ℤ) - (ArithmeticFunction.sigma 1 (2^14 * 4409^1 * 458009^1) : ℤ) := rfl
  rw [h_eq]
  rw [sigma_eq_59]
  decide

def S : Finset ℕ :=
  {1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 4409, 8192, 8818, 16384, 17636, 35272, 70544, 141088, 282176, 458009, 564352, 916018, 1128704, 1832036, 2257408, 3664072, 4514816, 7328144, 9029632, 14656288, 18059264, 29312576, 36118528, 58625152, 72237056, 117250304, 234500608, 469001216, 938002432, 1876004864, 2019361681, 3752009728, 4038723362, 7504019456, 8077446724, 16154893448, 32309786896, 64619573792, 129239147584, 258478295168, 516956590336, 1033913180672, 2067826361344, 4135652722688, 8271305445376, 16542610890752, 33085221781504}

lemma card_S : #S = 60 := by decide

lemma h_BC : ({1, 4409} * {1, 458009} : Finset ℕ) = {1, 4409, 458009, 2019361681} := by decide

lemma h_S : ( {1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384} * {1, 4409, 458009, 2019361681} : Finset ℕ ) = S := by decide


lemma divisors_33085221781504_eq : divisors 33085221781504 = S := by
  have h1 : 33085221781504 = 16384 * 4409 * 458009 := by decide
  rw [h1]
  rw [Nat.divisors_mul]
  rw [Nat.divisors_mul]
  have h_16384 : divisors 16384 = {1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384} := by decide
  have h_4409_prime : Nat.Prime 4409 := by norm_num
  have h_458009_prime : Nat.Prime 458009 := by norm_num
  have h_4409 : divisors 4409 = {1, 4409} := h_4409_prime.divisors
  have h_458009 : divisors 458009 = {1, 458009} := h_458009_prime.divisors
  rw [h_16384, h_4409, h_458009]
  rw [mul_assoc]
  rw [h_BC]
  exact h_S

lemma sum_S_eq_1 : S.sum (fun d => (2 * d : ℤ) - (ArithmeticFunction.sigma 1 d : ℤ)) = 1 := by
  unfold S
  rw [sum_insert (by decide)]
  rw [sum_insert (by decide)]
  rw [sum_insert (by decide)]
  rw [sum_insert (by decide)]
  rw [sum_insert (by decide)]
  rw [sum_insert (by decide)]
  rw [sum_insert (by decide)]
  rw [sum_insert (by decide)]
  rw [sum_insert (by decide)]
  rw [sum_insert (by decide)]
  rw [sum_insert (by decide)]
  rw [sum_insert (by decide)]
  rw [sum_insert (by decide)]
  rw [sum_insert (by decide)]
  rw [sum_insert (by decide)]
  rw [sum_insert (by decide)]
  rw [sum_insert (by decide)]
  rw [sum_insert (by decide)]
  rw [sum_insert (by decide)]
  rw [sum_insert (by decide)]
  rw [sum_insert (by decide)]
  rw [sum_insert (by decide)]
  rw [sum_insert (by decide)]
  rw [sum_insert (by decide)]
  rw [sum_insert (by decide)]
  rw [sum_insert (by decide)]
  rw [sum_insert (by decide)]
  rw [sum_insert (by decide)]
  rw [sum_insert (by decide)]
  rw [sum_insert (by decide)]
  rw [sum_insert (by decide)]
  rw [sum_insert (by decide)]
  rw [sum_insert (by decide)]
  rw [sum_insert (by decide)]
  rw [sum_insert (by decide)]
  rw [sum_insert (by decide)]
  rw [sum_insert (by decide)]
  rw [sum_insert (by decide)]
  rw [sum_insert (by decide)]
  rw [sum_insert (by decide)]
  rw [sum_insert (by decide)]
  rw [sum_insert (by decide)]
  rw [sum_insert (by decide)]
  rw [sum_insert (by decide)]
  rw [sum_insert (by decide)]
  rw [sum_insert (by decide)]
  rw [sum_insert (by decide)]
  rw [sum_insert (by decide)]
  rw [sum_insert (by decide)]
  rw [sum_insert (by decide)]
  rw [sum_insert (by decide)]
  rw [sum_insert (by decide)]
  rw [sum_insert (by decide)]
  rw [sum_insert (by decide)]
  rw [sum_insert (by decide)]
  rw [sum_insert (by decide)]
  rw [sum_insert (by decide)]
  rw [sum_insert (by decide)]
  rw [sum_insert (by decide)]
  rw [sum_singleton]
  simp only [Nat.cast_one, Nat.cast_ofNat]
  rw [f_eq_0, f_eq_1, f_eq_2, f_eq_3, f_eq_4, f_eq_5, f_eq_6, f_eq_7, f_eq_8, f_eq_9, f_eq_10, f_eq_11, f_eq_12, f_eq_13, f_eq_14, f_eq_15, f_eq_16, f_eq_17, f_eq_18, f_eq_19, f_eq_20, f_eq_21, f_eq_22, f_eq_23, f_eq_24, f_eq_25, f_eq_26, f_eq_27, f_eq_28, f_eq_29, f_eq_30, f_eq_31, f_eq_32, f_eq_33, f_eq_34, f_eq_35, f_eq_36, f_eq_37, f_eq_38, f_eq_39, f_eq_40, f_eq_41, f_eq_42, f_eq_43, f_eq_44, f_eq_45, f_eq_46, f_eq_47, f_eq_48, f_eq_49, f_eq_50, f_eq_51, f_eq_52, f_eq_53, f_eq_54, f_eq_55, f_eq_56, f_eq_57, f_eq_58, f_eq_59]
  decide


theorem a_33085221781504 : a 33085221781504 = 1 := by
  unfold a
  rw [divisors_33085221781504_eq]
  exact sum_S_eq_1


theorem oeis_296075_conjecture_0.disproof : ¬ (∀ n : ℕ, a n = 1 ↔ n = 1 ∨ n = 12) := by
  intro h
  have h1 : a 33085221781504 = 1 ↔ 33085221781504 = 1 ∨ 33085221781504 = 12 := h 33085221781504
  have h2 : a 33085221781504 = 1 := a_33085221781504
  have h3 : 33085221781504 = 1 ∨ 33085221781504 = 12 := h1.mp h2
  rcases h3 with h3_1 | h3_12
  · revert h3_1; decide
  · revert h3_12; decide

