import FormalConjectures.Util.ProblemImports
open Nat Finset
def A003958 (n : ℕ) : ℕ := n.factorization.prod fun p e => (p - 1) ^ e
def a_test (n : ℕ) : ℕ := A003958 (ArithmeticFunction.sigma 1 n)

set_option maxRecDepth 10000000

lemma A003958_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) : A003958 (a * b) = A003958 a * A003958 b := by
  dsimp [A003958]
  rw [Nat.factorization_mul ha hb]
  apply Finsupp.prod_add_index'
  · intro x; exact pow_zero _
  · intro x y z; exact pow_add _ _ _

lemma A003958_prime {p : ℕ} (hp : Nat.Prime p) : A003958 p = p - 1 := by
  dsimp [A003958]
  rw [Nat.Prime.factorization hp]
  have H : (fun₀ | p => 1).prod (fun p e => (p - 1) ^ e) = (p - 1) ^ 1 := by
    apply Finsupp.prod_single_index
    exact pow_zero (p - 1)
  rw [H, pow_one]

lemma A003958_prime_pow {p e : ℕ} (hp : Nat.Prime p) : A003958 (p ^ e) = (p - 1) ^ e := by
  dsimp [A003958]
  rw [Nat.factorization_pow, Nat.Prime.factorization hp]
  rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  have H : (fun₀ | p => e).prod (fun p e => (p - 1) ^ e) = (p - 1) ^ e := by
    apply Finsupp.prod_single_index
    exact pow_zero (p - 1)
  exact H

lemma sigma_mul_coprime {a b : ℕ} (h : a.gcd b = 1) :
  ArithmeticFunction.sigma 1 (a * b) = ArithmeticFunction.sigma 1 a * ArithmeticFunction.sigma 1 b :=
  ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime h

lemma sigma_2_13 : ArithmeticFunction.sigma 1 (2^13) = 16383 := by
  have hp : Nat.Prime 2 := by norm_num
  rw [ArithmeticFunction.sigma_one_apply_prime_pow hp]
  try norm_num
lemma A003958_sig_2_13 : A003958 16383 = 10584 := by
  have H : (16383 : ℕ) = 3 * 5461 := by norm_num
  rw [H]
  rw [A003958_mul (by norm_num) (by norm_num)]
  have hq : Nat.Prime 3 := by norm_num
  have step1 := A003958_prime hq
  rw [step1]
  have H : (5461 : ℕ) = 43 * 127 := by norm_num
  rw [H]
  rw [A003958_mul (by norm_num) (by norm_num)]
  have hq : Nat.Prime 43 := by norm_num
  have step1 := A003958_prime hq
  rw [step1]
  have hq : Nat.Prime 127 := by norm_num
  have step1 := A003958_prime hq
  rw [step1]
  try norm_num

lemma sigma_3_6 : ArithmeticFunction.sigma 1 (3^6) = 1093 := by
  have hp : Nat.Prime 3 := by norm_num
  rw [ArithmeticFunction.sigma_one_apply_prime_pow hp]
  try norm_num
lemma A003958_sig_3_6 : A003958 1093 = 1092 := by
  have hq : Nat.Prime 1093 := by norm_num
  have step1 := A003958_prime hq
  rw [step1]
  try norm_num

lemma sigma_5_1 : ArithmeticFunction.sigma 1 (5^1) = 6 := by
  have hp : Nat.Prime 5 := by norm_num
  rw [ArithmeticFunction.sigma_one_apply_prime_pow hp]
  try norm_num
lemma A003958_sig_5_1 : A003958 6 = 2 := by
  have H : (6 : ℕ) = 2 * 3 := by norm_num
  rw [H]
  rw [A003958_mul (by norm_num) (by norm_num)]
  have hq : Nat.Prime 2 := by norm_num
  have step1 := A003958_prime hq
  rw [step1]
  have hq : Nat.Prime 3 := by norm_num
  have step1 := A003958_prime hq
  rw [step1]
  try norm_num

lemma sigma_7_6 : ArithmeticFunction.sigma 1 (7^6) = 137257 := by
  have hp : Nat.Prime 7 := by norm_num
  rw [ArithmeticFunction.sigma_one_apply_prime_pow hp]
  try norm_num
lemma A003958_sig_7_6 : A003958 137257 = 132496 := by
  have H : (137257 : ℕ) = 29 * 4733 := by norm_num
  rw [H]
  rw [A003958_mul (by norm_num) (by norm_num)]
  have hq : Nat.Prime 29 := by norm_num
  have step1 := A003958_prime hq
  rw [step1]
  have hq : Nat.Prime 4733 := by norm_num
  have step1 := A003958_prime hq
  rw [step1]
  try norm_num

lemma sigma_13_4 : ArithmeticFunction.sigma 1 (13^4) = 30941 := by
  have hp : Nat.Prime 13 := by norm_num
  rw [ArithmeticFunction.sigma_one_apply_prime_pow hp]
  try norm_num
lemma A003958_sig_13_4 : A003958 30941 = 30940 := by
  have hq : Nat.Prime 30941 := by norm_num
  have step1 := A003958_prime hq
  rw [step1]
  try norm_num

lemma sigma_17_2 : ArithmeticFunction.sigma 1 (17^2) = 307 := by
  have hp : Nat.Prime 17 := by norm_num
  rw [ArithmeticFunction.sigma_one_apply_prime_pow hp]
  try norm_num
lemma A003958_sig_17_2 : A003958 307 = 306 := by
  have hq : Nat.Prime 307 := by norm_num
  have step1 := A003958_prime hq
  rw [step1]
  try norm_num
