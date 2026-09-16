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
  decide
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

lemma sigma_3_6 : ArithmeticFunction.sigma 1 (3^6) = 1093 := by
  have hp : Nat.Prime 3 := by norm_num
  rw [ArithmeticFunction.sigma_one_apply_prime_pow hp]
  decide
lemma A003958_sig_3_6 : A003958 1093 = 1092 := by
  have hq : Nat.Prime 1093 := by norm_num
  have step1 := A003958_prime hq
  rw [step1]

lemma sigma_5_1 : ArithmeticFunction.sigma 1 (5^1) = 6 := by
  have hp : Nat.Prime 5 := by norm_num
  rw [ArithmeticFunction.sigma_one_apply_prime_pow hp]
  decide
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

lemma sigma_7_6 : ArithmeticFunction.sigma 1 (7^6) = 137257 := by
  have hp : Nat.Prime 7 := by norm_num
  rw [ArithmeticFunction.sigma_one_apply_prime_pow hp]
  decide
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

lemma sigma_13_4 : ArithmeticFunction.sigma 1 (13^4) = 30941 := by
  have hp : Nat.Prime 13 := by norm_num
  rw [ArithmeticFunction.sigma_one_apply_prime_pow hp]
  decide
lemma A003958_sig_13_4 : A003958 30941 = 30940 := by
  have hq : Nat.Prime 30941 := by norm_num
  have step1 := A003958_prime hq
  rw [step1]

lemma sigma_17_2 : ArithmeticFunction.sigma 1 (17^2) = 307 := by
  have hp : Nat.Prime 17 := by norm_num
  rw [ArithmeticFunction.sigma_one_apply_prime_pow hp]
  decide
lemma A003958_sig_17_2 : A003958 307 = 306 := by
  have hq : Nat.Prime 307 := by norm_num
  have step1 := A003958_prime hq
  rw [step1]

def n1 : ℕ := (2^13) * (3^6) * (5^1) * (7^6) * (13^4) * (17^2)
lemma sigma_n1 : ArithmeticFunction.sigma 1 n1 = ArithmeticFunction.sigma 1 (2^13) * ArithmeticFunction.sigma 1 (3^6) * ArithmeticFunction.sigma 1 (5^1) * ArithmeticFunction.sigma 1 (7^6) * ArithmeticFunction.sigma 1 (13^4) * ArithmeticFunction.sigma 1 (17^2) := by
  unfold n1
  have h_gcd_5 : ((2^13) * (3^6) * (5^1) * (7^6) * (13^4)).gcd (17^2) = 1 := by norm_num
  rw [sigma_mul_coprime h_gcd_5]
  have h_gcd_4 : ((2^13) * (3^6) * (5^1) * (7^6)).gcd (13^4) = 1 := by norm_num
  rw [sigma_mul_coprime h_gcd_4]
  have h_gcd_3 : ((2^13) * (3^6) * (5^1)).gcd (7^6) = 1 := by norm_num
  rw [sigma_mul_coprime h_gcd_3]
  have h_gcd_2 : ((2^13) * (3^6)).gcd (5^1) = 1 := by norm_num
  rw [sigma_mul_coprime h_gcd_2]
  have h_gcd_1 : ((2^13)).gcd (3^6) = 1 := by norm_num
  rw [sigma_mul_coprime h_gcd_1]
  -- rw closes the goal

lemma A003958_sigma_n1 : A003958 (ArithmeticFunction.sigma 1 n1) = n1 := by
  rw [sigma_n1]
  rw [sigma_2_13]
  rw [sigma_3_6]
  rw [sigma_5_1]
  rw [sigma_7_6]
  rw [sigma_13_4]
  rw [sigma_17_2]
  rw [A003958_mul (by norm_num) (by norm_num)]
  rw [A003958_mul (by norm_num) (by norm_num)]
  rw [A003958_mul (by norm_num) (by norm_num)]
  rw [A003958_mul (by norm_num) (by norm_num)]
  rw [A003958_mul (by norm_num) (by norm_num)]
  rw [A003958_sig_2_13]
  rw [A003958_sig_3_6]
  rw [A003958_sig_5_1]
  rw [A003958_sig_7_6]
  rw [A003958_sig_13_4]
  rw [A003958_sig_17_2]
  unfold n1
  norm_num

theorem oeis_351442_conjecture_0.disproof : ¬ (∀ n : ℕ, n > 0 → (a_test n = n ↔ n ∈ ({1, 2, 8, 128, 288, 720, 32768, 29719872, 2147483648} : Finset ℕ))) := by
  intro h
  have h_pos : 0 < n1 := by
    unfold n1
    norm_num
  have h1 := h n1 h_pos
  have h2 : a_test n1 = n1 := A003958_sigma_n1
  have h3 : n1 ∈ ({1, 2, 8, 128, 288, 720, 32768, 29719872, 2147483648} : Finset ℕ) := h1.mp h2
  revert h3
  unfold n1
  decide

